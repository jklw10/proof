import os
import csv
import numpy as np
from scipy.optimize import minimize
import matplotlib.pyplot as plt

# =========================================================================
# STEP 1: Parse the Real Calibration CSV
# =========================================================================
def load_calibration_data(filepath="entropy/data.csv"):
    """
    Reads calibration data directly from the CSV.
    Expected Columns:
      Column 0: Qubit ID (int)
      Column 1: T1 (relaxation time in us)
      Column 2: T2 (coherence time in us)
    """
    if not os.path.exists(filepath):
        if os.path.exists("data.csv"):
            filepath = "data.csv"
        else:
            raise FileNotFoundError(f"Could not find the calibration file at '{filepath}' or 'data.csv'")

    qubits_data = {}
    with open(filepath, 'r') as f:
        reader = csv.reader(f)
        # Skip header
        header = next(reader)
        
        for row in reader:
            if not row or len(row) < 3:
                continue
            try:
                qubit_id = int(row[0].replace('"', '').strip())
                t1 = float(row[1].replace('"', '').strip())
                t2 = float(row[2].replace('"', '').strip())
                
                # Calculate physical rates
                gamma1 = 1.0 / t1 if t1 > 0 else 0.0
                gamma2 = 1.0 / t2 if t2 > 0 else 0.0
                gamma_phi = gamma2 - (0.5 * gamma1)
                
                qubits_data[qubit_id] = {
                    't1': t1, 't2': t2,
                    'gamma1': gamma1, 'gamma2': gamma2,
                    'gamma_phi': gamma_phi
                }
            except Exception:
                # Skip malformed lines
                continue
                
    return qubits_data

# =========================================================================
# STEP 2: Construct the 127-Qubit Heavy-Hex Lattice Coordinates & Edges
# =========================================================================
def construct_heavy_hex_geometry():
    """
    Generates nominal 2D positions for the 127 qubits on a heavy-hex layout.
    Edges are established purely by checking Euclidean distance spacing.
    """
    pos_nominal = {}
    node_id = 0
    
    # Fill standard coordinates on a grid mapped to heavy-hex configurations
    for r in range(15):
        for c in range(15):
            is_node = False
            if r % 4 == 0:
                is_node = True
            elif r % 4 == 2 and c % 2 == 0:
                is_node = True
            elif (r % 4 == 1 or r % 4 == 3) and (c % 4 == 0 or c % 4 == 2):
                is_node = True
                
            if is_node and node_id < 127:
                pos_nominal[node_id] = np.array([float(c) * 0.1, float(r) * 0.1])
                node_id += 1

    # Connect nearest-neighbors (nominally spaced by ~0.1 mm)
    edges = []
    for i in range(127):
        for j in range(i + 1, 127):
            dist = np.linalg.norm(pos_nominal[i] - pos_nominal[j])
            if dist < 0.14:  # Spacing threshold for adjacent nodes
                edges.append((i, j))
                
    return pos_nominal, edges

# =========================================================================
# STEP 3: Joint Coordinate Optimization
# =========================================================================
def optimize_layout(qubits_data, pos_nominal, edges):
    num_nodes = 127
    
    # Extract dephasing rates from the parsed CSV dictionary
    observed_dephasing = np.zeros(num_nodes)
    for i in range(num_nodes):
        if i in qubits_data:
            val = qubits_data[i]['gamma_phi']
            # Safeguard against unphysical values (temporal drift)
            observed_dephasing[i] = max(val, 1e-4)
        else:
            observed_dephasing[i] = 1e-3  # default fallback
            
    # Model parameters
    C0 = np.mean(observed_dephasing)  # Average coupling scale
    Gamma0 = np.min(observed_dephasing) * 0.5  # Base floor dephasing
    d0 = 0.1  # Nominal spacing (0.1 mm)

    # Convert nominal coordinates to flat array for optimizer input
    initial_flat = np.array([pos_nominal[i] for i in range(num_nodes)]).flatten()

    # Pre-build lookup sets/tables for the loss function
    edge_set = set(edges)

    def loss_function(flat_coords):
        coords = flat_coords.reshape((num_nodes, 2))
        
        # 1. Structural Spring Loss (keeps layout close to standard geometry)
        spring_loss = 0.0
        for u, v in edges:
            d_uv = np.linalg.norm(coords[u] - coords[v])
            spring_loss += (d_uv - d0) ** 2
            
        # 2. Preventing Overlap (forces distance between un-connected nodes)
        repulsion_loss = 0.0
        for u in range(num_nodes):
            for v in range(u + 1, num_nodes):
                if (u, v) not in edge_set and (v, u) not in edge_set:
                    d_uv = np.linalg.norm(coords[u] - coords[v])
                    if d_uv < d0:
                        repulsion_loss += (d_uv - d0) ** 2
                        
        # 3. Fit to the C0 / d Cross-Talk Model
        model_loss = 0.0
        for u in range(num_nodes):
            pred_coupling = 0.0
            for v in range(num_nodes):
                if u != v:
                    d_uv = np.linalg.norm(coords[u] - coords[v])
                    # Sum up coupling from immediate neighborhood
                    if d_uv < 0.15 and d_uv > 1e-4:
                        pred_coupling += C0 / d_uv
            pred_total = Gamma0 + pred_coupling
            model_loss += (pred_total - observed_dephasing[u]) ** 2
            
        return 150.0 * spring_loss + 10.0 * repulsion_loss + 1.0 * model_loss

    print("Running 2D coordinates optimization to fit your model...")
    res = minimize(loss_function, initial_flat, method='L-BFGS-B')
    opt_coords = res.x.reshape((num_nodes, 2))
    print("Optimization complete.")
    
    return opt_coords, observed_dephasing

# =========================================================================
# STEP 4: Execution & Image Generation
# =========================================================================
def main():
    try:
        print("Loading calibration data...")
        qubits_data = load_calibration_data()
        print(f"Loaded data for {len(qubits_data)} qubits from CSV.")
    except Exception as e:
        print(f"[ERROR] Failed to load CSV data: {e}")
        return

    # Generate layout structure
    pos_nominal, edges = construct_heavy_hex_geometry()
    
    # Run coordinate adaptation
    opt_coords, observed_dephasing = optimize_layout(qubits_data, pos_nominal, edges)

    # Plot comparison maps
    fig, axes = plt.subplots(1, 2, figsize=(16, 7))

    # Left Plot: Ideal Grid Reference
    axes[0].scatter([pos_nominal[i][0] for i in range(127)], 
                    [pos_nominal[i][1] for i in range(127)], 
                    c='darkgray', s=40, zorder=3)
    for u, v in edges:
        axes[0].plot([pos_nominal[u][0], pos_nominal[v][0]], 
                     [pos_nominal[u][1], pos_nominal[v][1]], 
                     color='royalblue', alpha=0.4, zorder=2)
    axes[0].set_title("Standard Heavy-Hex 2D Layout Geometry", fontsize=13)
    axes[0].set_xlabel("X coordinate (mm)")
    axes[0].set_ylabel("Y coordinate (mm)")
    axes[0].set_aspect('equal')
    axes[0].grid(True, linestyle='--', alpha=0.5)

    # Right Plot: Fitted Spatial Map
    sc = axes[1].scatter(opt_coords[:, 0], opt_coords[:, 1], 
                        c=observed_dephasing, cmap='plasma', 
                        edgecolors='k', s=60, zorder=3)
    for u, v in edges:
        axes[1].plot([opt_coords[u, 0], opt_coords[v, 0]], 
                     [opt_coords[u, 1], opt_coords[v, 1]], 
                     color='tomato', alpha=0.5, zorder=2)
    axes[1].set_title("Model-Estimated Layout (Fitted to observed $\\Gamma_\\phi$)", fontsize=13)
    axes[1].set_xlabel("Optimized X (mm)")
    axes[1].set_ylabel("Optimized Y (mm)")
    axes[1].set_aspect('equal')
    axes[1].grid(True, linestyle='--', alpha=0.5)
    
    cbar = fig.colorbar(sc, ax=axes[1])
    cbar.set_label("Observed Dephasing Rate $\\Gamma_\\phi$ ($\\mu s^{-1}$)", fontsize=11)

    plt.tight_layout()
    output_filename = "estimated_qubit_layout.png"
    plt.savefig(output_filename, dpi=300)
    print(f"Saved estimated layout visualization to: {output_filename}")
    plt.show()

if __name__ == "__main__":
    main()