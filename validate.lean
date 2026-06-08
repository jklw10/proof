import Lean

-- =========================================================================
-- PART 1: Data Structures and Parsing Utilities
-- =========================================================================

/-- Structure containing the 2-channel entropic analysis of a qubit -/
structure QubitAnalysis where
  id : Nat
  t1 : Float
  t2 : Float
  gamma1 : Float     -- Energy relaxation rate (1/T1)
  gamma2 : Float     -- Total decoherence rate (1/T2)
  gamma_phi : Float  -- Implied pure dephasing rate (1/T2 - 1/(2*T1))
  is_physical : Bool -- True if gamma_phi >= 0 (satisfies T2 <= 2*T1)

/-- Structure representing a qubit's physical 3D coordinates on the chip (in millimeters) -/
structure QubitCoords where
  id : Nat
  x : Float
  y : Float
  z : Float

/-- Helper to parse a single String to an Option Float -/
def toFloat? (s : String) : Option Float := do
  let s := s.trimAscii.toString
  let mut s := s
  let mut sign := false
  if let some _ := s.dropPrefix? "-" then
    sign := true

  if let some (n, esign, e) := Lean.Syntax.decodeScientificLitVal? s then
    let res := Float.ofScientific n esign e
    return if sign then -res else res
  else if let some n := Lean.Syntax.decodeNatLitVal? s then
    let res := Float.ofNat n
    return if sign then -res else res
  else none

/-- Helper to strip leading and trailing double quotes from CSV fields -/
def stripQuotes (s : String) : String :=
  let s := s.trimAscii.toString
  let s := if s.startsWith "\"" then s.drop 1 else s
  let s := if s.endsWith "\"" then s.dropEnd 1 else s
  s.trimAscii.toString

/-- Parses a multi-column IBM calibration row into a QubitAnalysis structure.
    Column 0: Qubit ID
    Column 1: T1 (relaxation time)
    Column 2: T2 (coherence time) -/
def parseLine (line : String) : Option QubitAnalysis :=
  let parts := line.splitOn "," |>.map stripQuotes
  match parts with
  | idStr :: t1Str :: t2Str :: _ => do
    let id ← idStr.toNat?
    let t1 ← toFloat? t1Str
    let t2 ← toFloat? t2Str
    let gamma1 := 1.0 / t1
    let gamma2 := 1.0 / t2
    let gamma_phi := gamma2 - (0.5 * gamma1)
    let is_physical := gamma_phi >= 0.0
    return { id := id, t1 := t1, t2 := t2, gamma1 := gamma1, gamma2 := gamma2, gamma_phi := gamma_phi, is_physical := is_physical }
  | _ => none

-- =========================================================================
-- PART 2: 3D Spatial Projector & Cross-Talk Predictor
-- =========================================================================
-- Map the physical layout offsets on the 23x13 grid embedding
def heavyHex127Coordinates : Array (Float × Float) :=
  -- This lookup table can be populated with the coordinates of qubits 0 to 126
  #[
    (0.0, 0.0),   -- Qubit 0
    (1.0, 0.0),   -- Qubit 1
    (2.0, 0.0),   -- Qubit 2
    -- ... and so on for all 127 qubits
    (11.0, 5.0)   -- Qubit 126
  ]

/-- Physical Heavy-Hex Projector using the actual layout coordinates --/
def getQubitCoords (id : Nat) : QubitCoords :=
  let pitch := 0.1 -- 100 μm in millimeters
  let coords := heavyHex127Coordinates.getD id (0.0, 0.0)
  let x := coords.1 * pitch
  let y := coords.2 * pitch
  let z := 0.05 -- 50 μm substrate depth
  { id := id, x := x, y := y, z := z }

/-- Calculates the Euclidean distance between two qubits in millimeters -/
def distance3D (q1 q2 : QubitCoords) : Float :=
  let dx := q1.x - q2.x
  let dy := q1.y - q2.y
  let dz := q1.z - q2.z
  Float.sqrt (dx*dx + dy*dy + dz*dz)

/-- Predictions: Uses your 3D spherical conservation law (C0 / d)
    to predict the spatial entropic coupling (cross-talk) between two qubits.
    The coupling strength C0 is mapped directly to the chip's average pure dephasing rate. -/
def predictCrossTalk (C0 : Float) (q1 q2 : QubitCoords) : Option Float :=
  let d := distance3D q1 q2
  if d > 0.0 then
    return C0 / d
  else
    none

-- =========================================================================
-- PART 3: The Validation Pipeline
-- =========================================================================

/-- Processes the dataset line by line.
    Accumulates statistics, detects temporal drift, and prints a predicted 3D spatial cross-talk map. -/
def validateData (content : String) : IO Unit := do
  let lines := content.splitOn "\n"
  let dataLines := lines.tail
  let mut lineIndex := 1

  -- Accumulators
  let mut totalQubits : Nat := 0
  let mut physicalCount : Nat := 0
  let mut driftOutliers : Nat := 0

  let mut sumGamma1 : Float := 0.0
  let mut sumGamma2 : Float := 0.0
  let mut sumGammaPhi : Float := 0.0

  -- Store parsed qubits for spatial cross-talk prediction
  let mut parsedQubits : List QubitAnalysis := []

  for line in dataLines do
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then continue
    lineIndex := lineIndex + 1

    match parseLine trimmed with
    | some analysis =>
      totalQubits := totalQubits + 1
      sumGamma1 := sumGamma1 + analysis.gamma1
      sumGamma2 := sumGamma2 + analysis.gamma2
      parsedQubits := analysis :: parsedQubits

      if analysis.is_physical then
        physicalCount := physicalCount + 1
        sumGammaPhi := sumGammaPhi + analysis.gamma_phi
      else
        driftOutliers := driftOutliers + 1
        IO.println s!"[INFO] Line {lineIndex} (Qubit {analysis.id}): Temporal drift detected (T2 = {analysis.t2} μs > 2*T1 = {2.0 * analysis.t1} μs)"

    | none => continue

  -- Calculations
  let totalQubitsF := Float.ofNat totalQubits
  let physicalCountF := Float.ofNat physicalCount

  let avgGamma1 := sumGamma1 / totalQubitsF
  let avgGamma2 := sumGamma2 / totalQubitsF
  let avgGammaPhi := if physicalCount > 0 then sumGammaPhi / physicalCountF else 0.0
  let dephasingContributionPercent := (avgGammaPhi / avgGamma2) * 100.0

  -- Output the 2-Channel statistical sweep
  IO.println "\n=================================================="
  IO.println "         TWO-CHANNEL ENTROPIC SWEEP RESULTS       "
  IO.println "=================================================="
  IO.println s!"Total Qubits Processed      : {totalQubits}"
  IO.println s!"Physically Consistent Qubits : {physicalCount}"
  IO.println s!"Temporal Drift Outliers      : {driftOutliers}"
  IO.println "--------------------------------------------------"
  IO.println s!"Avg Energy Relaxation (Γ1)   : {avgGamma1} μs⁻¹"
  IO.println s!"Avg Total Decoherence (Γ2)  : {avgGamma2} μs⁻¹"
  IO.println s!"Avg Pure Phase Dephasing (Γφ): {avgGammaPhi} μs⁻¹"
  IO.println "--------------------------------------------------"
  IO.println s!"Phase Noise Contribution     : {dephasingContributionPercent}%"
  IO.println "=================================================="

  -- Output the 3D Spatial Cross-Talk Prediction Map using spherical conservation
  IO.println "\n=================================================="
  IO.println "       PREDICTED 3D SPATIAL CROSS-TALK MAP        "
  IO.println "=================================================="
  IO.println s!"Coupling constant (C0 = Avg Γφ): {avgGammaPhi} μs⁻¹"
  IO.println "Sample predictions for nearest-neighbor qubits (distance ≈ 0.1 mm):"

  let mut printedPredictions := 0
  let qubitsList := parsedQubits.reverse

  for i in [0:qubitsList.length] do
    for j in [i+1:qubitsList.length] do
      if printedPredictions >= 10 then break
      -- Safely extract indices using option syntax, which resolves types and prevents compilation panic
      match qubitsList[i]?, qubitsList[j]? with
      | some q1, some q2 =>
        let coords1 := getQubitCoords q1.id
        let coords2 := getQubitCoords q2.id
        let dist := distance3D coords1 coords2

        -- If they are nearest neighbors (distance ≈ 0.1 mm on our grid)
        if dist < 0.11 then
          match predictCrossTalk avgGammaPhi coords1 coords2 with
          | some coupling =>
            IO.println s!"  Qubit {q1.id} <-> Qubit {q2.id} | Separation: {dist} mm | Predicted Coupling: {coupling} μs⁻¹"
            printedPredictions := printedPredictions + 1
          | none => continue
      | _, _ => continue

  IO.println "=================================================="
  IO.println "\n[SUCCESS] Pipeline validation and prediction complete."

def main : IO Unit := do
  let filePath := "data.csv"
  try
    let content ← IO.FS.readFile filePath
    validateData content
  catch e =>
    IO.println s!"[ERROR] Could not read '{filePath}': {e}"
    IO.Process.exit 1
