import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section vfw

variable {d : ℕ}

def vfD (V : (Fin d → ℝ) → (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  fun x => fderiv ℝ u x (V x)

def vfW : List ((Fin d → ℝ) → (Fin d → ℝ)) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | V :: Vs, u => vfD V (vfW Vs u)

abbrev WOp (d : ℕ) := List (ℂ × List ((Fin d → ℝ) → (Fin d → ℝ)))

def WOp.app (P : WOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  (P.map fun t => t.1 * vfW t.2 u x).sum

def WOp.symb (P : WOp d) (m : ℕ) (x ξ : Fin d → ℝ) : ℂ :=
  (P.map fun t => if t.2.length = m then t.1 * (t.2.map fun V => ((ξ ⬝ᵥ V x : ℝ) : ℂ)).prod else 0).sum

end vfw

def VOpToSOp : Prop :=
  ∀ (d m : ℕ) (P : WOp d) (O : Set (Fin d → ℝ)), IsOpen O →
    (∀ t ∈ P, t.2.length ≤ m ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O) →
    ∃ S : SOp d, S.ord = m ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ (m : WithTop ℕ∞) u O → ∀ x ∈ O, S.app u x = WOp.app P u x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = WOp.symb P m x ξ

def IsChart (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)) : Prop :=
  IsOpen O ∧ IsOpen U ∧ ContDiffOn ℝ ∞ κ O ∧ ContDiffOn ℝ ∞ Φ U ∧
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) ∧ (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g)

def VR {k r d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (X : B.Mat k r) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x => fderiv ℝ Φ (κ x) (κ x * X)

def VL {k r d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (X : B.Mat k r) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x => fderiv ℝ Φ (κ x) (X * κ x)

def ChartSysW : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') → GEqs k r z z' u →
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → WOp d) (m : ι → ℕ),
      (∀ j, m j ≤ 2 * r + k + 1) ∧ (∀ j, ∀ t ∈ P j, t.2.length ≤ m j ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O) ∧
      ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
      (∀ j, ∀ x ∈ O, WOp.app (P j) (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → (∀ j, WOp.symb (P j) (m j) x ξ = 0) →
        ∃ Ξ : B.Mat k r, B.inLie k r Ξ ∧ Ξ ≠ 0 ∧ IsNilpotent Ξ ∧
          (∀ X ∈ JfS.lieOf (UWset k r z) ∪ JfS.lieOf (Nset k r), (Matrix.trace (Ξ * X)).re = 0) ∧
          (∀ X ∈ JfS.lieOf (UWset k r z') ∪ JfS.lieOf (Nset k r),
            (Matrix.trace (Ξ * (κ x * X * (κ x)⁻¹))).re = 0)

theorem chartEqs_of (hA : ChartSysW) (hB : VOpToSOp) : ChartEqs := by
  intro k r z z' d O U κ Φ u hk hz hz' hT hT' hO hU hκ hΦ hκO hΦU hOm hG
  obtain ⟨ι, hι, P, m, hm, hP, huc, hPu, hsym⟩ :=
    hA k r z z' d O U κ Φ u hk hz hz' hT hT' ⟨hO, hU, hκ, hΦ, hκO, hΦU⟩ hOm hG
  have hS : ∀ j, ∃ S : SOp d, S.ord = m j ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ v : (Fin d → ℝ) → ℂ, ContDiffOn ℝ ((m j : ℕ) : WithTop ℕ∞) v O → ∀ x ∈ O,
        S.app v x = WOp.app (P j) v x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = WOp.symb (P j) (m j) x ξ :=
    fun j => hB d (m j) (P j) O hO (hP j)
  choose S hSo hSc hSa hSs using hS
  refine ⟨ι, hι, S, fun j => hSc j, fun j => by rw [hSo j]; exact hm j, huc, ?_, ?_⟩
  · intro j x hx
    rw [hSa j _ (huc.of_le (by exact_mod_cast hm j)) x hx]
    exact hPu j x hx
  · intro x hx ξ hξ hall
    exact hsym x hx ξ hξ (fun j => by rw [← hSs j x hx ξ]; exact hall j)

def ChartCov : Prop :=
  ∀ (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)), IsChart k r d O U κ Φ →
    ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ∃ Ξ₀ : B.Mat k r, B.inLie k r Ξ₀ ∧ (ξ ≠ 0 → Ξ₀ ≠ 0) ∧
      ∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re

def RwChart : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u →
    ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
    (∀ X : B.Mat k r, ContDiffOn ℝ ∞ (VR κ Φ X) O ∧ ContDiffOn ℝ ∞ (VL κ Φ X) O) ∧
    ∀ Xs : List (B.Mat k r), (∀ X ∈ Xs, B.inLie k r X) → Xs.length ≤ 2 * r + k + 1 → ∀ x ∈ O,
      B.Rw Xs u (κ x) = vfW (Xs.map (VR κ Φ)) (fun y => u (κ y)) x ∧
      Xs.foldr Q.LdV u (κ x) = vfW (Xs.map (VL κ Φ)) (fun y => u (κ y)) x

def LieNFin : Prop :=
  ∀ (k r : ℕ), ∃ (q : ℕ) (Xs : Fin q → B.Mat k r), (∀ i, Xs i ∈ JfS.lieOf (Nset k r)) ∧
    ∀ X ∈ JfS.lieOf (Nset k r), B.inLie k r X ∧ ∃ a : Fin q → ℝ, X = ∑ i, ((a i : ℝ) : ℂ) • Xs i

def CapWords : Prop :=
  ∀ (k r j : ℕ), 1 ≤ j → j ≤ 2 * r + k + 1 →
    ∃ (Ys : Fin (2 * r + k + 2) → ℝ) (lam : Fin (2 * r + k + 2) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.CV k r (Ys i : ℂ) f g = (L.map fun t => t.1 • B.Rw t.2 f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * Ξ.charpoly.coeff (2 * r + k + 1 - j)

def cmp {k r : ℕ} (Ξ : B.Mat k r) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => Matrix.trace (Ξ * Q.unitB (Hpk k r) Bs a b)

def CapRWords : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z'] Bs →
    ∀ j, 1 ≤ j → j ≤ k →
    ∃ (ws : Fin (k + 1) → ℂ) (lam : Fin (k + 1) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.capR k r Bs (ws i) f g = (L.map fun t => t.1 • B.Rw t.2 f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def CapLWords : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z] Bs →
    ∀ j, 1 ≤ j → j ≤ k →
    ∃ (ws : Fin (k + 1) → ℂ) (lam : Fin (k + 1) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.capLft k r Bs (ws i) f g = (L.map fun t => t.1 • t.2.foldr Q.LdV f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def CmpZero : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    Q.IsFrameOf k r [z] Bs → ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
    (∀ j, 1 ≤ j → j ≤ k → (cmp Ξ Bs).charpoly.coeff (k - j) = 0) →
    ∀ X ∈ JfS.lieOf (UWset k r z), (Matrix.trace (Ξ * X)).re = 0

def FrameEx : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs

def ChartSysWOfParts : Prop :=
  ChartCov → RwChart → LieNFin → CapWords → CapRWords → CapLWords → CmpZero → FrameEx → ChartSysW

theorem chartEqs_of_parts (hJ : ChartSysWOfParts) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords)
    (h5 : CapRWords) (h6 : CapLWords) (h7 : CmpZero) (h8 : FrameEx) (hB : VOpToSOp) : ChartEqs :=
  chartEqs_of (hJ h1 h2 h3 h4 h5 h6 h7 h8) hB

def SOpField : Prop :=
  ∀ (d : ℕ) (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (O : Set (Fin d → ℝ)), IsOpen O →
    (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) → ContDiffOn ℝ ∞ V O →
    ∃ S' : SOp d, S'.ord = S.ord + 1 ∧ (∀ i w, ContDiffOn ℝ ∞ (S'.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ ((S.ord + 1 : ℕ) : WithTop ℕ∞) u O → ∀ x ∈ O,
        S'.app u x = vfD V (S.app u) x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S'.symb x ξ = ((ξ ⬝ᵥ V x : ℝ) : ℂ) * S.symb x ξ

def SOpLift : Prop :=
  ∀ (d : ℕ) (S : SOp d) (m' : ℕ) (O : Set (Fin d → ℝ)), S.ord ≤ m' → (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) →
    ∃ S' : SOp d, S'.ord = m' ∧ (∀ i w, ContDiffOn ℝ ∞ (S'.a i w) O) ∧ (∀ u x, S'.app u x = S.app u x) ∧
      ∀ x ξ, S'.symb x ξ = if S.ord = m' then S.symb x ξ else 0

def SOpLin : Prop :=
  ∀ (d : ℕ) (S T : SOp d) (c : ℂ) (O : Set (Fin d → ℝ)), S.ord = T.ord → (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) →
    (∀ i w, ContDiffOn ℝ ∞ (T.a i w) O) →
    ∃ R : SOp d, R.ord = S.ord ∧ (∀ i w, ContDiffOn ℝ ∞ (R.a i w) O) ∧
      (∀ u x, R.app u x = c * S.app u x + T.app u x) ∧ ∀ x ξ, R.symb x ξ = c * S.symb x ξ + T.symb x ξ

def VOpToSOpOfSteps : Prop := SOpField → SOpLift → SOpLin → VOpToSOp

theorem chartEqs_of_all (hJ : ChartSysWOfParts) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords)
    (h5 : CapRWords) (h6 : CapLWords) (h7 : CmpZero) (h8 : FrameEx) (hS : VOpToSOpOfSteps) (s1 : SOpField)
    (s2 : SOpLift) (s3 : SOpLin) : ChartEqs :=
  chartEqs_of_parts hJ h1 h2 h3 h4 h5 h6 h7 h8 (hS s1 s2 s3)

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
