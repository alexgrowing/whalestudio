import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.PointLattice

section General

variable {E A n : Type} [Field E] [CommRing A] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem latUnip_map_mulVec (ι : E →+* A) (M : Matrix n n E) (y : n → E) :
    (fun i => ι ((M *ᵥ y) i)) = M.map ι *ᵥ fun i => ι (y i) := by
  funext i
  exact RingHom.map_mulVec ι M y i

theorem latUnip_conj_pow (X Y G : Matrix n n A) (h : X * Y = 1) (m : ℕ) :
    (Y * G * X - 1) ^ m * Y = Y * (G - 1) ^ m := by
  have h1 : (Y * G * X - 1) * Y = Y * (G - 1) := by
    rw [sub_mul, one_mul, mul_assoc (Y * G), h, mul_one, mul_sub, mul_one]
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_assoc, h1, ← mul_assoc, ih, mul_assoc, ← pow_succ]

end General

theorem lamX_unipMod : ∀ (I : AutInst) (x a : I.GA) (γ : GL (Fin I.n) I.E) (l : ℕ), 1 ≤ l → I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → (x⁻¹ * a * x).2 ∈ I.Kset → I.UnipMod l (x⁻¹ * a * x).2 → (∀ y ∈ lamX I x, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I x) ∧ ∀ y ∈ lamX I x, ∃ z ∈ lamX I x, (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y = (l : I.E) • z := by
  intro I x a γ l hl hfa hk hu
  have hK : ∀ w, w ∈ I.Lf ↔ I.fmat (x⁻¹ * a * x).2 *ᵥ w ∈ I.Lf := hk
  have hmem : ∀ y, y ∈ lamX I x ↔
      I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := (lamX_selfDual I x).1
  have hconj : I.fmat (x⁻¹ * a * x).2 = I.fmat x.2⁻¹ * I.fmat a.2 * I.fmat x.2 := rfl
  have hXY : I.fmat x.2 * I.fmat x.2⁻¹ = 1 := by
    show I.fmat (x.2 * x.2⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have key : ∀ y, I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) i)) =
      I.fmat (x⁻¹ * a * x).2 *ᵥ (I.fmat x.2⁻¹ *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) := by
    intro y
    rw [latUnip_map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) (γ : Matrix (Fin I.n) (Fin I.n) I.E) y, ← hfa, hconj, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, mul_assoc (I.fmat x.2⁻¹ * I.fmat a.2), hXY, mul_one]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [hmem, key]
    exact (hK _).1 ((hmem y).1 hy)
  · obtain ⟨w, hw, hwe⟩ := hu _ ((hmem y).1 hy)
    have hl0 : (l : I.E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨(l : I.E)⁻¹ • ((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y), ?_, ?_⟩
    · rw [hmem]
      have hpow : (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n).map (Formalism.UG.inclE (F := I.F) (Af I.F)) = (I.fmat a.2 - 1) ^ I.n := by
        rw [hfa, ← RingHom.mapMatrix_apply, map_pow, map_sub, map_one, RingHom.mapMatrix_apply]
      have hcp := latUnip_conj_pow (I.fmat x.2) (I.fmat x.2⁻¹) (I.fmat a.2) hXY I.n
      have e1 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((l : I.E)⁻¹ • ((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y)) i)) =
          Formalism.UG.inclE (F := I.F) (Af I.F) ((l : I.E)⁻¹) • fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y) i) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      have e2 : I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y) i)) =
          (l : TensorProduct I.F I.E (Af I.F)) • w := by
        rw [latUnip_map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) y, hpow, Matrix.mulVec_mulVec, ← hcp,
          ← Matrix.mulVec_mulVec, ← hconj, hwe]
      rw [e1, Matrix.mulVec_smul, e2, smul_smul, ← map_natCast (Formalism.UG.inclE (F := I.F) (Af I.F)) l, ← map_mul,
        inv_mul_cancel₀ hl0, map_one, one_smul]
      exact hw
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]

end GlobalTheory.PointLattice
