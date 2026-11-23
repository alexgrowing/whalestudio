import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexifiedDerivedActionLieHomGramAdjointStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

private lemma inv_conj_mul_conj {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q)
    (A B : Matrix (Fin n) (Fin n) ℂ) : (Q⁻¹ * A * Q) * (Q⁻¹ * B * Q) = Q⁻¹ * (A * B) * Q := by
  have h : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
  calc (Q⁻¹ * A * Q) * (Q⁻¹ * B * Q) = Q⁻¹ * A * (Q * Q⁻¹) * B * Q := by
        simp only [Matrix.mul_assoc]
    _ = Q⁻¹ * (A * B) * Q := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private lemma single_one_mul_single_one_jet_harmonics {n : ℕ} (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · simp [h]

theorem conj_single_comm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
      (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q) =
    (if b = c then Q⁻¹ * Matrix.single a d 1 * Q else 0) -
      (if d = a then Q⁻¹ * Matrix.single c b 1 * Q else 0) := by
  rw [inv_conj_mul_conj Q hQ, inv_conj_mul_conj Q hQ, ← Matrix.sub_mul, ← Matrix.mul_sub,
    single_one_mul_single_one_jet_harmonics, single_one_mul_single_one_jet_harmonics]
  split_ifs <;> simp [Matrix.mul_sub, Matrix.sub_mul]

theorem smooth_gl_module : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  intro hK k r ε mu R hDS Q hQ
  obtain ⟨hmem, hlin, hadd, -, hbr, -⟩ := GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hDS
  have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
  have hz : ∀ Y, R.dC Y 0 = 0 := fun Y => by
    have h := hlin Y 1 0 h0 0 h0
    simpa using h
  have hY0 : ∀ v ∈ R.sm, R.dC 0 v = 0 := fun v hv => by
    have h := hadd 0 0 1 v hv
    simpa using h
  have hsub : ∀ Y Z, ∀ v ∈ R.sm, R.dC (Y - Z) v = R.dC Y v - R.dC Z v := fun Y Z v hv => by
    have h := hadd Z (Y - Z) 1 v hv
    simp only [one_smul, add_sub_cancel] at h
    rw [h, add_sub_cancel_left]
  let E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub := fun a b =>
    { toFun := fun v => ⟨R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v, hmem _ v v.2⟩
      map_add' := fun v w => Subtype.ext (by simpa using hlin _ 1 v v.2 w w.2)
      map_smul' := fun c v => Subtype.ext (by simpa [hz] using hlin _ c v v.2 0 h0) }
  refine ⟨E, fun a b v => rfl, ?_⟩
  intro a b c d
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have lhs : (((E a b * E c d - E c d * E a b) v : R.smSub) : R.H) =
      R.dC ((Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
        (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q)) v := by
    rw [← hbr _ _ v v.2]; rfl
  rw [lhs, conj_single_comm Q hQ a b c d, hsub _ _ v v.2]
  split_ifs <;> simp [E, hY0 v v.2]

end GlobalTheory
