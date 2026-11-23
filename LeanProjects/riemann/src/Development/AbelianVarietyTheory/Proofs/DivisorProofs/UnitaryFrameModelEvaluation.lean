import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTorusElementExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameTorusLatticeActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFunctionalNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryInverseInfiniteNonzeroStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

theorem vanish_of_block_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ Φ ∈ M.So B.ψ B.τ₁, ∀ (g : UA σ X.J) (h : UA σ W.J) (ξ : Fin n × Fin d → F), (∃ i, ∀ j ∈ blk i, ξ j = 0) →
      e (om (g, h) Φ) (fun j => algebraMap F (AF F) (ξ j)) = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP q x y hfr M₁ blk e hG hco hev Φ hΦ g h ξ hξ
  obtain ⟨i, hi⟩ := hξ
  have htor := GlobalTheory.T.unitary_torus_element_exists F E σ B n X r s hP.base hP.herm q x y hfr
  have hblk := GlobalTheory.T.frame_torus_lattice_action F E σ B n d X W q x y M₁ blk hG hco htor i
  have hW := IsUWeilPair.isUSplitting hP.weil
  set ξ' : Fin n × Fin d → AF F := fun j => algebraMap F (AF F) (ξ j) with hξ'
  let Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => e (om (g, h) Ψ) ξ'
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hxi : x i ≠ 0 := by
    intro h0
    have := hfr.2.2 i i
    simp [h0, form] at this
  have hc := GlobalTheory.T.unitary_inverse_infinite_nonzero F E σ B n X.J g (x i) hxi
  refine GlobalTheory.T.pair_functional_nonvanishing hKP F E σ B n d X W M χX χW om r s r' s' hP Λ (mat g⁻¹ *ᵥ incV F (x i)) hc ?_ Φ hΦ
  intro z _ _ Ψ hΨ
  show e (om (g, h) (M.co.rho B.ψ _ Ψ)) ξ' = e (om (g, h) Ψ) ξ'
  rw [hW.impl (g, h) _ Ψ hΨ]
  have hgg : mat g * mat g⁻¹ = 1 := by simp [mat]
  have hgen : ∀ (A : Matrix (Fin n) (Fin n) (AE F E)) (Bm : Matrix (Fin d) (Fin d) (AE F E))
      (u : Fin n → AE F E) (w : Fin d → AE F E), A * Matrix.vecMulVec u w * Bmᵀ = Matrix.vecMulVec (A *ᵥ u) (Bm *ᵥ w) := by
    intro A Bm u w
    ext k l
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hact : actAB (cA σ) (g, h) (Matrix.vecMulVec (mat g⁻¹ *ᵥ incV F (x i)) z) =
      Matrix.vecMulVec (incV F (x i)) (mat h *ᵥ z) := by
    change mat g * _ * (mat h)ᵀ = _
    rw [hgen, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  rw [hact]
  obtain ⟨z', hz', hze⟩ := hblk (mat h *ᵥ z)
  have hΨ2 : om (g, h) Ψ ∈ schA F _ := hW.pres _ _ hΨ
  have hheis := hev.Heisenberg₂ (Matrix.vecMulVec (incV F (x i)) (mat h *ᵥ z)) _ hΨ2
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp [incM, Matrix.map_one]
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by
    simp [incM, Matrix.map_one]
  rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at hheis
  rw [hheis]
  have hdot : ξ' ⬝ᵥ z' = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ∈ blk i
    · simp [hξ', hi j hj]
    · simp [hz' j hj]
  simp only [Darboux.rho, hze, schr, hdot, zero_dotProduct, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThKTorus
