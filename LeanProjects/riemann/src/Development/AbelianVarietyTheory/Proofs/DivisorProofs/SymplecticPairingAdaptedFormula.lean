import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetAdditiveSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDeterminantNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrAEMixedNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumThreeComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensVmvLeft
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB

namespace GlobalTheory.PairX

theorem vmv_sum {A α β : Type} [CommRing A] [Fintype α] [Fintype β] (u : α → A) (v : β → A) (P : α → A) (Q : β → A) :
    ∑ i, ∑ j, Matrix.vecMulVec u v i j * P i * Q j = (∑ i, u i * P i) * ∑ j, v j * Q j := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.vecMulVec_apply]; ring

theorem mul_sum {A α β γ : Type} [CommRing A] [Fintype α] [Fintype β] [Fintype γ] (M : Matrix α γ A) (C : Matrix γ β A)
    (P : α → A) (Q : β → A) :
    ∑ i, ∑ j, (M * C) i j * P i * Q j = ∑ m, (∑ i, M i m * P i) * ∑ j, C m j * Q j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [OrthPlane.sum_three_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_swap_herm {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (hinv : ∀ t, σ (σ t) = t) {d : ℕ}
    {J : Matrix (Fin d) (Fin d) E} (hh : ∀ i j, σ (J j i) = J i j) (x v : Fin d → E) : form σ J x v = σ (form σ J v x) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hinv, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hh]; ring

theorem dotProduct_J_c_eq_neg_of_pairing : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ : ℕ} (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ) (JW : Matrix (Fin d) (Fin d) E),
    B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∀ (α β a : Fin d → AE F E) (C : Matrix (Fin n₁) (Fin d) (AE F E)),
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F JW)
      (Matrix.vecMulVec (incV F H.x) α + incM F H.ι * C + Matrix.vecMulVec (incV F H.y) β) (Matrix.vecMulVec (incV F H.x) a) =
    -Algebra.trace (AF F) (AE F E) (β ⬝ᵥ (incM F JW *ᵥ fun k => cA σ (a k))) := by
  intro F E _ _ _ _ _ σ B n d n₁ X X₁ H r s i₀ i₁ JW hB hX hA α β a C
  have hinv : ∀ t, σ (σ t) = t := fun t => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  set P : Fin n → AE F E := fun i => ∑ k, incM F X.J i k * cA σ (incV F H.x k) with hPdef
  have hform : ∀ u : Fin n → E, ∑ i, inclR (F := F) (AF F) (u i) * P i = inclR (F := F) (AF F) (form σ X.J u H.x) := by
    intro u
    simp only [hPdef, form, dotProduct, Matrix.mulVec, incM, incV, Matrix.map_apply, OrthPlane.cA_inclR, map_sum, map_mul,
      Finset.mul_sum]
  have hcol : ∀ m, H.ι *ᵥ Pi.single m 1 = fun j => H.ι j m := by
    intro m; ext j; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  unfold symp
  rw [TensForm.hTens_add_left, TensForm.hTens_add_left, TensForm.hTens_vmv_right, TensForm.hTens_vmv_right,
    TensForm.hTens_vmv_right, vmv_sum, vmv_sum, mul_sum]
  have h1 : ∑ i, incV F H.x i * P i = 0 := by
    simp only [incV]; rw [hform, hA.xx, map_zero]
  have h2 : ∀ m, ∑ i, incM F H.ι i m * P i = 0 := by
    intro m
    have := hform (fun i => H.ι i m)
    simp only [incM, Matrix.map_apply]
    rw [this, ← hcol, (hA.orth _).1, map_zero]
  have h3 : ∑ i, incV F H.y i * P i = 1 := by
    simp only [incV]; rw [hform, form_swap_herm hinv hX.herm, hA.xy, map_one, map_one]
  simp only [hPdef] at h1 h2 h3 ⊢
  simp only [h1, h2, h3, zero_mul, Finset.sum_const_zero, zero_add, one_mul, neg_mul, map_neg, dotProduct, Matrix.mulVec]

end GlobalTheory.PairX
