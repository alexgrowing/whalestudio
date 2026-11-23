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

namespace GlobalTheory.ArchSchB.LeviPair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_swap_herm {σ : E →ₐ[F] E} (hinv : ∀ t, σ (σ t) = t) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hherm : ∀ i j, σ (J j i) = J i j) (x v : Fin d → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J x v = σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J v x) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, map_sum, map_mul, hinv, hherm, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a b => σ (v a) * (J b a * x b))]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem vecMulVec_mulVec' {A : Type} [CommRing A] {m n : Type} [Fintype n] (p : m → A) (q w : n → A) :
    Matrix.vecMulVec p q *ᵥ w = (q ⬝ᵥ w) • p := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_sum_eq_dot {A : Type} [CommRing A] {m n : Type} [Fintype m] [Fintype n] (x : Matrix m n A)
    (U : m → A) (V : n → A) : ∑ i, ∑ j, x i j * U i * V j = U ⬝ᵥ (x *ᵥ V) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.ArchSchB.LeviPair

open GlobalTheory.ArchSchB.LeviPair in

theorem GlobalTheory.ArchSchB.symp_levi_pair_eq_trace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (r s r' s' i₀ i₁ j₀ j₁ : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ i₀ i₁ → H'.IsAdapted σ B W W₁ j₀ j₁ →
    ∀ (α : Fin d → AE F E) (c₁ c₂ c : Fin n₁ → AE F E) (Z : Matrix (Fin n₁) (Fin d₁) (AE F E)),
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (Matrix.vecMulVec (incV F H.x) α + Matrix.vecMulVec (incM F H.ι *ᵥ c₁) (incV F H'.x) +
        incM F H.ι * Z * (incM F H'.ι)ᵀ + Matrix.vecMulVec (incM F H.ι *ᵥ c₂) (incV F H'.y))
      (Matrix.vecMulVec (incM F H.ι *ᵥ c) (incV F H'.x)) =
    Algebra.trace (AF F) (AE F E) (c₂ ⬝ᵥ (incM F X₁.J *ᵥ fun k => cA σ (c k))) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i₀ i₁ j₀ j₁ hB hX hW hH hH' α c₁ c₂ c Z
  have hinv : ∀ t, σ (σ t) = t := fun t => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hcol : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (m : Fin b), M *ᵥ Pi.single m 1 = fun j => M j m := by
    intro a b M m; ext j; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  set c' : Fin n₁ → AE F E := fun k => cA σ (c k) with hc'
  set A : Fin d → AE F E := incV F (W.J *ᵥ fun l => σ (H'.x l)) with hAdef
  set U : Fin n → AE F E := incM F (X.J * H.ι.map σ) *ᵥ c' with hUdef
  have hA' : ∀ j, ∑ l, incM F W.J j l * cA σ (incV F H'.x l) = A j := by
    intro j
    simp only [hAdef, incV, incM, Matrix.map_apply, OrthPlane.cA_inclR, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hU' : ∀ i, ∑ k, incM F X.J i k * cA σ ((incM F H.ι *ᵥ c) k) = U i := by
    intro i
    simp only [hUdef, hc', incM, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul,
      OrthPlane.cA_inclR, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  have hdotA : ∀ v : Fin d → E, incV F v ⬝ᵥ A = inclR (F := F) (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ W.J v H'.x) := by
    intro v
    simp only [hAdef, incV, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hx0 : ∀ m, ∑ i, H.x i * (X.J * H.ι.map σ) i m = 0 := by
    intro m
    have h := (hH.orth (Pi.single m 1)).1
    rw [hcol] at h
    have h' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ X.J H.x (fun j => H.ι j m) = 0 := by
      rw [form_swap_herm hinv hX.herm, h, map_zero]
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.map_apply] using h'
  have h1 : U ⬝ᵥ incV F H.x = 0 := by
    rw [dotProduct_comm, hUdef, Matrix.dotProduct_mulVec]
    have : incV F H.x ᵥ* incM F (X.J * H.ι.map σ) = 0 := by
      ext m
      have := congrArg (inclR (F := F) (AF F)) (hx0 m)
      simpa only [Matrix.vecMul, dotProduct, incV, incM, Matrix.map_apply, map_sum, map_mul, map_zero, Pi.zero_apply] using this
    rw [this, zero_dotProduct]
  have h2 : incV F H'.x ⬝ᵥ A = 0 := by rw [hdotA, hH'.xx, map_zero]
  have h3 : (incM F H'.ι)ᵀ *ᵥ A = 0 := by
    ext m
    change incV F (fun j => H'.ι j m) ⬝ᵥ A = 0
    rw [hdotA, ← hcol, (hH'.orth _).1, map_zero]
  have h4 : incV F H'.y ⬝ᵥ A = -1 := by
    rw [hdotA, OrthPlane.form_swap hinv hW.skew, hH'.xy, map_one, map_neg, map_one]
  have hg : (incM F H.ι)ᵀ * incM F (X.J * H.ι.map σ) = incM F X₁.J := by
    rw [← hH.gram, Matrix.mul_assoc]
    simp only [incM, Matrix.transpose_map, Matrix.map_mul]
  have h5 : U ⬝ᵥ (incM F H.ι *ᵥ c₂) = c₂ ⬝ᵥ (incM F X₁.J *ᵥ c') := by
    rw [dotProduct_comm, hUdef, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hg,
      ← Matrix.dotProduct_mulVec]
  unfold symp
  rw [TensForm.hTens_vmv_right]
  simp only [hA', hU']
  rw [sum_sum_eq_dot, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, vecMulVec_mulVec', vecMulVec_mulVec',
    vecMulVec_mulVec', ← Matrix.mulVec_mulVec, h2, h3, h4]
  simp only [Matrix.mulVec_zero, zero_smul, add_zero, dotProduct_add, dotProduct_smul, smul_eq_mul, h1, mul_zero,
    zero_add, dotProduct_zero, neg_smul, one_smul, dotProduct_neg, h5, neg_one_mul, neg_neg]
