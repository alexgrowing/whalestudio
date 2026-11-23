import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairThetaIntegralStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

open GlobalTheory.ThK.UnipDom GlobalTheory.ThK.UnipDom.Inverse

private theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (v w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ v (GlobalTheory.WeilM.schr ψ w Φ) =
      ψ (⅟(2 : R) * (v.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ v.2)) • GlobalTheory.WeilM.schr ψ (v + w) Φ := by
  funext z
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add,
    Prod.snd_add, add_assoc]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(v.1 ⬝ᵥ w.2)) * invOf_mul_self (2 : R)

private theorem rho_add' {R : Type} [CommRing R] [Invertible (2 : R)] {U : Type} [AddCommGroup U] [Module R U]
    {B : U → U → R} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar R ℂ)
    (Φ : (κ → R) → ℂ) (x y : U) :
    co.rho ψ (x + y) Φ = ψ (-(⅟(2 : R) * B x y)) • co.rho ψ x (co.rho ψ y Φ) := by
  simp only [GlobalTheory.WeilM.Darboux.rho]
  rw [schr_schr', ← co.form, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul,
    map_add]

private theorem hTens_vmv {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (p p' : α → A) (q q' : β → A) :
    hTens c JA JB (Matrix.vecMulVec p q) (Matrix.vecMulVec p' q') =
      (p ⬝ᵥ JA *ᵥ fun k => c (p' k)) * (q ⬝ᵥ JB *ᵥ fun l => c (q' l)) := by
  calc hTens c JA JB (Matrix.vecMulVec p q) (Matrix.vecMulVec p' q')
      = ∑ i, ∑ j, ∑ k, ∑ l, (p i * JA i k * c (p' k)) * (q j * JB j l * c (q' l)) := by
        simp only [hTens, Matrix.vecMulVec_apply, map_mul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    _ = _ := by
        rw [dotProduct, dotProduct, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem fA_iota {σ : E →ₐ[F] E} {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E)
    (x : Fin d → E) (h : ∀ v, form σ J (ι *ᵥ v) x = 0) (η : Fin d₁ → AE F E) :
    fA σ J (incM F ι *ᵥ η) (incV F x) = 0 := by
  unfold fA
  rw [dotProduct_comm, Matrix.dotProduct_mulVec]
  have hz : ((incM F J *ᵥ fun i => cA σ (incV F x i)) ᵥ* incM F ι) = 0 := by
    funext j
    have h0 := h (Pi.single j 1)
    rw [form, Matrix.mulVec_single_one] at h0
    simp only [dotProduct, Matrix.mulVec, Matrix.col_apply] at h0
    have : ((incM F J *ᵥ fun i => cA σ (incV F x i)) ᵥ* incM F ι) j =
        inclR (F := F) (AF F) (∑ i, ι i j * ∑ k, J i k * σ (x k)) := by
      simp only [Matrix.vecMul, dotProduct, Matrix.mulVec, incM, incV, Matrix.map_apply, cA_inclR, map_sum, map_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, Pi.zero_apply, h0, map_zero]
  rw [hz, zero_dotProduct]

private theorem fA_swap' {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (v w : Fin n → AE F E) :
    fA σ J w v = cA σ (fA σ J v w) := by
  have hJ' : ∀ i k, cA σ (incM F J i k) = incM F J k i := by
    intro i k; simp [incM, cA_inclR, hJ]
  simp only [fA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA hσ, hJ', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem fA_add_right' (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → AE F E) :
    fA σ J v (w + w') = fA σ J v w + fA σ J v w' := by
  simp only [fA, dotProduct, Matrix.mulVec, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private theorem symp_vmv (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (p q : Fin n → AE F E) (w : Fin d → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F J) (incM F JW) (Matrix.vecMulVec p w) (Matrix.vecMulVec q w) =
      -Algebra.trace (AF F) (AE F E) (fA σ J p q * GlobalTheory.UnipMass.hA σ JW w w) := by
  rw [symp, hTens_vmv, neg_one_mul, map_neg]
  rfl

end

theorem UpperTheory.theta_pair_plane_compat :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
                 (n d n₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (M : Model σ X W) (M₂ : Model σ X₁ W) (H : Plane E n n₁) (j₀ j₁ : ℕ)
                 (χX χW : Chr F E) (om : Rep σ X W) (om₂ : Rep σ X₁ W) (r s r₁ s₁ r' s' : ℕ),
                 IsPair B M χX χW om r s r' s' → IsPair B M₂ χX χW om₂ r₁ s₁ r' s' → H.IsAdapted σ B X X₁ j₀ j₁ →
                 ∀ e₁ : Fn F n d →ₗ[ℂ] Fn F n₁ d, IsEv B M M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁ →
                 ∀ u ∈ unip σ X H, ∀ (z : Fin n₁ → AE F E) (β : AE F E),
                   mat u⁻¹ *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ z + β • incV F H.x → ∀ (w : Fin d → AE F E), ∀ Ψ ∈ schA F (Fin n × Fin d),
                   e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) w) (om (u, 1) Ψ)) =
                     B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (β * GlobalTheory.UnipMass.hA σ W.J w w)) •
                       M₂.co.rho B.ψ (Matrix.vecMulVec z w) (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) w) Ψ)) := by
  intro hKP F E _ _ _ _ _ σ B n d n₁ X W X₁ M M₂ H j₀ j₁ χX χW om om₂ r s r₁ s₁ r' s' hP hP₂ hH e₁ he u hu z β hv w Ψ hΨ
  have hstd : IsStd B.ψ := hP.base.std
  have hσ : ∀ e, σ (σ e) = e := sigma_sigma hP.base.cm
  have hsch : ∀ γ, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ γ Φ ∈ schA F (Fin n × Fin d) :=
    fun γ Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd γ Φ hΦ
  have himpl := (IsUWeilPair.isUSplitting hP.weil).impl (u, (1 : UA σ W.J))
    (Matrix.vecMulVec (mat u⁻¹ *ᵥ incV F H.y) w) Ψ hΨ
  have hact : actAB (cA σ) (u, (1 : UA σ W.J)) (Matrix.vecMulVec (mat u⁻¹ *ᵥ incV F H.y) w) =
      Matrix.vecMulVec (incV F H.y) w := by
    show mat u * _ * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_mulVec,
      ← GlobalTheory.ThK.UnipDom.Inverse.mat_mul, mul_inv_cancel, GlobalTheory.ThK.UnipDom.Inverse.mat_one, Matrix.one_mulVec]
  rw [hact] at himpl
  have hI : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hix : fA σ X.J (incM F H.ι *ᵥ z) (incV F H.x) = 0 := fA_iota X.J H.ι H.x (fun v => (hH.orth v).1) z
  have hiy : fA σ X.J (incM F H.ι *ᵥ z) (incV F H.y) = 0 := fA_iota X.J H.ι H.y (fun v => (hH.orth v).2) z
  have hxi : fA σ X.J (incV F H.x) (incM F H.ι *ᵥ z) = 0 := by rw [fA_swap' hσ hP.herm.herm, hix, map_zero]
  have hxy : fA σ X.J (incV F H.x) (incV F H.y) = 1 := by rw [fA_incV, hH.xy, map_one]
  have hsum : Matrix.vecMulVec (mat u⁻¹ *ᵥ incV F H.y) w =
      Matrix.vecMulVec (β • incV F H.x) w + Matrix.vecMulVec (incM F H.ι *ᵥ z + incV F H.y) w := by
    rw [hv]; ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.add_apply]
    ring
  have hsum2 : Matrix.vecMulVec (incM F H.ι *ᵥ z + incV F H.y) w =
      Matrix.vecMulVec (incM F H.ι *ᵥ z) w + Matrix.vecMulVec (incV F H.y) w := by
    ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.add_apply]
    ring
  have hΨA := hsch (Matrix.vecMulVec (incV F H.y) w) Ψ hΨ
  have h2 : M.co.rho B.ψ (Matrix.vecMulVec (incM F H.ι *ᵥ z + incV F H.y) w) Ψ =
      M.co.rho B.ψ (Matrix.vecMulVec (incM F H.ι *ᵥ z) w) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) w) Ψ) := by
    rw [hsum2, rho_add', symp_vmv, hiy, zero_mul, map_zero, neg_zero, mul_zero, neg_zero, AddChar.map_zero_eq_one,
      one_smul]
  have hinv := he.inv (Matrix.vecMulVec (β • incV F H.x) w)
    ⟨β • w, (GlobalTheory.ThK.IsoZero.vmv_smul_right _ _ _).symm⟩ _
    (hsch (Matrix.vecMulVec (incM F H.ι *ᵥ z + incV F H.y) w) Ψ hΨ)
  have hheis := he.Heisenberg₂ (Matrix.vecMulVec z w) _ hΨA
  rw [hI, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec] at hheis
  rw [← himpl, GlobalTheory.T.adapted_plane_pair_theta_integral hKP.base F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₂ om₂ r₁ s₁ hH hP₂ e₁ he
    u hu _ (hsch _ Ψ hΨ), hsum, rho_add', map_smul, hinv, h2, hheis, symp_vmv, fA_smul_left, fA_add_right', hxi, hxy,
    zero_add, mul_one, mul_neg, neg_neg]
