import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairAdaptedPlanes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagrOrth

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem psi_mul_neg (ψ : AddChar (AF F) ℂ) (a : AF F) : ψ a * ψ (-a) = 1 := by
  rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

theorem psi_ne_zero (ψ : AddChar (AF F) ℂ) (a : AF F) : ψ a ≠ 0 := by
  intro h; have := psi_mul_neg ψ a; rw [h, zero_mul] at this; exact zero_ne_one this

theorem schr_injective (ψ : AddChar (AF F) ℂ) (hψ : ∀ b : AF F, (∀ a, ψ (a * b) = 1) → b = 0) {κ : Type} [Fintype κ]
    [DecidableEq κ] (w w' : (κ → AF F) × (κ → AF F)) (h : ∀ φ, schr ψ w φ = schr ψ w' φ) : w = w' := by
  classical
  have h1 : w.1 = w'.1 := by
    have := congrFun (h fun x => if x = 0 then 1 else 0) (-w.1)
    simp only [schr, neg_add_cancel, if_true, mul_one] at this
    by_contra hne
    have hne' : -w.1 + w'.1 ≠ 0 := by
      intro h0; apply hne; rw [neg_add_eq_zero] at h0; exact h0
    rw [if_neg hne', mul_zero] at this
    exact psi_ne_zero ψ _ this
  have h2 : ∀ x : κ → AF F, ψ (x ⬝ᵥ w.2) = ψ (x ⬝ᵥ w'.2) := by
    have e := fun x => congrFun (h fun _ => 1) x
    simp only [schr, mul_one, h1] at e
    have e0 := e 0
    simp only [zero_dotProduct, zero_add] at e0
    intro x
    have ex := e x
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e0] at ex
    exact mul_right_cancel₀ (psi_ne_zero ψ _) ex
  refine Prod.ext h1 (funext fun i => ?_)
  rw [← sub_eq_zero]
  apply hψ
  intro a
  have := h2 (Pi.single i a)
  rw [single_dotProduct, single_dotProduct] at this
  rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, this, psi_mul_neg]

open GlobalTheory.MixedLagrX GlobalTheory.MixedLagrXW in

theorem symp_one_iso_zero {B : Base F E} {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    {i₀ i₁ : ℕ} (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (z : Matrix (Fin n) (Fin d₁) (AE F E)) (y : Fin n → AE F E) :
    sy σ X W (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) (Matrix.vecMulVec y (incV F H'.x)) = 0 := by
  rw [sy, symp, repA, hTens_sandwich, incM_gram, incM_gram, gram_ιx hH', incM_zero]
  simp

open GlobalTheory.MixedLagrX GlobalTheory.MixedLagrXW in

theorem symp_one_one {B : Base F E} {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    {i₀ i₁ : ℕ} (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (z z' : Matrix (Fin n) (Fin d₁) (AE F E)) :
    sy σ X W (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) = sy σ X W₁ z z' := by
  have g1 : (1 : Matrix (Fin n) (Fin n) E)ᵀ * X.J * (1 : Matrix (Fin n) (Fin n) E).map σ = X.J := by
    rw [Matrix.transpose_one, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.one_mul, Matrix.mul_one]
  rw [sy, sy, symp, symp, hTens_sandwich, incM_gram, incM_gram, g1, hH'.gram, GlobalTheory.MixedLagrGram.hTens_eq_trace]

theorem psi_nondeg [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (b : AF F) (h : ∀ a, ψ (a * b) = 1) :
    b = 0 := by
  obtain ⟨hv, -, hinf⟩ := GlobalTheory.GaugeEx.CharLoc.char_local F ψ (GlobalTheory.StdCharFromIsStd.isCharAF hψ)
  refine Prod.ext (hinf b.1 fun y => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
  · have e := h (pairA F y 0)
    rw [show pairA F y 0 * b = pairA F (b.1 * y) 0 from Prod.ext (mul_comm _ _) (zero_mul _)] at e
    exact e
  · show b.2 v = 0
    by_contra hb
    obtain ⟨y, hy⟩ := hv v
    apply hy
    have e := h (pairA F 0 (singleV F v (y * (b.2 v)⁻¹)))
    rw [show pairA F 0 (singleV F v (y * (b.2 v)⁻¹)) * b = pairA F 0 (singleV F v y) from
      Prod.ext (zero_mul _) (by
        show singleV F v (y * (b.2 v)⁻¹) * b.2 = singleV F v y
        rw [GlobalTheory.SnMass.Inhab.single_mul, mul_assoc, inv_mul_cancel₀ hb, mul_one])] at e
    exact e

end GlobalTheory.MixedLagrOrth

open GlobalTheory.MixedLagrOrth in

theorem GlobalTheory.MixedLagrOrth.mem_iso_zero_of_orth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F),
        (∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr B.ψ w φ = M.co.rho B.ψ u (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ)) →
        (∀ z : Matrix (Fin n) (Fin d₁) E,
          w.1 ⬝ᵥ (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * incM F z * (incM F H'.ι)ᵀ)).2 =
            (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * incM F z * (incM F H'.ι)ᵀ)).1 ⬝ᵥ w.2) →
        ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), w = M.co.e u := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁ w hex horth
  obtain ⟨u, ⟨y, rfl⟩, z, hz, hw⟩ := hex
  have hD : ∀ p q, GlobalTheory.MixedLagrXW.sy σ X W p q = (M.co.e p).1 ⬝ᵥ (M.co.e q).2 - (M.co.e q).1 ⬝ᵥ (M.co.e p).2 :=
    M.co.form
  have hD₁ : ∀ p q, GlobalTheory.MixedLagrXW.sy σ X W₁ p q =
      (M₁.co.e p).1 ⬝ᵥ (M₁.co.e q).2 - (M₁.co.e q).1 ⬝ᵥ (M₁.co.e p).2 := M₁.co.form
  have ouv : ∀ zz : Matrix (Fin n) (Fin d₁) (AE F E),
      (M.co.e (Matrix.vecMulVec y (incV F H'.x))).1 ⬝ᵥ (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * zz * (incM F H'.ι)ᵀ)).2 -
        (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * zz * (incM F H'.ι)ᵀ)).1 ⬝ᵥ
          (M.co.e (Matrix.vecMulVec y (incV F H'.x))).2 = 0 := by
    intro zz
    have h := symp_one_iso_zero (X := X) hH' zz y
    rw [hD] at h
    linear_combination -h
  have hw' : w = M.co.e (Matrix.vecMulVec y (incV F H'.x)) +
      M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
    haveI : IsTotallyReal F := hP.base.cm.1
    refine schr_injective B.ψ (psi_nondeg hP.base.std) _ _ fun φ => ?_
    rw [hw φ]
    simp only [Darboux.rho]
    rw [GlobalTheory.MixedLagr.schr_comp, ouv z, mul_zero, AddChar.map_zero_eq_one, one_smul]
  have key : ∀ z' : Matrix (Fin n) (Fin d₁) E, (M₁.co.e (incM F z')).1 ⬝ᵥ (M₁.co.e z).2 = 0 := by
    intro z'
    have h := horth z'
    have o := ouv (incM F z')
    have c := symp_one_one (X := X) hH' z (incM F z')
    rw [hD, hD₁, hz, zero_dotProduct] at c
    rw [hw'] at h
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add] at h
    linear_combination c - h + o
  obtain ⟨f₁, hf₁, hfe₁⟩ := GlobalTheory.MixedLagrX.exists_ratMap M₁ hP₁.good.rat
  have h2 : Module.finrank F E = 2 := hP.base.cm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hsurj : Function.Surjective f₁ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hf₁
    simp [Module.finrank_matrix, Module.finrank_prod, h2]
    ring
  have hz2 : (M₁.co.e z).2 = 0 := by
    funext i
    obtain ⟨x, hx⟩ := hsurj (Pi.single i 1, 0)
    have h := key x
    rw [← hfe₁ x, hx, GlobalTheory.MixedLagr.hat] at h
    have hs : (fun j => algebraMap F (AF F) ((Pi.single i (1 : F) : Fin n × Fin d₁ → F) j)) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    simp only at h
    rw [hs, single_dotProduct, one_mul] at h
    exact h
  have hz0 : z = 0 := M₁.co.e.injective (by rw [map_zero]; exact Prod.ext hz hz2)
  refine ⟨_, ⟨y, rfl⟩, ?_⟩
  rw [hw', hz0, Matrix.mul_zero, Matrix.zero_mul, map_zero, add_zero]
