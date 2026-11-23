import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTensorLeftFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleConjFunctionalStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConjRelDbl

open GlobalTheory.DblEval (conjLin conjLin_apply)

section Heis

variable {R : Type} [CommRing R] [Invertible (2 : R)]

omit [Invertible (2 : R)] in
theorem fromCols_zero_mul_blockDiag_transpose {m a b : Type} [Fintype a] [Fintype b]
    (z : Matrix m b R) (A : Matrix a b R) :
    Matrix.fromCols (0 : Matrix m b R) z * (Matrix.fromBlocks A 0 0 A)ᵀ = Matrix.fromCols (0 : Matrix m a R) (z * Aᵀ) := by
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero]
  ext i j
  cases j <;> simp [Matrix.mul_apply, Matrix.fromCols, Matrix.fromBlocks, Fintype.sum_sum_type]

theorem rho_fromCols_zero_boxFun {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (ξ : E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (d : Darboux (symp c ξ JA JB) κ) (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) (h : IsDblCoord c ξ JA JB d dd)
    (ψ : AddChar R ℂ) (w : Matrix α β E) (φ₁ φ₂ : (κ → R) → ℂ) :
    dd.rho ψ (Matrix.fromCols 0 w) (boxFun φ₁ φ₂) = boxFun φ₁ (d.rho ψ⁻¹ w φ₂) := by
  funext y
  obtain ⟨u, v, rfl⟩ : ∃ u v, y = Sum.elim u v := ⟨_, _, (Sum.elim_comp_inl_inr y).symm⟩
  have h' := h 0 w
  simp only [Darboux.rho, boxFun, h', schr, map_zero, Prod.fst_zero, Prod.snd_zero, neg_zero,
    sumElim_dotProduct_sumElim, Sum.elim_add_add, Sum.elim_comp_inl, Sum.elim_comp_inr, AddChar.inv_apply,
    dotProduct_zero, zero_dotProduct, add_zero, zero_add, mul_zero, dotProduct_neg]
  have e1 : (Sum.elim u v + Sum.elim (0 : κ → R) (d.e w).1) ∘ Sum.inl = u := funext fun i => by simp
  have e2 : (Sum.elim u v + Sum.elim (0 : κ → R) (d.e w).1) ∘ Sum.inr = v + (d.e w).1 := funext fun i => by simp
  rw [e1, e2, neg_add, mul_neg]
  ring

omit [CommRing R] [Invertible (2 : R)] in
theorem boxFun_cancel {κ κ' : Type} {u : (κ → R) → ℂ} {v v' : (κ' → R) → ℂ} (t₀ : κ → R) (hu : u t₀ ≠ 0)
    (h : boxFun u v = boxFun u v') : v = v' :=
  funext fun s => mul_left_cancel₀ hu (by simpa [boxFun] using congrFun h (Sum.elim t₀ s))

variable (ψ : AddChar R ℂ) (hψ : ∀ t, ‖ψ t‖ = 1)
include hψ

theorem conj_psi' (t : R) : starRingEnd ℂ (ψ t) = ψ⁻¹ t := by
  rw [AddChar.inv_apply, AddChar.map_neg_eq_inv]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ t]
  norm_num

theorem conj_schr' {κ : Type} [Fintype κ] (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) (x : κ → R) :
    starRingEnd ℂ (schr ψ w φ x) = schr ψ⁻¹ w (fun x => starRingEnd ℂ (φ x)) x := by
  simp only [schr, map_mul, conj_psi' ψ hψ]

theorem conj_schr_inv' {κ : Type} [Fintype κ] (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) (x : κ → R) :
    starRingEnd ℂ (schr ψ⁻¹ w φ x) = schr ψ w (fun x => starRingEnd ℂ (φ x)) x := by
  simp only [schr, map_mul, AddChar.inv_apply, conj_psi' ψ hψ, inv_inv, neg_neg]

end Heis

end GlobalTheory.ConjRelDbl

end

noncomputable section

namespace GlobalTheory.ConjRelDbl

open GlobalTheory.DblEval (conjLin conjLin_apply)

section admitted

def conjForm {X : Type} (l : (X → ℂ) →ₗ[ℂ] ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun φ := starRingEnd ℂ (l (fun x => starRingEnd ℂ (φ x)))
  map_add' φ ψ := by
    have h : (fun x => starRingEnd ℂ ((φ + ψ) x)) = (fun x => starRingEnd ℂ (φ x)) + fun x => starRingEnd ℂ (ψ x) :=
      funext fun x => map_add _ _ _
    rw [h, map_add, map_add]
  map_smul' c φ := by
    have h : (fun x => starRingEnd ℂ ((c • φ) x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (φ x) :=
      funext fun x => by simp
    rw [h, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply, smul_eq_mul]

variable {F : Type} [Field F] [NumberField F]

theorem admissible_of_slice_zero {κ κ' : Type} [Fintype κ] [Fintype κ'] (p₀ : κ → AF F) :
    ∀ l ∈ (adeleClass F).adm κ',
      l ∘ₗ LinearMap.funLeft ℂ ℂ (fun t : κ' → AF F => Sum.elim p₀ t) ∈ (adeleClass F).adm (κ ⊕ κ') := by
  classical
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  intro l hl g hg
  obtain ⟨Tsl, hTsl⟩ := GlobalTheory.ThK.Adapt.exists_slice (Equiv.refl (κ ⊕ κ'))
    (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (p₀ k).1)
  obtain ⟨T, hT⟩ := hl _ (GlobalTheory.ThK.Adapt.slice_mem_SB (Equiv.refl (κ ⊕ κ')) (fun k => (p₀ k).2) hg)
  refine ⟨T.comp Tsl, fun f => ?_⟩
  rw [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hT]
  congr 1
  funext t
  simp only [LinearMap.funLeft_apply, Function.comp_apply, pureA, hTsl]
  congr 2 <;> funext k <;> rcases k with k | k <;> rfl

theorem adm_of_box {κ κ₁ κ' κ₁' : Type} [Fintype κ] [Fintype κ₁] [Fintype κ'] [Fintype κ₁']
    (Ed : ((κ ⊕ κ' → AF F) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁' → AF F) → ℂ)) (e₁ : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
    (e₂ : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ₁' → AF F) → ℂ))
    (hadm : ∀ l ∈ (adeleClass F).adm (κ₁ ⊕ κ₁'), l ∘ₗ Ed ∈ (adeleClass F).adm (κ ⊕ κ'))
    (hbox : ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', Ed (boxFun φ₁ φ₂) = boxFun (e₁ φ₁) (e₂ φ₂))
    (hne : ∃ φ ∈ schA F κ, e₁ φ ≠ 0) :
    ∀ l ∈ (adeleClass F).adm κ₁', l ∘ₗ e₂ ∈ (adeleClass F).adm κ' := by
  classical
  obtain ⟨f₁, g₁, hg₁, hne₁⟩ : ∃ (f₁ : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
      (g₁ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g₁ ∈ SB _ ∧ e₁ (pureA F f₁ g₁) ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨φ, hφ, hφne⟩ := hne
    have hz : ∀ φ ∈ schA F κ, e₁ φ = 0 := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem x hx => obtain ⟨f, g, hg, rfl⟩ := hx; exact hc f g hg
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
    exact hφne (hz φ hφ)
  obtain ⟨t₀, ht₀⟩ : ∃ t, e₁ (pureA F f₁ g₁) t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne₁ (funext h)
  obtain ⟨Bx, hBx⟩ := GlobalTheory.T.schwartz_tensor_left_factor (mixedEmbedding.mixedSpace F) κ κ' f₁
  intro l hl g hg
  obtain ⟨T, hT⟩ := hadm _ (admissible_of_slice_zero t₀ l hl) _ (GlobalTheory.SchwartzBox.sb_box hg₁ hg)
  refine ⟨(e₁ (pureA F f₁ g₁) t₀)⁻¹ • T.comp Bx, fun f => ?_⟩
  have hkey : pureA F (Bx f) (fun z => g₁ (z ∘ Sum.inl) * g (z ∘ Sum.inr)) =
      boxFun (pureA F f₁ g₁) (pureA F f g) := by
    funext x
    simp only [pureA, boxFun, hBx, Function.comp_def]
    ring
  have h1 := hT (Bx f)
  rw [LinearMap.comp_apply, hkey, hbox _ (Submodule.subset_span ⟨f₁, g₁, hg₁, rfl⟩) _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)] at h1
  have h2 : LinearMap.funLeft ℂ ℂ (fun t : κ₁' → AF F => Sum.elim t₀ t)
      (boxFun (e₁ (pureA F f₁ g₁)) (e₂ (pureA F f g))) = e₁ (pureA F f₁ g₁) t₀ • e₂ (pureA F f g) := by
    funext t; simp [boxFun]
  rw [LinearMap.comp_apply, h2, map_smul, smul_eq_mul] at h1
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ← h1, smul_eq_mul, LinearMap.comp_apply,
    inv_mul_cancel_left₀ ht₀]

end admitted

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W₁.J) M₁.co dd₁ →
      ∀ (Ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ))
        (e₂ : Fn F n d →ₗ[ℂ] Fn F n d₁),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (Ed Φ)) →
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = Ed Φ ∧
          Ed (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = Ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁), l ∘ₗ Ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), Ed (boxFun Φ₁ Φ₂) = boxFun (e Φ₁) (e₂ Φ₂)) →
        (∀ Φ ∈ schA F (Fin n × Fin d), e₂ Φ ∈ schA F (Fin n × Fin d₁)) →
        (∃ Φ ∈ schA F (Fin n × Fin d), e₂ Φ ≠ 0) →
        ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F (Fin n × Fin d), e₂ (fun x => star (Φ x)) = c • fun x => star (e Φ x) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hpair₁ e he hne dd dd₁
    hdd hdd₁ Ed e₂ hEdS hheis hinv hadm hbox he₂S hne₂
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hpair.base.std
  have conjMem : ∀ {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ :=
    fun Φ hΦ => GlobalTheory.SchAConj.star_mem_schA F _ Φ hΦ
  have rhoInvMem : ∀ (w : Matrix (Fin n) (Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d),
      M.co.rho B.ψ⁻¹ w Φ ∈ schA F (Fin n × Fin d) := by
    intro w Φ hΦ
    have h1 : M.co.rho B.ψ⁻¹ w Φ = fun x => starRingEnd ℂ (M.co.rho B.ψ w (fun y => starRingEnd ℂ (Φ y)) x) :=
      funext fun x => by simp only [Darboux.rho, conj_schr' B.ψ hψ, Complex.conj_conj]
    rw [h1]
    exact conjMem _ (GlobalTheory.HeisSchA.schr_mem_schA B.ψ hpair.base.std _ _ (conjMem Φ hΦ))
  obtain ⟨φ₁, hφ₁, hφ₁ne⟩ := hne
  obtain ⟨t₀, ht₀⟩ : ∃ t, e φ₁ t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ₁ne (funext h)
  have hone : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [incM, Matrix.map_one _ (map_zero _) (map_one _)]
  have boxMem : ∀ Φ ∈ schA F (Fin n × Fin d), boxFun φ₁ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) :=
    fun Φ hΦ => GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ hφ₁ Φ hΦ
  have heis₂ : ∀ (z : Matrix (Fin n) (Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d),
      e₂ (M.co.rho B.ψ⁻¹ (z * (incM F H'.ι)ᵀ) Φ) = M₁.co.rho B.ψ⁻¹ z (e₂ Φ) := by
    intro z Φ hΦ
    have h1 := hheis (Matrix.fromCols 0 z) (boxFun φ₁ Φ) (boxMem Φ hΦ)
    rw [fromCols_zero_mul_blockDiag_transpose, rho_fromCols_zero_boxFun _ _ _ _ _ _ hdd,
      hbox _ hφ₁ _ (rhoInvMem _ Φ hΦ), hbox _ hφ₁ _ hΦ, rho_fromCols_zero_boxFun _ _ _ _ _ _ hdd₁] at h1
    exact boxFun_cancel t₀ ht₀ h1
  have inv₂ : ∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d),
      e₂ (M.co.rho B.ψ⁻¹ (Matrix.vecMulVec y (incV F H'.x)) Φ) = e₂ Φ := by
    intro y Φ hΦ
    have h1 := (hinv y (boxFun φ₁ Φ) (boxMem Φ hΦ)).2
    rw [rho_fromCols_zero_boxFun _ _ _ _ _ _ hdd, hbox _ hφ₁ _ (rhoInvMem _ Φ hΦ), hbox _ hφ₁ _ hΦ] at h1
    exact boxFun_cancel t₀ ht₀ h1
  have hS1 : ∀ Φ ∈ schA F (Fin n × Fin d), conjLin e₂ Φ ∈ schA F (Fin n × Fin d₁) := fun Φ hΦ =>
    conjMem _ (he₂S _ (conjMem Φ hΦ))
  have hS2 : ∀ z : Matrix (Fin n) (Fin d₁) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d),
      conjLin e₂ (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) =
        M₁.co.rho B.ψ z (conjLin e₂ Φ) := by
    intro z Φ hΦ
    rw [hone, Matrix.one_mul]
    funext y
    rw [conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (M.co.rho B.ψ (z * (incM F H'.ι)ᵀ) Φ x)) =
        M.co.rho B.ψ⁻¹ (z * (incM F H'.ι)ᵀ) (fun x => starRingEnd ℂ (Φ x)) :=
      funext fun x => conj_schr' B.ψ hψ _ _ _
    rw [h1, heis₂ z _ (conjMem Φ hΦ)]
    exact conj_schr_inv' B.ψ hψ _ _ _
  have hS3 : ∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), conjLin e₂ (M.co.rho B.ψ u Φ) = conjLin e₂ Φ := by
    rintro u ⟨y, rfl⟩ Φ hΦ
    funext x'
    rw [conjLin_apply, conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (M.co.rho B.ψ (Matrix.vecMulVec y (incV F H'.x)) Φ x)) =
        M.co.rho B.ψ⁻¹ (Matrix.vecMulVec y (incV F H'.x)) (fun x => starRingEnd ℂ (Φ x)) :=
      funext fun x => conj_schr' B.ψ hψ _ _ _
    rw [h1, inv₂ y _ (conjMem Φ hΦ)]
  have hS4 : ∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁), l ∘ₗ conjLin e₂ ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro l hl
    have h1 : conjForm l ∈ (adeleClass F).adm (Fin n × Fin d₁) := GlobalTheory.T.admissible_conj_functional F _ l hl _ fun Φ => rfl
    have h2 := adm_of_box Ed e e₂ hadm hbox ⟨φ₁, hφ₁, hφ₁ne⟩ _ h1
    refine GlobalTheory.T.admissible_conj_functional F _ _ h2 (l ∘ₗ conjLin e₂) fun Φ => ?_
    show l (conjLin e₂ Φ) = starRingEnd ℂ (starRingEnd ℂ (l _))
    rw [Complex.conj_conj]
    rfl
  obtain ⟨c', hc'⟩ := GlobalTheory.T.skew_adapted_plane_pair_converse hKP F E σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH'
    hpair₁ e he (conjLin e₂) hS1 hS2 hS3 hS4
  have hrel : ∀ Φ ∈ schA F (Fin n × Fin d), e₂ (fun x => star (Φ x)) = starRingEnd ℂ c' • fun x => star (e Φ x) := by
    intro Φ hΦ
    funext y
    have h1 := congrFun (hc' Φ hΦ) y
    rw [conjLin_apply, Pi.smul_apply, smul_eq_mul] at h1
    have h2 := congrArg (starRingEnd ℂ) h1
    rw [Complex.conj_conj, map_mul] at h2
    simpa using h2
  refine ⟨starRingEnd ℂ c', fun hc => ?_, hrel⟩
  obtain ⟨Φ', hΦ', hne'⟩ := hne₂
  apply hne'
  have h3 := hrel _ (conjMem Φ' hΦ')
  rw [hc, zero_smul] at h3
  simpa using h3

end GlobalTheory.ConjRelDbl
