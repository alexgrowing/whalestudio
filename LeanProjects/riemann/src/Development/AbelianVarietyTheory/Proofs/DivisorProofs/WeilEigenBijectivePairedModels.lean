import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapPartRightEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameConjMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectivePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierRightIsometryL2Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierLeftIsometryL2Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationAutomorphismCommutesSchwartzStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DblGoodInt

section Coord

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
  {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}

theorem symp_fromCols {d : Darboux (symp c ξ JA JB) κ} {dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)}
    (h : IsDblCoord c ξ JA JB d dd) (w₁ w₂ w₁' w₂' : Matrix α β E) :
    symp c ξ JA (dbl JB) (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁' w₂') =
      symp c ξ JA JB w₁ w₁' - symp c ξ JA JB w₂ w₂' := by
  rw [dd.form, h, h, d.form, d.form]
  simp only [GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg]
  ring

def dblEquiv (d₁ : Darboux (symp c ξ JA JB) κ) : Matrix α (β ⊕ β) E ≃ₗ[R] (κ ⊕ κ → R) × (κ ⊕ κ → R) where
  toFun z := (Sum.elim (d₁.e z.toCols₁).1 (d₁.e z.toCols₂).1, Sum.elim (d₁.e z.toCols₁).2 (-(d₁.e z.toCols₂).2))
  invFun p := Matrix.fromCols (d₁.e.symm (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl)) (d₁.e.symm (p.1 ∘ Sum.inr, -(p.2 ∘ Sum.inr)))
  map_add' z z' := by
    have h1 : (z + z').toCols₁ = z.toCols₁ + z'.toCols₁ := by ext; simp [Matrix.toCols₁]
    have h2 : (z + z').toCols₂ = z.toCols₂ + z'.toCols₂ := by ext; simp [Matrix.toCols₂]
    rw [h1, h2, map_add, map_add]
    ext k <;> cases k <;> simp [add_comm]
  map_smul' a z := by
    have h1 : (a • z).toCols₁ = a • z.toCols₁ := by ext; simp [Matrix.toCols₁]
    have h2 : (a • z).toCols₂ = a • z.toCols₂ := by ext; simp [Matrix.toCols₂]
    rw [h1, h2, map_smul, map_smul]
    ext k <;> cases k <;> simp
  left_inv z := by
    simp only
    conv_rhs => rw [← Matrix.fromCols_toCols z]
    congr 1 <;> rw [LinearEquiv.symm_apply_eq] <;> ext <;> simp
  right_inv p := by
    simp only [Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, LinearEquiv.apply_symm_apply]
    ext k <;> cases k <;> simp

def dblOf (d₁ : Darboux (symp c ξ JA JB) κ)
    (hf : ∀ w₁ w₂ w₁' w₂' : Matrix α β E, symp c ξ JA (dbl JB) (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁' w₂') =
      symp c ξ JA JB w₁ w₁' - symp c ξ JA JB w₂ w₂') : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ) where
  e := dblEquiv d₁
  form z z' := by
    rw [← Matrix.fromCols_toCols z, ← Matrix.fromCols_toCols z', hf, d₁.form, d₁.form]
    simp only [dblEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Matrix.toCols₁_fromCols,
      Matrix.toCols₂_fromCols, GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg]
    ring

theorem isDblCoord_dblOf (d₁ : Darboux (symp c ξ JA JB) κ)
    (hf : ∀ w₁ w₂ w₁' w₂' : Matrix α β E, symp c ξ JA (dbl JB) (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁' w₂') =
      symp c ξ JA JB w₁ w₁' - symp c ξ JA JB w₂ w₂') : IsDblCoord c ξ JA JB d₁ (dblOf d₁ hf) := fun w₁ w₂ => by
  simp [dblOf, dblEquiv]

end Coord

section Fun

variable {R : Type}

def conjEquiv {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (X → ℂ) :=
  LinearEquiv.ofLinear (conjMap T.toLinearMap) (conjMap T.symm.toLinearMap)
    (LinearMap.ext fun φ => by simp [conjMap_apply]) (LinearMap.ext fun φ => by simp [conjMap_apply])

def partLEquiv {κ κ' : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partL T.toLinearMap) (partL T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])

def partREquiv {κ κ' : Type} (T : ((κ' → R) → ℂ) ≃ₗ[ℂ] ((κ' → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partR T.toLinearMap) (partR T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])

def dblEquivFun {κ : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) :
    ((κ ⊕ κ → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → R) → ℂ) :=
  (partREquiv (conjEquiv T)).trans (partLEquiv T)

theorem dblEquivFun_coe {κ : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) :
    (dblEquivFun T).toLinearMap = evDbl T.toLinearMap := rfl

theorem dblEquivFun_symm_coe {κ : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) :
    (dblEquivFun T).symm.toLinearMap = partR (conjMap T.symm.toLinearMap) ∘ₗ partL (κ' := κ) T.symm.toLinearMap := rfl

end Fun

section Law

variable {F : Type} [Field F] [NumberField F]

theorem evDbl_schr (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)) (A₁ B₁ A₂ B₂ : κ → AF F) (a₁ b₁ a₂ b₂ : κ₁ → AF F)
    (h1 : ∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a₁, b₁) (T Φ))
    (h2 : ∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a₂, b₂) (T Φ))
    (h3 : ∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) :
    ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
      schr ψ (Sum.elim a₁ a₂, Sum.elim b₁ (-b₂)) (evDbl T φ) := by
  intro φ hφ
  have hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a₂, -b₂) (conjMap T g) := by
    intro g hg
    have hs : star g ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ g hg
    rw [conjMap_apply, conjMap_apply, GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]
    have := GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (a₂, -b₂) (T (star g))
    simpa only [neg_neg] using this
  funext s
  have hΨ := h3 φ hφ
  have hslice := GlobalTheory.DoublingEvLaw.sliceL hΨ (s ∘ Sum.inr + a₂)
  have hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂))
      (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b₂) - ⅟(2 : AF F) * (a₂ ⬝ᵥ b₂)) •
        schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a₂))) := by
    funext x₁
    have e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) =
        ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂)) := by
      funext x₂
      simp only [schr, Pi.smul_apply, smul_eq_mul, GlobalTheory.DoublingEvLaw.elim_dot, Sum.elim_add_add]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [e1, map_smul, hconj _ (GlobalTheory.DoublingEvLaw.sliceR hφ _)]
    simp only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [dotProduct_neg, dotProduct_neg]
    rw [show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]
    congr 2
    ring_nf
  rw [evDbl_apply, hinner, map_smul, h1 _ hslice]
  simp only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, GlobalTheory.DoublingEvLaw.elim_dot, partR_apply, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_neg]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hs : s ⬝ᵥ Sum.elim b₁ (-b₂) = (s ∘ Sum.inl) ⬝ᵥ b₁ - (s ∘ Sum.inr) ⬝ᵥ b₂ := by
    rw [← Sum.elim_comp_inl_inr s, GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr,
      sub_eq_add_neg]
  rw [hs]
  ring

end Law

section Generic

variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra (AF F) E] {c : E →ₐ[AF F] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
  {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}

theorem hasDbl_of (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (d d₁ : Darboux (symp c ξ JA JB) κ)
    (T : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ)) (hT : IsTame F T.toLinearMap)
    (hT' : IsTame F T.symm.toLinearMap) (hheis : ∀ w, ∀ φ ∈ schA F κ, T (d.rho ψ w φ) = d₁.rho ψ w (T φ))
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ k : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = k * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) :
    HasDbl c (adeleClass F) ψ ξ JA JB d d₁ T := by
  intro dd hdd
  have hf := symp_fromCols hdd
  have hR : IsTame F (partR (κ := κ) (conjMap T.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ (GlobalTheory.T.tame_conj_map F κ κ _ hT)
  have hL : IsTame F (partL (κ' := κ) T.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ hT
  have hR' : IsTame F (partR (κ := κ) (conjMap T.symm.toLinearMap)) :=
    GlobalTheory.T.tame_part_right F κ κ κ _ (GlobalTheory.T.tame_conj_map F κ κ _ hT')
  have hL' : IsTame F (partL (κ' := κ) T.symm.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ hT'
  have hTd : IsTame F (dblEquivFun T).toLinearMap := by rw [dblEquivFun_coe]; exact hR.comp hL
  have hTd' : IsTame F (dblEquivFun T).symm.toLinearMap := by rw [dblEquivFun_symm_coe]; exact hL'.comp hR'
  have hconj : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ k : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖conjMap T.toLinearMap φ x‖ₑ ^ 2 ∂μ = k * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
    intro μ hμ
    obtain ⟨k, hk⟩ := hunit μ hμ
    refine ⟨k, fun φ hφ => ?_⟩
    have h := hk (star φ) (GlobalTheory.SchAConj.star_mem_schA F κ φ hφ)
    simp only [conjMap_apply, Pi.star_apply, LinearEquiv.coe_coe, enorm_eq_nnnorm, nnnorm_star] at h ⊢
    exact h
  refine ⟨dblOf d₁ hf, dblEquivFun T, conjEquiv T, isDblCoord_dblOf d₁ hf, ⟨fun φ => ⟨fun h => hTd.mapsTo φ h,
    fun h => ?_⟩, fun w φ hφ => ?_, fun l => ⟨fun hl => hTd.comp_adm hl, fun hl => ?_⟩, fun μ hμ => ?_⟩,
    fun φ => ⟨fun h => ?_, fun h => ?_⟩, fun φ₁ _ φ₂ _ => evDbl_boxFun T.toLinearMap φ₁ φ₂⟩
  · have := hTd'.mapsTo _ h
    exact (by simpa using this : φ ∈ schA F (κ ⊕ κ))
  · obtain ⟨w₁, w₂, rfl⟩ : ∃ w₁ w₂, w = Matrix.fromCols w₁ w₂ := ⟨_, _, (Matrix.fromCols_toCols w).symm⟩
    show evDbl T.toLinearMap (schr ψ (dd.e (Matrix.fromCols w₁ w₂)) φ) =
      schr ψ ((dblOf d₁ hf).e (Matrix.fromCols w₁ w₂)) (evDbl T.toLinearMap φ)
    rw [hdd, isDblCoord_dblOf d₁ hf]
    exact evDbl_schr ψ hψ T.toLinearMap _ _ _ _ _ _ _ _ (fun Φ hΦ => hheis w₁ Φ hΦ) (fun Φ hΦ => hheis w₂ Φ hΦ)
      hR.mapsTo φ hφ
  · have := hTd'.comp_adm hl
    convert this using 1
    ext φ
    simp
  · obtain ⟨k₁, hk₁⟩ := GlobalTheory.T.partial_fourier_right_isometry_l2 F κ κ (conjMap T.toLinearMap) hR.mapsTo hconj μ hμ
    obtain ⟨k₂, hk₂⟩ := GlobalTheory.T.partial_fourier_left_isometry_l2 F κ κ T.toLinearMap hL.mapsTo hunit μ hμ
    refine ⟨k₂ * k₁, fun φ hφ => ?_⟩
    show ∫⁻ x, ‖partL (κ' := κ) T.toLinearMap (partR (κ := κ) (conjMap T.toLinearMap) φ) x‖ₑ ^ 2 ∂μ = _
    rw [hk₂ _ (hR.mapsTo φ hφ), hk₁ φ hφ, mul_assoc]
  · exact GlobalTheory.SchAConj.star_mem_schA F κ _ (hT.mapsTo _ (GlobalTheory.SchAConj.star_mem_schA F κ φ h))
  · have h2 := GlobalTheory.SchAConj.star_mem_schA F κ _ (hT'.mapsTo _ (GlobalTheory.SchAConj.star_mem_schA F κ _ h))
    have e : (conjEquiv T).symm (conjEquiv T φ) = φ := (conjEquiv T).symm_apply_apply φ
    rw [← e]
    exact h2

end Generic

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co M₁.co T := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hTame : IsTame F T.toLinearMap := by
    intro g hg
    obtain ⟨ι, _, P, g', hg', hP⟩ :=
      GlobalTheory.T.evaluation_good_models_intertwine F E σ B n d n d X W X W M M₁ 1 1 _ e hpair.good hM₁ hev g hg
    exact ⟨ι, inferInstance, P, g', hg', fun f => by
      rw [LinearEquiv.coe_coe, hTe _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)]
      exact hP f⟩
  refine hasDbl_of B.ψ (GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std) M.co M₁.co T hTame
    (GlobalTheory.T.evaluation_automorphism_commutes_schwartz F E σ B n d X W M M₁ hpair.good hM₁ e hev hbij T hTe) (fun w Φ hΦ => ?_) (fun μ hμ => ?_)
  · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) := GlobalTheory.T.schroedinger_preserves_adelic_schwartz F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
    have := hev.Heisenberg₂ w Φ hΦ
    rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
    rw [hTe _ hm, hTe _ hΦ, this]
  · obtain ⟨k, hk⟩ := GlobalTheory.T.weil_eigen_bijective_pair F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
    exact ⟨k, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hk Φ hΦ⟩

end GlobalTheory.DblGoodInt

end
