import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierPreservesSchwartzL2Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialRightPreservesL2NormStatement

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval GlobalTheory.WeilTr

noncomputable section

namespace GlobalTheory.DblTr

section Blocks

variable {A : Type} {κ κ₁ κ' κ₁' : Type}

def partLe (U : ((κ → A) → ℂ) ≃ₗ[ℂ] ((κ₁ → A) → ℂ)) : ((κ ⊕ κ' → A) → ℂ) ≃ₗ[ℂ] ((κ₁ ⊕ κ' → A) → ℂ) :=
  { partLₗ U.toLinearMap with
    invFun := partL U.symm
    left_inv := fun Φ => by
      show partL U.symm (partL U Φ) = Φ
      rw [partL_partL]
      simp only [LinearEquiv.symm_apply_apply]
      exact partL_id Φ
    right_inv := fun Φ => by
      show partL U (partL U.symm Φ) = Φ
      rw [partL_partL]
      simp only [LinearEquiv.apply_symm_apply]
      exact partL_id Φ }

def partRe (U : ((κ' → A) → ℂ) ≃ₗ[ℂ] ((κ₁' → A) → ℂ)) : ((κ ⊕ κ' → A) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ₁' → A) → ℂ) :=
  { partRₗ U.toLinearMap with
    invFun := partR U.symm
    left_inv := fun Φ => by
      show partR U.symm (partR U Φ) = Φ
      rw [partR_partR]
      simp only [LinearEquiv.symm_apply_apply]
      exact partR_id Φ
    right_inv := fun Φ => by
      show partR U (partR U.symm Φ) = Φ
      rw [partR_partR]
      simp only [LinearEquiv.apply_symm_apply]
      exact partR_id Φ }

end Blocks

def conjE {X Y : Type} (U : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ) :=
  { conjLin U.toLinearMap with
    invFun := conjLin U.symm.toLinearMap
    left_inv := fun φ => by
      funext x
      simp [conjLin_apply]
    right_inv := fun φ => by
      funext x
      simp [conjLin_apply] }

theorem conjE_apply {X Y : Type} (U : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) : conjE U φ = conjLin U.toLinearMap φ := rfl

end GlobalTheory.DblTr

namespace GlobalTheory.DblTr

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem partL_eq_of_eqOn {κ κ₁ κ' : Type} [Fintype κ] [Fintype κ'] {T e : ((κ → AF F) → ℂ) → (κ₁ → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, T Φ = e Φ) {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ')) :
    partL T Φ = partL e Φ :=
  partL_congr fun b => h _ (sliceL_mem hΦ b)

theorem partR_eq_of_eqOn {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] {T e : ((κ' → AF F) → ℂ) → (κ₁' → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ', T Φ = e Φ) {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ')) :
    partR T Φ = partR e Φ :=
  partR_congr fun a => h _ (sliceR_mem hΦ a)

theorem conjLin_eq_of_eqOn {κ κ₁ : Type} [Fintype κ] {T e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, T Φ = e Φ) : ∀ Φ ∈ schA F κ, conjLin T Φ = conjLin e Φ := fun Φ hΦ => by
  funext y
  rw [conjLin_apply, conjLin_apply, h _ (GlobalTheory.ConjSch.conj_mem_schA Φ hΦ)]

theorem adm_congr {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ)
    (hl : l' ∈ (adeleClass F).adm κ) : l ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨T, fun f => by rw [h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), hT]⟩

theorem dbl_eq {κ : Type} [Fintype κ] (U : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (u : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (hu : IsLocOp u) (hUu : ∀ Φ ∈ schA F κ, U Φ = u Φ)
    {Φ : (κ ⊕ κ → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    partR (conjLin U.toLinearMap) (partL U Φ) = partR (conjLin u) (partL u Φ) ∧
      partR (conjLin u) (partL u Φ) ∈ schA F (κ ⊕ κ) := by
  have h1 : partL U Φ = partL u Φ := partL_eq_of_eqOn hUu hΦ
  have h2 : partL u Φ ∈ schA F (κ ⊕ κ) := partL_mem u hu Φ hΦ
  refine ⟨?_, partR_mem (conjLin u) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin u hu) _ h2⟩
  rw [h1]
  exact partR_eq_of_eqOn (conjLin_eq_of_eqOn (T := U.toLinearMap) hUu) h2

theorem dbl_eq' {κ : Type} [Fintype κ] (U : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (u : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (hu : IsLocOp u) (hUu : ∀ Φ ∈ schA F κ, U Φ = u Φ)
    {Φ : (κ ⊕ κ → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    partL U (partR (conjLin U.toLinearMap) Φ) = partL u (partR (conjLin u) Φ) ∧
      partL u (partR (conjLin u) Φ) ∈ schA F (κ ⊕ κ) := by
  have h1 : partR (conjLin U.toLinearMap) Φ = partR (conjLin u) Φ :=
    partR_eq_of_eqOn (conjLin_eq_of_eqOn (T := U.toLinearMap) hUu) hΦ
  have h2 : partR (conjLin u) Φ ∈ schA F (κ ⊕ κ) :=
    partR_mem (conjLin u) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin u hu) Φ hΦ
  refine ⟨?_, partL_mem u hu _ h2⟩
  rw [h1]
  exact partL_eq_of_eqOn hUu h2

end Gen

end GlobalTheory.DblTr

namespace GlobalTheory.DblTr

section Main

variable {F : Type} [Field F] [NumberField F]

theorem hasDbl_of_loc {E' : Type} [CommRing E'] [Algebra (AF F) E'] (c : E' →ₐ[AF F] E') {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E') (JA : Matrix α α E') (JB : Matrix β β E') {κ : Type}
    [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) (d d₁ : Darboux (symp c ξ JA JB) κ)
    (T : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ)) (e e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (hL : IsLocOp e) (hL' : IsLocOp e') (hTe : ∀ Φ ∈ schA F κ, T Φ = e Φ)
    (hTe' : ∀ Φ ∈ schA F κ, T.symm Φ = e' Φ) (hmem : ∀ Φ, Φ ∈ schA F κ ↔ T Φ ∈ schA F κ)
    (Heisenberg₂ : ∀ w, ∀ Φ ∈ schA F κ, T (d.rho ψ w Φ) = d₁.rho ψ w (T Φ))
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F κ, ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) :
    HasDbl c (adeleClass F) ψ ξ JA JB d d₁ T := by
  intro dd hdd
  have hconj : ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ := fun Φ hΦ =>
    GlobalTheory.ConjSch.conj_mem_schA Φ hΦ

  have hSmem : ∀ φ, φ ∈ schA F κ ↔ conjE T φ ∈ schA F κ := fun φ => by
    constructor
    · intro hφ
      have := hconj _ ((hmem _).1 (hconj φ hφ))
      exact this
    · intro hφ
      have h1 : (fun x => starRingEnd ℂ (conjE T φ x)) = T (fun x => starRingEnd ℂ (φ x)) := by
        funext x; simp [conjE_apply, conjLin_apply]
      have h2 := hconj _ hφ
      rw [h1, ← hmem] at h2
      have h3 := hconj _ h2
      simpa using h3

  have hLmem : ∀ Φ ∈ schA F (κ ⊕ κ), partL T Φ ∈ schA F (κ ⊕ κ) := fun Φ hΦ => by
    rw [partL_eq_of_eqOn hTe hΦ]; exact partL_mem e hL Φ hΦ
  have hRmem : ∀ Φ ∈ schA F (κ ⊕ κ), partR (conjE T) Φ ∈ schA F (κ ⊕ κ) := fun Φ hΦ => by
    have h := partR_eq_of_eqOn (κ := κ) (conjLin_eq_of_eqOn (T := T.toLinearMap) hTe) hΦ
    rw [show partR (conjE T) Φ = partR (conjLin T.toLinearMap) Φ from rfl, h]
    exact partR_mem (conjLin e) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e hL) Φ hΦ

  have heis₂ : ∀ w, ∀ φ ∈ schA F κ, conjE T (d.rho ψ⁻¹ w φ) = d₁.rho ψ⁻¹ w (conjE T φ) := fun w φ hφ => by
    funext y
    rw [conjE_apply, conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (d.rho ψ⁻¹ w φ x)) = d.rho ψ w (fun x => starRingEnd ℂ (φ x)) :=
      funext fun x => conj_schr_inv ψ hψ _ _ _
    rw [LinearEquiv.coe_coe, h1, Heisenberg₂ w _ (hconj φ hφ)]
    exact conj_schr ψ hψ _ _ _

  have hunitS : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F κ, ∫⁻ x, ‖conjE T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := fun μ hμ => by
    obtain ⟨C, hC⟩ := hunit μ hμ
    refine ⟨C, fun Φ hΦ => ?_⟩
    have h1 := hC _ (hconj Φ hΦ)
    have hce : ∀ z : ℂ, ‖starRingEnd ℂ z‖ₑ = ‖z‖ₑ := fun z => by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      congr 1
      ext
      simp
    simp only [conjE_apply, conjLin_apply, LinearEquiv.coe_coe, hce] at h1 ⊢
    exact h1
  set Td : ((κ ⊕ κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → AF F) → ℂ) := (partLe (κ' := κ) T).trans (partRe (κ := κ) (conjE T))
    with hTd
  have hTd_apply : ∀ Φ, Td Φ = partR (conjE T) (partL T Φ) := fun Φ => rfl
  have hTd_symm : ∀ Φ, Td.symm Φ = partL T.symm (partR (conjE T).symm Φ) := fun Φ => rfl
  have hTeq : ∀ Φ ∈ schA F (κ ⊕ κ), Td Φ = partR (conjLin e) (partL e Φ) ∧ partR (conjLin e) (partL e Φ) ∈ schA F (κ ⊕ κ) :=
    fun Φ hΦ => dbl_eq T e hL hTe hΦ
  have hTeq' : ∀ Φ ∈ schA F (κ ⊕ κ), Td.symm Φ = partL e' (partR (conjLin e') Φ) ∧
      partL e' (partR (conjLin e') Φ) ∈ schA F (κ ⊕ κ) :=
    fun Φ hΦ => dbl_eq' T.symm e' hL' hTe' hΦ
  refine ⟨GlobalTheory.DblSchr.dblD c d₁, Td, conjE T, GlobalTheory.DblSchr.isDblCoord_dblD c d₁, ⟨fun Φ => ?_, fun w Φ hΦ => ?_,
    fun l => ?_, fun μ hμ => ?_⟩, hSmem, fun φ₁ _ φ₂ _ => ?_⟩
  · constructor
    · intro hΦ
      rw [(hTeq Φ hΦ).1]; exact (hTeq Φ hΦ).2
    · intro hΦ
      have := (hTeq' _ hΦ)
      rw [LinearEquiv.symm_apply_apply] at this
      rw [this.1]; exact this.2
  · rw [← Matrix.fromCols_toCols w, rho_dbl c ξ JA JB d dd hdd, rho_dbl c ξ JA JB d₁ _ (GlobalTheory.DblSchr.isDblCoord_dblD c d₁),
      hTd_apply, hTd_apply]
    have hc1 : ∀ Ψ : (κ ⊕ κ → AF F) → ℂ, partL T (partR (d.rho ψ⁻¹ w.toCols₂) Ψ) =
        partR (d.rho ψ⁻¹ w.toCols₂) (partL T Ψ) := fun Ψ => partL_partR_rho T.toLinearMap d ψ⁻¹ _ Ψ
    have hc2 : ∀ Ψ : (κ ⊕ κ → AF F) → ℂ, partR (conjE T) (partL (d₁.rho ψ w.toCols₁) Ψ) =
        partL (d₁.rho ψ w.toCols₁) (partR (conjE T) Ψ) := fun Ψ => partR_partL_rho (conjE T).toLinearMap d₁ ψ _ Ψ
    rw [partL_intertwine T (d.rho ψ w.toCols₁) (d₁.rho ψ w.toCols₁) T _ (fun φ hφ => Heisenberg₂ _ φ hφ)
        (fun b => by rw [sliceL_partR_rho]; exact Submodule.smul_mem _ _ (sliceL_mem hΦ _)),
      hc1, hc2,
      partR_intertwine (conjE T) (d.rho ψ⁻¹ w.toCols₂) (d₁.rho ψ⁻¹ w.toCols₂) (conjE T) _ (fun φ hφ => heis₂ _ φ hφ)
        (fun a => sliceR_mem (hLmem Φ hΦ) a)]
  · constructor
    · intro hl
      refine adm_congr (l' := (l ∘ₗ partRₗ (conjLin e)) ∘ₗ partLₗ e) (fun Φ hΦ => ?_)
        (partL_adm e hL _ (partR_adm (conjLin e) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e hL) l hl))
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, partLₗ_apply, partRₗ_apply]
      rw [(hTeq Φ hΦ).1]
    · intro hl
      refine adm_congr (l' := ((l ∘ₗ Td.toLinearMap) ∘ₗ partLₗ e') ∘ₗ partRₗ (conjLin e')) (fun Φ hΦ => ?_)
        (partR_adm (conjLin e') (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e' hL') _ (partL_adm e' hL' _ hl))
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, partLₗ_apply, partRₗ_apply]
      rw [← (hTeq' Φ hΦ).1, LinearEquiv.apply_symm_apply]
  · obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.partial_fourier_preserves_schwartz_L2 T.toLinearMap hunit hLmem μ hμ
    obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.partial_right_preserves_l2_norm (κ := κ) (conjE T).toLinearMap hunitS hRmem μ hμ
    refine ⟨C₂ * C₁, fun φ hφ => ?_⟩
    rw [hTd_apply]
    have h2 := hC₂ _ (hLmem φ hφ)
    have h1 := hC₁ φ hφ
    simp only [LinearEquiv.coe_coe] at h1 h2
    rw [h2, h1, mul_assoc]
  · funext y
    rw [hTd_apply]
    simp only [partR, partL, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]
    have h1 : (fun x => T (fun x' => φ₁ x' * φ₂ x) (y ∘ Sum.inl)) = T φ₁ (y ∘ Sum.inl) • φ₂ := funext fun x => by
      rw [show (fun x' => φ₁ x' * φ₂ x) = φ₂ x • φ₁ from funext fun x' => by simp [mul_comm], map_smul]
      simp [mul_comm]
    rw [h1, map_smul]
    rfl

end Main

end GlobalTheory.DblTr
