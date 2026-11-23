import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorLocalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorsProductCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorsProductExtendStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.LocOpInv

theorem pure_mem {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in cofinite, φ v = stdInd F κ v) : pure f φ ∈ schA F κ :=
  GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd

theorem stdInd_mem_SB_ne {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F) :
    stdInd F κ v ∈ SB (κ → Fv F v) ∧ stdInd F κ v ≠ 0 := by
  refine ⟨GlobalTheory.StdVacuum.indicator_mem_SB v, fun h => ?_⟩
  have h0 := congrFun h 0
  rw [stdInd, Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    from fun i => zero_mem _)] at h0
  exact one_ne_zero h0

theorem isLocOp_inv : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsLocOp e →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∃ e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ), IsLocOp e' ∧ ∀ Φ ∈ schA F κ, e' (e Φ) = Φ := by
  classical
  intro F _ _ κ _ e he hbij
  obtain ⟨ei, ev, hSB, hstd, hloc⟩ := he
  have hne : ∀ v, ev v (stdInd F κ v) ≠ 0 := fun v h =>
    (stdInd_mem_SB_ne v).2 (GlobalTheory.T.restricted_tensor_local_operators e ei ev hSB hstd hloc hbij.injOn v _ (stdInd_mem_SB_ne v).1 h)
  obtain ⟨S, hS⟩ := GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei (GlobalTheory.T.bijective_infinite_part_of_restricted_product e ei ev hSB hstd hloc hbij hne)

  have hbv : ∀ v, Function.Bijective ((ev v).restrict (p := SB (κ → Fv F v)) (q := SB (κ → Fv F v)) (hSB v)) := by
    intro v
    refine ⟨?_, ?_⟩
    · refine (injective_iff_map_eq_zero _).2 fun ψ hψ => ?_
      exact Subtype.ext (GlobalTheory.T.restricted_tensor_local_operators e ei ev hSB hstd hloc hbij.injOn v ψ.1 ψ.2 (congrArg Subtype.val hψ))
    · intro χ
      obtain ⟨ψ, hψ, h⟩ := GlobalTheory.T.local_operators_product_compatible e ei ev hSB hstd hloc hbij.surjOn hne v χ.1 χ.2
      exact ⟨⟨ψ, hψ⟩, Subtype.ext h⟩
  let Lv : ∀ v, SB (κ → Fv F v) ≃ₗ[ℂ] SB (κ → Fv F v) := fun v => LinearEquiv.ofBijective _ (hbv v)
  have hCv : ∀ v, ∃ C : Submodule ℂ ((κ → Fv F v) → ℂ), IsCompl (SB (κ → Fv F v)) C := fun v =>
    Submodule.exists_isCompl _
  choose Cv hCv using hCv
  let ev' : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := fun v =>
    (SB (κ → Fv F v)).subtype ∘ₗ ((Lv v).symm : SB (κ → Fv F v) →ₗ[ℂ] SB (κ → Fv F v)) ∘ₗ
      Submodule.linearProjOfIsCompl _ _ (hCv v)
  have hev'1 : ∀ v, ∀ ψ (hψ : ψ ∈ SB (κ → Fv F v)), ev' v ψ = ((Lv v).symm ⟨ψ, hψ⟩ : SB _) := by
    intro v ψ hψ
    simp only [ev', LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    have hp : Submodule.linearProjOfIsCompl _ _ (hCv v) ψ = ⟨ψ, hψ⟩ :=
      Submodule.linearProjOfIsCompl_apply_left (hCv v) ⟨ψ, hψ⟩
    rw [hp]
  have hev'SB : ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev' v ψ ∈ SB (κ → Fv F v) := fun v ψ hψ => by
    rw [hev'1 v ψ hψ]; exact Subtype.property _
  have hevev' : ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v (ev' v ψ) = ψ := by
    intro v ψ hψ
    rw [hev'1 v ψ hψ]
    have := congrArg Subtype.val ((Lv v).apply_symm_apply ⟨ψ, hψ⟩)
    exact this
  have hev'std : ∀ᶠ v in cofinite, ev' v (stdInd F κ v) = stdInd F κ v := by
    filter_upwards [hstd] with v hv
    have h1 := (stdInd_mem_SB_ne (κ := κ) v).1
    rw [hev'1 v _ h1]
    have : (Lv v) ⟨stdInd F κ v, h1⟩ = ⟨stdInd F κ v, h1⟩ := Subtype.ext hv
    rw [← this, LinearEquiv.symm_apply_apply]

  let Le : schA F κ ≃ₗ[ℂ] schA F κ := LinearEquiv.ofBijective ((e.restrict (p := schA F κ) (q := schA F κ)
    fun Φ hΦ => hbij.mapsTo hΦ)) ⟨fun a b h => Subtype.ext (hbij.injOn a.2 b.2 (congrArg Subtype.val h)), fun b => by
      obtain ⟨a, ha, h⟩ := hbij.surjOn b.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (schA F κ)
  let e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    (schA F κ).subtype ∘ₗ (Le.symm : schA F κ →ₗ[ℂ] schA F κ) ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have he'e : ∀ Φ ∈ schA F κ, e' (e Φ) = Φ := by
    intro Φ hΦ
    have h1 : e Φ ∈ schA F κ := hbij.mapsTo hΦ
    simp only [e', LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    have hp : Submodule.linearProjOfIsCompl _ _ hC (e Φ) = ⟨e Φ, h1⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨e Φ, h1⟩
    rw [hp]
    have : Le ⟨Φ, hΦ⟩ = ⟨e Φ, h1⟩ := rfl
    rw [← this, LinearEquiv.symm_apply_apply]
  refine ⟨e', ⟨S, ev', hev'SB, hev'std, fun f φ hφ hφs => ?_⟩, he'e⟩
  have hφ' : ∀ v, ev' v (φ v) ∈ SB (κ → Fv F v) := fun v => hev'SB v _ (hφ v)
  have hφ's : ∀ᶠ v in cofinite, ev' v (φ v) = stdInd F κ v := by
    filter_upwards [hφs, hev'std] with v h1 h2
    rw [h1, h2]
  have hΨ : pure (S f) (fun v => ev' v (φ v)) ∈ schA F κ := pure_mem (S f) _ hφ' hφ's
  have hE : e (pure (S f) fun v => ev' v (φ v)) = pure f φ := by
    rw [hloc _ _ hφ' hφ's, hS]
    congr 1
    funext v
    exact hevev' v _ (hφ v)
  rw [← hE, he'e _ hΨ]

end GlobalTheory.LocOpInv

end
