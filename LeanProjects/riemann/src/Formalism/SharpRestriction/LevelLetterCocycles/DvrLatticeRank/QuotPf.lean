import Formalism.SharpRestriction.LevelLetterCocycles.MixedPositionHypothesis
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem qpf_filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  have h : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := fun x hx => PD.Fil_anti a hx
  intro x hx
  rw [FilV, LinearMap.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion h) y, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp, LinearMap.id_comp, Submodule.subtype_comp_inclusion]

theorem qpf_fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := by
  unfold FildR
  exact inf_le_inf_left _ (qpf_filV_succ_le PD a)

theorem qpf_isJumpV_iff_pos (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ) :
    IsJumpV PD ρ τ a ↔ 0 < multV PD ρ τ a := by
  have hle := qpf_fildR_succ_le PD ρ τ a
  haveI := hfin
  haveI : Module.Finite LL ↥(FildR PD ρ τ a) :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ))
      (Submodule.inclusion_injective _)
  unfold IsJumpV multV
  constructor
  · intro hne
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
    omega
  · intro hpos heq
    rw [heq] at hpos
    simp at hpos

theorem qpf_multV_nonneg (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ) :
    0 ≤ multV PD ρ τ a := by
  by_cases h : FildR PD ρ τ (a + 1) = FildR PD ρ τ a
  · unfold multV
    rw [h]
    simp
  · exact le_of_lt ((qpf_isJumpV_iff_pos PD ρ τ hfin a).1 h)

end Gen

theorem quotient_jumps_subset (D : D7) (h8 : adm8 D) (h11 : adm11 D) : quotR D := by
  unfold quotR
  intro l _ hl2 K LL hG
  unfold quotA
  intro T₁ T₂ F hc1 hc2 hon τ X hJ a ha
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hden : Formalism.MainNotions.LiftingTheory.lker_Den ↥LL.1 ↥(OL LL) := by
    intro c
    have hint : IsIntegral ℚ_[l] c := Algebra.IsIntegral.isIntegral c
    have halg : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 hint.isAlgebraic
    have hinj : Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
      exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    obtain ⟨y, hy, hyc⟩ : ∃ y ≠ (0 : ℤ_[l]), IsIntegral ℤ_[l] (y • c) := by
      exact IsAlgebraic.exists_integral_multiple halg
    refine ⟨algebraMap ℤ_[l] ↥(OL LL) y, ?_, ⟨y • c, hyc⟩, ?_⟩
    · rw [← IsScalarTower.algebraMap_apply]
      exact fun h => hy (hinj (h.trans (map_zero _).symm))
    · rw [← IsScalarTower.algebraMap_apply]
      change _ = y • c
      rw [Algebra.smul_def]
  have hses : IsSESLat (Qp := ℚ_[l]) (Formalism.MainNotions.LiftingTheory.lker_ι F hon hden) F := by
    refine ⟨(LinearMap.ker F.f).injective_subtype, Formalism.MainNotions.LiftingTheory.lker_surj F hon, hon,
      fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, ?_⟩, fun y hy => hy⟩
    rintro ⟨y, rfl⟩
    exact LinearMap.mem_ker.1 y.2
  obtain ⟨-, -, hmult⟩ := h11 l K LL _ T₁ T₂ (Formalism.MainNotions.LiftingTheory.lker_ι F hon hden) F hses hc1
  apply hJ
  rw [qpf_isJumpV_iff_pos _ _ τ ((h8 l K LL T₂).2 τ).1] at ha
  rw [qpf_isJumpV_iff_pos _ _ τ ((h8 l K LL T₁).2 τ).1, hmult τ a]
  have h0 := qpf_multV_nonneg _ _ τ ((h8 l K LL (Formalism.MainNotions.LiftingTheory.lker_T₀ F hon hden)).2 τ).1 a
  omega

end Formalism.MainNotions.N.Ln34

end
