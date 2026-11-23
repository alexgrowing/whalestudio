import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

section General

variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] [TopologicalSpace LL]
  [IsTopologicalRing LL]
  {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousConstSMul LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [TopologicalSpace V'] [ContinuousAdd V']
  [ContinuousConstSMul LL V']

theorem cupAnti_cob_of_flip (χ : G →* LLˣ) (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (m : V →ₗ[LL] V' →ₗ[LL] LL) (hm : Continuous fun p : V × V' => m p.1 p.2)
    (hχ : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : LLˣ) : LL) * m x y)
    {a : G → V} (ha : a ∈ continuousCocycles ρ) {b : G → V'} (hb : b ∈ continuousCocycles ρ')
    (h : ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ m.flip b a) :
    ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ' m a b := by
  obtain ⟨f, hf, hfe⟩ := h
  obtain ⟨hac, ha⟩ := ha
  obtain ⟨hbc, hb⟩ := hb
  refine ⟨fun g => -(m (a g) (b g)) - f g, ((hm.comp (hac.prodMk hbc)).neg).sub hf, ?_⟩
  funext x
  obtain ⟨g, h⟩ := x
  have h1 := congrFun hfe (g, h)
  have h2 := hχ g (a h) (b h)
  simp only [ReciprocityTheory.Def.d1, charRep, cupL, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    ha, hb, map_add, LinearMap.add_apply] at h1 ⊢
  linear_combination -h1 + h2

theorem cupAnti_cob_of_left (χ : G →* LLˣ) (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (m : V →ₗ[LL] V' →ₗ[LL] LL) (hm : Continuous fun p : V × V' => m p.1 p.2)
    (hχ : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : LLˣ) : LL) * m x y)
    {a : G → V} (ha : a ∈ Formalism.WeaklyAdmissibleFiltrations.B1 ρ) {b : G → V'} (hb : b ∈ continuousCocycles ρ') :
    ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ' m a b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨hbc, hb⟩ := hb
  refine ⟨fun g => m x (b g), hm.comp (continuous_const.prodMk hbc), ?_⟩
  funext y
  obtain ⟨g, h⟩ := y
  have h2 := hχ g x (b h)
  simp only [ReciprocityTheory.Def.d1, charRep, cupL, cob, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, LinearMap.pi_apply,
    hb, map_add, map_sub, LinearMap.sub_apply]
  linear_combination -h2

end General

theorem cupL_anticomm_cobL : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, (CobL (P.PD K) (cupL A'.ρ m a b) ↔ CobL (P.PD K) (cupL A.ρ m.flip b a)) ∧ (a ∈ B1 A.ρ ∨ b ∈ B1 A'.ρ → CobL (P.PD K) (cupL A'.ρ m a b)) := by
  intro l _ P K LL _ _ _ O _ _ hO A A' m hm a ha b hb
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  have hc : Continuous fun p : A.V × A'.V => m p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left m
  have hc' : Continuous fun p : A'.V × A.V => m.flip p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left m.flip
  have hχ := hm.1
  have hχ' : ∀ g x y, m.flip (A'.ρ g x) (A.ρ g y) =
      ((cycLL (P.PD K) LL g : LLˣ) : LL) * m.flip x y := fun g x y => hχ g y x
  refine ⟨⟨fun h => cupAnti_cob_of_flip _ A'.ρ A.ρ m.flip hc' hχ' hb ha h,
    fun h => cupAnti_cob_of_flip _ A.ρ A'.ρ m hc hχ ha hb h⟩, ?_⟩
  rintro (h | h)
  · exact cupAnti_cob_of_left _ A.ρ A'.ρ m hc hχ h hb
  · exact cupAnti_cob_of_flip _ A.ρ A'.ρ m hc hχ ha hb
      (cupAnti_cob_of_left _ A'.ρ A.ρ m.flip hc' hχ' h ha)

end GlobalTheory
