import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem flagiso_reg {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ' : Sp Ω ⟶ X') (e : X' ≅ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ e.hom) ⤳ e.hom q.1) : regAt ξ' q = regAt (ξ' ≫ e.hom) ⟨e.hom q.1, h⟩ := by
  have key : ∀ y, genMap (ξ' ≫ e.hom) ⟨e.hom q.1, h⟩ y = genMap ξ' q (e.hom.stalkMap q.1 y) := by
    intro y
    simp only [genMap, CommRingCat.comp_apply]
    rw [Scheme.stalkClosedPointTo_comp]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact congrArg (Scheme.stalkClosedPointTo ξ').hom
      (Scheme.Hom.stalkSpecializes_stalkMap_apply e.hom _ _ q.2 y)
  have hs : Function.Surjective (e.hom.stalkMap q.1) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap q.1)).2
  ext t
  simp only [regAt, RingHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨z, key z⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, (key y).symm⟩

theorem flagiso_span {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V']
    (φ : V ≃ₗ[Ω] V') (R R' : Subring Ω) (h : R' = R) (s : Set V) (v : V) :
    φ v ∈ Submodule.span R' (φ '' s) ↔ v ∈ Submodule.span R s := by
  subst h
  have hsp := Submodule.span_image (R := R') (φ.toLinearMap.restrictScalars R') (s := s)
  change Submodule.span R' (φ '' s) = _ at hsp
  rw [hsp, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hwv' : w = v := φ.injective hwv
    exact hwv' ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem flagiso_step {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V']
    (φ : V ≃ₗ[Ω] V') {r : ℕ} (b : Fin r → V) (i : ℕ) :
    flagStep Ω (fun k => φ (b k)) i = (flagStep Ω b i).map φ.toLinearMap := by
  simp only [flagStep, Submodule.map_span, Set.image_image]
  rfl

theorem flag_bundle_iff_under_isomorphism : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (e : X' ≅ X) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (φ : V ≃ₗ[Ω] V') (L : Lat ξ V) (L' : Lat ξ' V') (r : ℕ) (b : Fin r → V), ξ' ≫ e.hom = ξ → (∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) (v : V), v ∈ L ⟨e.hom q.1, h⟩ ↔ φ v ∈ L' q) → (L.IsFlagVBOn Set.univ b ↔ L'.IsFlagVBOn Set.univ (fun i => φ (b i))) ∧ ∀ (i : Fin r) (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), (L'.gr (fun i => φ (b i)) i q : Set Ω) = L.gr b i ⟨e.hom q.1, h⟩ := by
  intro X X' Ω _ ξ ξ' e V V' _ _ _ _ φ L L' r b hξ hL
  subst hξ
  have hi : ∀ x : X', e.inv (e.hom x) = x := fun x => by simp
  have hj : ∀ y : X, e.hom (e.inv y) = y := fun y => by simp
  have hfwd : ∀ x : X', genPt ξ' ⤳ x → genPt (ξ' ≫ e.hom) ⤳ e.hom x := fun x hx =>
    e.hom.base.hom.map_specializes hx
  have hbwd : ∀ y : X, genPt (ξ' ≫ e.hom) ⤳ y → genPt ξ' ⤳ e.inv y := by
    intro y hy
    have h1 := e.inv.base.hom.map_specializes hy
    have h2 : e.inv (genPt (ξ' ≫ e.hom)) = genPt ξ' := hi _
    rw [← h2]
    exact h1
  have hframe : ∀ (q : Cpt ξ') (p : Cpt (ξ' ≫ e.hom)), e.hom q.1 = p.1 → ∀ c : Fin r → V,
      (L.IsFrameAt c p ↔ L'.IsFrameAt (fun k => φ (c k)) q) := by
    rintro q ⟨p, hp⟩ hqp c
    simp only at hqp
    subst hqp
    have hR := flagiso_reg ξ' e q hp
    have hli : LinearIndependent Ω (fun k => φ (c k)) ↔ LinearIndependent Ω c :=
      LinearMap.linearIndependent_iff φ.toLinearMap φ.ker
    have hset : φ '' Set.range c = Set.range (fun k => φ (c k)) := (Set.range_comp φ c).symm
    simp only [Lat.IsFrameAt, SetLike.ext_iff]
    rw [hli]
    apply and_congr_right
    intro _
    constructor
    · intro H w
      obtain ⟨v, rfl⟩ := φ.surjective w
      rw [← hset, flagiso_span φ _ _ hR, ← H v, hL q hp v]
    · intro H v
      rw [hL q hp v, H (φ v), ← hset, flagiso_span φ _ _ hR]
  have hstep : ∀ (c : Fin r → V) (i : ℕ),
      (flagStep Ω c i = flagStep Ω b i ↔
        flagStep Ω (fun k => φ (c k)) i = flagStep Ω (fun k => φ (b k)) i) := by
    intro c i
    rw [flagiso_step, flagiso_step]
    exact (Submodule.map_injective_of_injective φ.injective).eq_iff.symm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro H q' -
    obtain ⟨U, hU, c, hc, hfr⟩ := H ⟨e.hom q'.1, hfwd _ q'.2⟩ trivial
    refine ⟨e.hom ⁻¹ᵁ U, hU, fun k => φ (c k), fun i => (hstep c i).1 (hc i), ?_⟩
    intro q₁ _ hq₁
    exact (hframe q₁ ⟨e.hom q₁.1, hfwd _ q₁.2⟩ rfl c).1 (hfr _ trivial hq₁)
  · rintro H p -
    obtain ⟨U', hU', c', hc', hfr'⟩ := H ⟨e.inv p.1, hbwd _ p.2⟩ trivial
    refine ⟨e.inv ⁻¹ᵁ U', hU', fun k => φ.symm (c' k), fun i => ?_, ?_⟩
    · rw [hstep]
      simpa using hc' i
    · intro q _ hq
      apply (hframe ⟨e.inv q.1, hbwd _ q.2⟩ q (hj q.1) (fun k => φ.symm (c' k))).2
      simpa using hfr' ⟨e.inv q.1, hbwd _ q.2⟩ trivial hq
  · intro i q h
    have hR := flagiso_reg ξ' e q h
    have hS : {t : Ω | ∃ w ∈ L' q, w - t • φ (b i) ∈ flagStep Ω (fun k => φ (b k)) i} =
        {t : Ω | ∃ v ∈ L ⟨e.hom q.1, h⟩, v - t • b i ∈ flagStep Ω b i} := by
      ext t
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨w, hw, hwt⟩
        obtain ⟨v, rfl⟩ := φ.surjective w
        refine ⟨v, (hL q h v).2 hw, ?_⟩
        rw [flagiso_step] at hwt
        obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.1 hwt
        have hyv' : y = v - t • b i := φ.injective (by simpa using hyv)
        exact hyv' ▸ hy
      · rintro ⟨v, hv, hvt⟩
        refine ⟨φ v, (hL q h v).1 hv, ?_⟩
        rw [flagiso_step]
        have hm := Submodule.mem_map_of_mem (f := φ.toLinearMap) hvt
        simpa using hm
    have key : ∀ (R₁ R₂ : Subring Ω), R₁ = R₂ → ∀ S : Set Ω,
        (Submodule.span R₁ S : Set Ω) = Submodule.span R₂ S := by
      rintro _ _ rfl _
      rfl
    simp only [Lat.gr]
    rw [hS]
    exact key _ _ hR _

end PositivityTheory.UnitarySelfGeneration
