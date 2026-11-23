import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentre
import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LPulllocCentre

theorem pullLoc_eq_span_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F) (p₀ : Cpt M.ξ) (p' : Cpt ξ'), L.IsCohOn Set.univ → ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) → L.pullLoc ξ' i j p' = Submodule.span (regAt ξ' p') (j '' (L p₀ : Set E)) := by
  intro o _ Ω _ _ κ _ x M E _ _ L X' Ω' _ ξ' i F _ _ j p₀ p' hcoh hdom
  obtain ⟨hd1, hd2⟩ := hdom
  obtain ⟨c, hc⟩ := M.tie.cover p₀
  have hcx : x c ≠ 0 := hc.1
  have hch0 : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p₀ := fun a ha => (M.tie.ring c hcx a).1 ha p₀ hc
  have hctr : p' ∈ ctrSet o x i ξ' := ⟨c, hcx, fun a ha => hd1 a (hch0 a ha)⟩
  obtain ⟨p₁, ⟨h11, -⟩, h13, h14⟩ := PositivityTheory.HtPt.Mb.centre o Ω κ x M X' Ω' ξ' i p' hctr
  have hp1c : InChart M.ξ x c p₁ := h14 c hcx fun k => hd1 _ (hc.2 k)
  have hle : regAt M.ξ p₁ ≤ regAt M.ξ p₀ := by
    intro a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p₁ hp1c).2 a).1 ha
    have hiv : unitAt ξ' p' (i v) :=
      ⟨(map_ne_zero i).2 hvu.1, h11 _ hvu.2.1, by rw [← map_inv₀]; exact h11 _ hvu.2.2⟩
    have hv0 : unitAt M.ξ p₀ v := hd2 v (hch0 v hv) hiv
    rw [div_eq_mul_inv]
    exact mul_mem (hch0 u hu) hv0.2.2
  have hsp : p₀.1 ⤳ p₁.1 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p₁ p₀).1 hle
  have hstalk : ∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → ∀ e ∈ L p, e ∈ L p₀ := by
    intro p hp e he
    have hs : p₀.1 ⤳ p.1 := hsp.trans (h13 p hp)
    obtain ⟨U, hU, n, b, hb⟩ := hcoh p (Set.mem_univ p)
    have h0U : p₀.1 ∈ U := hs.mem_open U.isOpen hU
    have hreg : regAt M.ξ p ≤ regAt M.ξ p₀ := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p p₀).2 hs
    rw [hb p (Set.mem_univ p) hU] at he
    rw [hb p₀ (Set.mem_univ p₀) h0U]
    induction he using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy => exact Submodule.smul_mem _ (⟨a, hreg a.2⟩ : regAt M.ξ p₀) hy
  exact Lat.pullLoc_eq_span_of_ctr j ⟨hd1, hd2⟩ fun p hp => hstalk p hp.1

end PositivityTheory.HtPt.Mb.LPulllocCentre

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.pullloc_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F) (p₀ : Cpt M.ξ) (p' : Cpt ξ'), L.IsCohOn Set.univ → ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) → L.pullLoc ξ' i j p' = Submodule.span (regAt ξ' p') (j '' (L p₀ : Set E)) :=
  @PositivityTheory.HtPt.Mb.LPulllocCentre.pullLoc_eq_span_centre
