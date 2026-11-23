import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentre
import Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap
import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinIso.JoinIso

theorem chRing_mem {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {ι : Type} {J : ι → Ω} {d : ι}
    {S : Subring Ω} (ho : ∀ r : o, algebraMap o Ω r ∈ S) (h : ∀ q, J q / J d ∈ S) :
    ∀ a ∈ chRing o J d, a ∈ S := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨q, rfl⟩ := hy
    exact h q
  | algebraMap r => exact ho r
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem eq_of_units {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {c : κ} {p q : Cpt M.ξ} (hp : InChart M.ξ x c p) (hq : InChart M.ξ x c q)
    (h : ∀ u ∈ chRing o x c, unitAt M.ξ p u ↔ unitAt M.ξ q u) : p = q := by
  have hle : ∀ {p q : Cpt M.ξ}, InChart M.ξ x c p → InChart M.ξ x c q →
      (∀ u ∈ chRing o x c, unitAt M.ξ p u → unitAt M.ξ q u) → regAt M.ξ p ≤ regAt M.ξ q := by
    intro p q hp hq h a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hp).2 a).1 ha
    exact ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c q hq).2 _).2 ⟨u, hu, v, hv, h v hv hvu, rfl⟩
  have h1 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p q).1 (hle hp hq fun u hu => (h u hu).1)
  have h2 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M q p).1 (hle hq hp fun u hu => (h u hu).2)
  exact Subtype.ext (h2.antisymm h1).eq

theorem isoAt_of_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) → ∀ p : Cpt M.ξ, (∃ l, InChart M.ξ w l p) → IsoAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ Ω _ _ κ _ x M κ' _ w M' f hd p ⟨l, hl⟩
  obtain ⟨c, hc⟩ := M.tie.cover p
  have hJ0 : joinCo (RingHom.id Ω) x w (c, l) ≠ 0 := mul_ne_zero hc.1 hl.1
  have ratio : ∀ j m, joinCo (RingHom.id Ω) x w (j, m) / joinCo (RingHom.id Ω) x w (c, l) =
      (x j / x c) * (w m / w l) := fun j m => by
    simp only [joinCo, RingHom.id_apply, mul_div_mul_comm]
  have hpJ : ∀ q, joinCo (RingHom.id Ω) x w q / joinCo (RingHom.id Ω) x w (c, l) ∈ regAt M.ξ p := by
    rintro ⟨j, m⟩
    rw [ratio]
    exact mul_mem (hc.2 j) (hl.2 m)
  have hAp := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hc).1
  have hctr : p ∈ ctrSet o (joinCo (RingHom.id Ω) x w) (RingHom.id Ω) M.ξ :=
    ⟨(c, l), hJ0, chRing_mem (fun r => hAp _ (Subalgebra.algebraMap_mem _ r)) hpJ⟩
  obtain ⟨p', ⟨hle', hun'⟩, -, hch'⟩ :=
    PositivityTheory.HtPt.Mb.centre o Ω (κ × κ') (joinCo (RingHom.id Ω) x w) M' M.X Ω M.ξ (RingHom.id Ω) p hctr
  have hle : ∀ a ∈ regAt M'.ξ p', a ∈ regAt M.ξ p := hle'
  have hun : ∀ a ∈ regAt M'.ξ p', unitAt M.ξ p a → unitAt M'.ξ p' a := hun'
  have hp'c : InChart M'.ξ (joinCo (RingHom.id Ω) x w) (c, l) p' := hch' (c, l) hJ0 hpJ
  have dom := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ M'.X Ω M'.ξ (RingHom.id Ω) f hd
  obtain ⟨h, hq1', hq2'⟩ := dom p'
  have hq1 : ∀ a ∈ regAt M.ξ ⟨f p'.1, h⟩, a ∈ regAt M'.ξ p' := hq1'
  have hq2 : ∀ a ∈ regAt M.ξ ⟨f p'.1, h⟩, unitAt M'.ξ p' a → unitAt M.ξ ⟨f p'.1, h⟩ a := hq2'
  have hx : ∀ j, x j / x c ∈ regAt M'.ξ p' := fun j => by
    have e : joinCo (RingHom.id Ω) x w (j, l) / joinCo (RingHom.id Ω) x w (c, l) = x j / x c := by
      rw [ratio, div_self hl.1, mul_one]
    rw [← e]
    exact hp'c.2 (j, l)
  obtain ⟨c₁, hc₁⟩ := M.tie.cover ⟨f p'.1, h⟩
  have hu : unitAt M.ξ ⟨f p'.1, h⟩ (x c / x c₁) :=
    hq2 _ (hc₁.2 c) ⟨div_ne_zero hc.1 hc₁.1, hq1 _ (hc₁.2 c), by rw [inv_div]; exact hx c₁⟩
  have hqc : InChart M.ξ x c ⟨f p'.1, h⟩ := ⟨hc.1, fun j => by
    have e : x j / x c = (x j / x c₁) * (x c / x c₁)⁻¹ := by
      have h1 := hc.1
      have h2 := hc₁.1
      field_simp
    rw [e]
    exact mul_mem (hc₁.2 j) hu.2.2⟩
  have hqp : (⟨f p'.1, h⟩ : Cpt M.ξ) = p := by
    refine eq_of_units M hqc hc fun u hu => ?_
    have uq := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hqc).1 u hu
    exact ⟨fun k => ⟨k.1, hAp u hu, hle _ (hq1 _ k.2.2)⟩, fun k => hq2 u uq (hun u (hq1 u uq) k)⟩
  have e' : f p'.1 = p.1 := congrArg Subtype.val hqp
  rw [hqp] at hq1
  have hreg : regAt M'.ξ p' = regAt M.ξ p := le_antisymm hle hq1
  have uniq : ∀ p'' : Cpt M'.ξ, f p''.1 = p.1 → p'' = p' := by
    intro p'' e
    obtain ⟨h2, r1', r2'⟩ := dom p''
    have e2 : (⟨f p''.1, h2⟩ : Cpt M.ξ) = p := Subtype.ext e
    rw [e2] at r1' r2'
    have r1 : ∀ a ∈ regAt M.ξ p, a ∈ regAt M'.ξ p'' := r1'
    have r2 : ∀ a ∈ regAt M.ξ p, unitAt M'.ξ p'' a → unitAt M.ξ p a := r2'
    have hch : InChart M'.ξ (joinCo (RingHom.id Ω) x w) (c, l) p'' := ⟨hJ0, fun q => r1 _ (hpJ q)⟩
    refine eq_of_units M' hch hp'c fun u hu => ?_
    have up' := (PositivityTheory.HtPt.Ma.regat_loc o Ω (κ × κ') _ M' (c, l) p' hp'c).1 u hu
    have up := hle u up'
    exact ⟨fun k => hun u up' (r2 u up k), fun k => ⟨k.1, r1 u up, r1 _ (hle _ k.2.2)⟩⟩
  refine ⟨⟨p', e', fun p'' e => uniq p'' e⟩, fun p'' e => ?_, hd⟩
  rw [uniq p'' e, hreg, Subring.map_id]

end PositivityTheory.HtPt.Mb.LJoinIso.JoinIso

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.join_iso : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) → ∀ p : Cpt M.ξ, (∃ l, InChart M.ξ w l p) → IsoAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LJoinIso.JoinIso.isoAt_of_chart
