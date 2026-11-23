import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.GalTw

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD map_trans evR_spec evR_not evR_map)

namespace Rule

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {ta : c.F ≃+* c.F}

theorem fixes_symm (h : Fixes c ta) : Fixes c ta.symm :=
  ⟨fun τ a => by rw [RingEquiv.symm_apply_eq, h.emb], fun a => by rw [RingEquiv.symm_apply_eq, h.base]⟩

def twHom (ta : c.F ≃+* c.F) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) : Tw ta S →ₐ[c.F] Tw ta T :=
  { φ.toRingHom with commutes' := fun a => φ.commutes (ta a) }

def untwHom {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] Tw ta T) : Tw ta.symm S →ₐ[c.F] T :=
  { φ.toRingHom with
    commutes' := fun a => (φ.commutes (ta.symm a)).trans
      (congrArg (algebraMap c.F T) (ta.apply_symm_apply a)) }

theorem fromT_tw_test (h : Fixes c ta) (hA : AllTest Xo c) (p : TRing c.F) (y : FrPt Xo c p.R) :
    FromT (twPt h y) := by
  haveI : IsReduced (Tw ta p.R) := ((GlobalTheory.reduced_finiteType_iff_testRing c.F).2 p).2
  exact hA _ _

theorem fromT_of_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hy : FromT y) (hm : FrMap φ y z) : FromT z := by
  obtain ⟨p, ψ, y₀, h₀⟩ := hy
  exact ⟨p, _, y₀, map_trans ψ φ h₀ hm⟩

theorem frMap_tw (h : Fixes c ta) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap φ y z) :
    FrMap (twHom ta φ) (twPt h y) (twPt h z) := hm

theorem fromT_of_tw (h : Fixes c ta) (hA : AllTest Xo c) {S : Type} [CommRing S] [Algebra c.F S]
    {y : FrPt Xo c S} (hy : FromT (twPt h y)) : FromT y := by
  obtain ⟨p, φ, y₀, h₀⟩ := hy
  have h₁ : FrMap (untwHom φ) (twPt (fixes_symm h) y₀) y := h₀
  exact fromT_of_map (fromT_tw_test (fixes_symm h) hA p y₀) h₁

theorem evR_galRul (h : Fixes c ta) (hWD : ValueWD Xo c) (hA : AllTest Xo c) {f : Rul Xo c} (hf : Natural c f)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val := by
  by_cases hy : FromT y
  · obtain ⟨q, φ, y₀, hm, e⟩ := evR_spec hy
    rw [e, evR_map hWD hf (fromT_tw_test h hA q y₀) (frMap_tw h hm)]
    rfl
  · rw [evR_not hy, evR_not (fun h' => hy (fromT_of_tw h hA h'))]
    rfl

theorem galRul_mem_sec (h : Fixes c ta) (hWD : ValueWD Xo c) (hA : AllTest Xo c) (hB : BorChartF Xo c)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) : galRul h f ∈ sec Xo c a n := by
  refine ⟨fun p q φ y z hm => ?_, fun q t y y' hb => ?_⟩
  · exact evR_map hWD hf.1 (fromT_tw_test h hA p y) (frMap_tw h hm)
  · have hb' : FrBor (S := Tw ta q.R) t (twPt h y) (twPt h y') := hb
    have h3 : evR Xo c f (twPt h y') = _ * evR Xo c f (twPt h y) :=
      wtAll_of_borChart hB (ex Dw a n) hf.1 hf.2 (Tw ta q.R) _ _ _ (fromT_tw_test h hA q y)
        (fromT_tw_test h hA q y') hb'
    exact h3

end Rule

theorem galRul_sec_val_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, galRul h f ∈ sec Xo c a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val) ∧ (∀ (t : c.F) (f g : Rul Xo c), galRul h (t • f + g) = ta t • galRul h f + galRul h g) ∧ ∀ (c₀ : Coeff l) (hle : c₀.F ≤ c.F), (∀ x : c₀.F, ta (incF c₀ c hle x) = incF c₀ c hle x) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (as : Fin m → c.F) (fs : Fin m → Rul Xo c₀), ∀ f ∈ sec Xo c a n, IsBC hle f as fs → IsBC hle (galRul h f) (fun i => ta (as i)) fs := by
  intro E _ _ _ H Dw l Xo c ta h
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hc := GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c
  have hWD : ValueWD Xo c := evalWD_fr (frChartF_of hc)
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hB : BorChartF Xo c := borChartF_of_cover hc
  refine ⟨fun a n f hf => ⟨Rule.galRul_mem_sec h hWD hA hB hf, fun S _ _ y => Rule.evR_galRul h hWD hA hf.1 y⟩,
    fun t f g => ?_, ?_⟩
  · funext p y
    have h1 : evR Xo c (t • f + g) (twPt h y) =
        algebraMap c.F (Tw ta p.R) t * evR Xo c f (twPt h y) + evR Xo c g (twPt h y) := by
      unfold evR
      rw [evalAt_add, evalAt_smul]
    refine h1.trans ?_
    show _ = ta t • galRul h f p y + galRul h g p y
    rw [Algebra.smul_def]
    rfl
  · intro c₀ hle hfix a n m as fs f hf hbc S _ A _ ho y
    letI : Algebra c₀.F (Tw ta S) := A
    have ho' : AlgOver c₀ c hle (Tw ta S) := fun x =>
      (congrArg (algebraMap c.F S) (hfix x)).trans (ho x)
    rw [Rule.evR_galRul h hWD hA hf.1 y]
    exact hbc (Tw ta S) ho' (twPt h y)

end GlobalTheory.GalTw
