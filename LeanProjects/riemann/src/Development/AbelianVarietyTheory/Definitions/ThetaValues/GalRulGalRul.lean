import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.GalTw.Test

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD map_trans evR_spec evR_not evR_map)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem allTest : AllTest Xo c :=
  Frames.allTest_of_secBaseChange (Out.Laws.secBaseChange GlobalTheory.abelianSchemeLaws_all.1) E H Dw l Xo c

theorem valueWD : ValueWD Xo c :=
  evalWD_fr (frChartF_of
    (Frames.chartCoverF_of_secBaseChange (Out.Laws.secBaseChange GlobalTheory.abelianSchemeLaws_all.1) E H Dw l Xo c))

theorem galRul_one {ta : c.F ≃+* c.F} (h : Fixes c ta) : galRul (Xo := Xo) h 1 = 1 := by
  funext p y
  obtain ⟨q, φ, y₀, -, hq⟩ := evR_spec (GlobalTheory.GalTw.Rule.fromT_tw_test h allTest p y)
  show (evR Xo c 1 (twPt h y)).val = (1 : Rul Xo c) p y
  rw [hq]
  simp only [Pi.one_apply, map_one]
  rfl

theorem galRul_mul {ta : c.F ≃+* c.F} (h : Fixes c ta) (f g : Rul Xo c) :
    galRul h (f * g) = galRul h f * galRul h g := by
  funext p y
  obtain ⟨q, φ, y₀, -, hq⟩ := evR_spec (GlobalTheory.GalTw.Rule.fromT_tw_test h allTest p y)
  show (evR Xo c (f * g) (twPt h y)).val = (evR Xo c f (twPt h y)).val * (evR Xo c g (twPt h y)).val
  rw [hq, hq, hq, Pi.mul_apply, Pi.mul_apply, map_mul]
  rfl

theorem galRul_const {ta : c.F ≃+* c.F} (h : Fixes c ta) (a : c.F) :
    galRul h (a • (1 : Rul Xo c)) = ta a • (1 : Rul Xo c) := by
  rw [galRul_smul h a 1, galRul_one h]

theorem fixes_trans {s t : c.F ≃+* c.F} (hs : Fixes c s) (ht : Fixes c t) : Fixes c (s.trans t) :=
  ⟨fun τ a => by rw [RingEquiv.trans_apply, hs.emb τ a, ht.emb τ a],
    fun a => by rw [RingEquiv.trans_apply, hs.base a, ht.base a]⟩

theorem galRul_galRul {s t : c.F ≃+* c.F} (hs : Fixes c s) (ht : Fixes c t) {f : Rul Xo c} (hf : Natural c f) :
    galRul ht (galRul hs f) = galRul (fixes_trans hs ht) f := by
  funext p y
  have hWD : ValueWD Xo c := valueWD
  have hA : AllTest Xo c := allTest
  show (evR Xo c (galRul hs f) (twPt ht y)).val = (evR Xo c f (twPt (fixes_trans hs ht) y)).val
  rw [GlobalTheory.GalTw.Rule.evR_galRul hs hWD hA hf (twPt ht y)]
  obtain ⟨q, φ, y₀, hm, -⟩ := evR_spec (GlobalTheory.GalTw.Rule.fromT_tw_test (fixes_trans hs ht) hA p y)
  let φ' : q.R →ₐ[c.F] Tw s (Tw t p.R) := { φ.toRingHom with commutes' := fun a => φ.commutes a }
  have hm' : FrMap φ' y₀ (twPt hs (twPt ht y)) := hm
  rw [GlobalTheory.CoefChangeCompare.evR_of_map hWD hf hm', GlobalTheory.CoefChangeCompare.evR_of_map hWD hf hm]
  rfl

theorem exists_moved {ta : c.F ≃+* c.F} (h : Fixes c ta) (hta : ta ≠ RingEquiv.refl _) (p : TRing c.F)
    [Nontrivial p.R] (y : FrPt Xo c p.R) : ∃ f : Rul Xo c, galRul h f ≠ f := by
  obtain ⟨a, ha⟩ : ∃ a, ta a ≠ a := by
    by_contra hc
    exact hta (RingEquiv.ext fun x => not_not.mp fun hx => hc ⟨x, hx⟩)
  refine ⟨a • (1 : Rul Xo c), fun heq => ha ?_⟩
  rw [galRul_const h a] at heq
  have hv := congrFun (congrFun heq p) y
  simp only [Pi.smul_apply, Pi.one_apply, Algebra.smul_def, mul_one] at hv
  exact (algebraMap c.F p.R).injective hv

theorem galRul_refl {f : Rul Xo c} (hf : Natural c f) : galRul fixes_refl f = f := by
  funext p y
  obtain ⟨q, φ, y₀, hm, -⟩ := evR_spec (GlobalTheory.GalTw.Rule.fromT_tw_test fixes_refl allTest p y)
  show (evR Xo c f (twPt fixes_refl y)).val = f p y
  rw [GlobalTheory.CoefChangeCompare.evR_of_map valueWD hf hm]
  let φ' : q.R →ₐ[c.F] p.R := { φ.toRingHom with commutes' := fun a => φ.commutes a }
  have hm' : FrMap φ' y₀ y := hm
  have h1 := GlobalTheory.CoefChangeCompare.evR_of_map valueWD hf hm'
  rw [GlobalTheory.CoefChangeCompare.evR_test hf p y] at h1
  exact h1.symm

end GlobalTheory.GalTw.Test
