import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueBarCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvaluatesOfUnif

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.ConjNorm

open GlobalTheory.ConjInner

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

set_option maxHeartbeats 1000000 in

theorem inner_reading_conj_at (he : R.models_HW) (fw : FWTie T R κ v₀) (hE : fw.Evaluates) (hT : BarTie fw) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i)
    (hB : JEvBarAt T R κ i σ hV) :
    ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ =
      starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ := by
  have hg : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have h1 := (hT i σ hσ hV).1 hB
  obtain ⟨v, hv, h1⟩ := h1
  have h2 := hE i ((starRingEnd ℂ).comp σ) hg hV
  have h3 : ∀ f g, evAt R i σ v (fw.jK i σ f) g =
      starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) (fw.jK i ((starRingEnd ℂ).comp σ) f) g) := fun f g =>
    (congrFun (h1 f) g).trans (congrArg (starRingEnd ℂ) (congrFun (h2 f) g).symm)
  have h4 : ∀ f f', ⟪fw.jK i σ f, fw.jK i σ f'⟫_ℂ =
      starRingEnd ℂ ⟪fw.jK i ((starRingEnd ℂ).comp σ) f, fw.jK i ((starRingEnd ℂ).comp σ) f'⟫_ℂ := fun f f' =>
    inner_conj_of_values R he i σ hv (fun τ => ((fw.hv₀ i _).1 τ).1) (h3 f) (h3 f')
  have h5 := fw.ks i
  obtain ⟨n, b, hb, -, -, -, h5⟩ := h5
  refine inner_conj_of_span σ _ _ _ h5 ?_
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  have e : ∀ k, ∃ f, ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = b k := fun k =>
    ⟨(fw.e i).symm ⟨b k, hb k⟩, congrArg Subtype.val ((fw.e i).apply_symm_apply _)⟩
  have e1 := e k
  have e2 := e l
  obtain ⟨f, e1⟩ := e1
  obtain ⟨f', e2⟩ := e2
  rw [← e1, ← e2]
  exact h4 f f'

theorem norm_eq_of_inner_conj {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] {x : H} {y : H'} (h : ⟪x, x⟫_ℂ = starRingEnd ℂ ⟪y, y⟫_ℂ) : ‖y‖ = ‖x‖ := by
  rw [inner_conj_symm] at h
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, h]

set_option maxHeartbeats 1000000 in

theorem norm_conj_of_not_good (he : R.models_HW) (fw : FWTie T R κ v₀) (hE : fw.Evaluates) (hT : BarTie fw) (hu : R.LUnif)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (x : Fin (R.nW i) → D.what₂.LL) :
    ‖(R.FW i).j ((starRingEnd ℂ).comp σ) x‖ = ‖(R.FW i).j σ x‖ := by
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := fw.laws.spaceW _ (inR i) _ (good_resC T hσ)
  by_cases hB : JEvBarAt T R κ i σ hV
  · exact norm_eq_of_inner_conj (inner_reading_conj_at T R κ v₀ he fw hE hT i σ hσ hV hB x x)
  · have h0 := (hT i σ hσ hV).2 hB
    have hx : x = 0 := by
      by_contra hx
      have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
      have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
      rw [h0] at h2
      exact h2 rfl
    subst hx
    rw [map_zero, map_zero, norm_zero, norm_zero]

omit R in

theorem not_good_conj {σ : D.what₂.LL →+* ℂ} (h : GoodEmb T.Q.c (res T σ)) :
    ¬ GoodEmb T.Q.c (res T ((starRingEnd ℂ).comp σ)) := by
  have key : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
      {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) {s : c.F →+* ℂ}, GoodEmb c s →
      ¬ GoodEmb c ((starRingEnd ℂ).comp s) := by
    intro E _ _ _ H l c s h h'
    have h2 : starRingEnd ℂ H.rt0 = H.rt0 := by
      conv_lhs => rw [← h]
      exact h'
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h2
    have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp [pow_two, him] at h3
    nlinarith [mul_self_nonneg H.rt0.re]
  exact key T.Q.c h

end GlobalTheory.ConjNorm

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.ConjNorm.pConj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ fw : FWTie T R κ v₀, BarTie fw → R.LUnif → R.PConj := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ fw hT hu i σ x
  have hE := GlobalTheory.evaluates_of_unif D G Pl0 T0 A T R F κ v₀ fw hu
  have key : ∀ σ, ¬ GoodEmb T.Q.c (res T σ) → (R.FW i).nrmAt ((starRingEnd ℂ).comp σ) x = (R.FW i).nrmAt σ x :=
    fun σ hσ => GlobalTheory.ConjNorm.norm_conj_of_not_good T R κ v₀ hC.models.HW fw hE hT hu i σ hσ x
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · have h1 := key _ (GlobalTheory.ConjNorm.not_good_conj T hσ)
    have e : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := RingHom.ext fun a => Complex.conj_conj _
    exact h1.symm.trans (congrArg (fun s => (R.FW i).nrmAt s x) e)
  · exact key σ hσ
