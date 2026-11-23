import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.NormEx
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotEq
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotProd
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotPi
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotLin
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory

theorem UpperTheory.eulerProduct_of_quotient_pushforward_support :
    QPush → EulerSupp → Euler := by
  intro hQ hS V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K T _ _ _ _ _ _ _ _
    Ti _ _ _ _ _ _ _ _ Tv _ _ _ _ _ _ _ _ qT pT KT hR hRT j ji jv h1 h2 h3 μ μi m ν νi nv
    hP hPi hPv S a b ha hb hE hET Fi Fv hFi hFii hFv hloc
  obtain ⟨hM, hSupp, hVal⟩ := hS V G Gi Gv q p K T Ti Tv qT pT KT hR hRT j ji jv h1 h2 h3 S Fi Fv
    hFi hFii hFv hloc
  refine ⟨hM, ?_⟩
  have lin := quotLin_of normEx quotEq
  have prd := quotProd_of normEx quotEq
  have pie := quotPi_of normEx quotEq
  let J : (∀ v : S, Tv v) →* ∀ v : S, Gv v :=
    Pi.monoidHom fun v : S => (jv v).comp (Pi.evalMonoidHom _ v)
  have hJ : ∀ (t : ∀ v : S, Tv v) (v : S), J t v = jv v (t v) := fun _ _ => rfl
  obtain ⟨pairPi, valPi⟩ := pie S (fun v : S => Gv v) (fun v : S => Tv v) (fun v : S => m v)
    (fun v : S => jv v) (fun v : S => nv v) (fun v => hPv v) J hJ
  obtain ⟨pairPr, valPr⟩ := prd Gi Ti (∀ v : S, Gv v) (∀ v : S, Tv v) μi ji νi hPi _ J _ pairPi
  obtain ⟨pairL, valL⟩ := (lin _ _ _ _ _ pairPr).2 a b ha hb
  have pullbackMapSquare : Measurable fun g : ∀ v : S, Gv v => ∏ v : S, Fv v (g v) :=
    Finset.measurable_fun_prod _ fun v _ => (hFv v).1.comp (measurable_pi_apply v)
  have indexFSecond : ∀ (t : ∀ v : S, Tv v) (g : ∀ v : S, Gv v),
      ∏ v : S, Fv v ((J t * g) v) = ∏ v : S, Fv v (g v) := fun t g =>
    Finset.prod_congr rfl fun v _ => (hFv v).2 (t v) (g v)
  have mF' : Measurable fun x : Gi × ∀ v : S, Gv v => Fi x.1 * ∏ v : S, Fv v (x.2 v) :=
    (hFi.comp measurable_fst).mul (pullbackMapSquare.comp measurable_snd)
  have iF' : ∀ (t : Ti × ∀ v : S, Tv v) (g : Gi × ∀ v : S, Gv v),
      Fi ((ji.prodMap J t * g).1) * ∏ v : S, Fv v ((ji.prodMap J t * g).2 v) =
        Fi g.1 * ∏ v : S, Fv v (g.2 v) := fun t g => by
    have e1 : Fi ((ji.prodMap J t * g).1) = Fi g.1 := hFii t.1 g.1
    have e2 : ∏ v : S, Fv v ((ji.prodMap J t * g).2 v) = ∏ v : S, Fv v (g.2 v) := indexFSecond t.2 g.2
    rw [e1, e2]
  have hpre : j ⁻¹' (US p K S : Set G) = (US pT KT S : Set T) := by
    ext t
    constructor
    · intro ht v hv
      have := ht v hv
      rw [h2] at this
      exact (h3 v _).2 this
    · intro ht v hv
      show p v (j t) ∈ K v
      rw [h2]
      exact (h3 v _).1 (ht v hv)
  have hET' : (ν.restrict (j ⁻¹' (US p K S : Set G))).map (prS qT pT S) =
      b • νi.prod (Measure.pi fun v : S => nv v) := by
    rw [hpre]; exact hET
  have cπ : Continuous (prS q p S) :=
    hR.cq.prodMk (continuous_pi fun v : S => hR.cp v)
  have cπT : Continuous (prS qT pT S) :=
    hRT.cq.prodMk (continuous_pi fun v : S => hRT.cp v)
  have comm : ∀ t, prS q p S (j t) = ji.prodMap J (prS qT pT S t) := fun t => by
    refine Prod.ext (h1 t) (funext fun v => h2 v t)
  have iF : ∀ t g, Fi (q (j t * g)) * ∏ᶠ v, Fv v (p v (j t * g)) =
      Fi (q g) * ∏ᶠ v, Fv v (p v g) := fun t g => by
    have e1 : Fi (q (j t * g)) = Fi (q g) := by rw [map_mul, h1, hFii]
    have e2 : ∀ v, Fv v (p v (j t * g)) = Fv v (p v g) := fun v => by
      rw [map_mul, h2, (hFv v).2]
    simp only [e1, e2]
  have push := hQ G T (Gi × ∀ v : S, Gv v) (Ti × ∀ v : S, Tv v) μ j ν _ (ji.prodMap J) _ hP pairL
    (US p K S) (hR.opnU S) (prS q p S) (prS qT pT S) cπ cπT comm hE hET'
    (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g))
    (fun x => Fi x.1 * ∏ v : S, Fv v (x.2 v)) hM iF mF' iF' hSupp hVal
  rw [push, (valL _ mF' iF').2, (valPr Fi _ hFi hFii pullbackMapSquare indexFSecond).2, (valPi fun v : S => Fv v)
    (fun v => hFv v) |>.2, Finset.prod_coe_sort S fun v => qI (m v) (jv v) (nv v) (Fv v), mul_assoc]
