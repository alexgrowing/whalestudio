import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc.SmKill

theorem ctn_sm {K : Type} [Field K] [NumberField K] {n : ℕ} [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {β : archGroup K n → ℝ}
    (hβ : Continuous β) (hβc : HasCompactSupport β) {f : AdelicGLn.AdelicGL K n → ℂ} (hf : Continuous f)
    (r : ℕ) (g : AdelicGLn.AdelicGL K n) :
    Integrable (fun y => (β y : ℂ) * An.ctn r f (g * infEmb K n y)) ν ∧
      An.ctn r (sm ν β f) g = ∫ y, (β y : ℂ) * An.ctn r f (g * infEmb K n y) ∂ν := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ (φ : AdelicGLn.AdelicGL K n → ℂ) (h : AdelicGLn.AdelicGL K n),
      An.ctn r φ h = c * constantTerm r φ h := ⟨_, fun _ _ => rfl⟩
  set F : (UPos n r → AdeleRing (𝓞 K) K) × archGroup K n → ℂ :=
    fun p => c * ((β p.2 : ℂ) * f (unipGL p.1 * g * infEmb K n p.2)) with hF
  have hFc : Continuous F :=
    continuous_const.mul ((Complex.continuous_ofReal.comp (hβ.comp continuous_snd)).mul
      (hf.comp ((continuous_unipGL.comp continuous_fst).mul continuous_const |>.mul
        (continuous_infEmb.comp continuous_snd))))
  have hint : Integrable F ((unipMeasure K n r).restrict (unipFundamentalDomain K n r) |>.prod ν) := by
    have e : ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod ν =
        ((unipMeasure K n r).prod ν).restrict (unipFundamentalDomain K n r ×ˢ Set.univ) := by
      rw [← Measure.restrict_univ (μ := ν), Measure.prod_restrict, Measure.restrict_univ]
    rw [e]
    refine IntegrableOn.of_forall_sdiff_eq_zero
      (hFc.continuousOn.integrableOn_compact (hC.prod hβc.isCompact))
      (measurableSet_unipFundamentalDomain.prod MeasurableSet.univ) fun p hp => ?_
    have hy : p.2 ∉ tsupport β := fun hy => hp.2 ⟨hDC hp.1.1, hy⟩
    simp [hF, image_eq_zero_of_notMem_tsupport hy]
  have hval : ∀ y, ∫ X in unipFundamentalDomain K n r, F (X, y) ∂unipMeasure K n r =
      (β y : ℂ) * An.ctn r f (g * infEmb K n y) := fun y => by
    simp only [hF, hc, constantTerm, mul_assoc]
    rw [integral_const_mul, integral_const_mul]
    ring
  constructor
  · have := hint.swap.integral_prod_left
    refine this.congr (Eventually.of_forall fun y => ?_)
    exact hval y
  · have h := integral_integral_swap (f := fun X y => F (X, y)) hint
    simp only [hval] at h
    rw [← h]
    simp only [hc, constantTerm, sm, hF]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [integral_const_mul]

end GlobalTheory.CompanionTheory.Conc.SmKill

open GlobalTheory.CompanionTheory.Conc.SmKill in

theorem GlobalTheory.CompanionTheory.Conc.kill_sm : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ) (r : ℕ) (p : ℂ[X]), Ker ν β → 0 < r → r < n → Continuous f →
    An.Kill r f p → An.Kill r (sm ν β f) p := by
  intro K _ _ n _ _ ν _ β f r p hk _ _ hf hkill g
  have h1 : ∀ j ∈ Finset.range (p.natDegree + 1),
      p.coeff j * An.ctn r (sm ν β f) (An.aR K n r j * g) =
        ∫ y, p.coeff j * ((β y : ℂ) * An.ctn r f (An.aR K n r j * g * infEmb K n y)) ∂ν := fun j _ => by
    rw [(ctn_sm ν hk.cont hk.cpt hf r _).2, integral_const_mul]
  rw [Finset.sum_congr rfl h1, ← integral_finset_sum _ fun j _ =>
    ((ctn_sm ν hk.cont hk.cpt hf r _).1).const_mul _]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  have h2 := hkill (g * infEmb K n y)
  have h3 : ∑ j ∈ Finset.range (p.natDegree + 1),
      p.coeff j * ((β y : ℂ) * An.ctn r f (An.aR K n r j * g * infEmb K n y)) =
      (β y : ℂ) * ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j * An.ctn r f (An.aR K n r j * (g * infEmb K n y)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (An.aR K n r j)]
    ring
  simp only [Pi.zero_apply]
  rw [h3, h2, mul_zero]

end
