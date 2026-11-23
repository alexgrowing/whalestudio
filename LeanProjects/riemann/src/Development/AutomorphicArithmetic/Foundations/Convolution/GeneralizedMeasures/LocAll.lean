import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.LocHeckeInert
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LocHeckeSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.PolyMem

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

namespace UpperTheory.ConvolutionTheory.GM.LocalAllPlaces

private theorem sph_unique {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (p : MvPolynomial (Fin n) ℂ)
    (h h' : GL (Fin n) (w.adicCompletion K) → ℂ) (a : IsSph w p h) (b : IsSph w p h') : h = h' := by
  obtain ⟨m1, b1, μ1, h1, hμ1, H1, e1, s1⟩ := a
  obtain ⟨m2, b2, μ2, h2, hμ2, H2, e2, s2⟩ := b
  obtain rfl : m1 = m2 := b1.measurable_eq.trans b2.measurable_eq.symm
  obtain rfl : μ1 = μ2 := by
    have h := Measure.isMulLeftInvariant_eq_smul μ1 μ2
    have h3 := congrArg (fun m : Measure _ => m (GLnLocal.integralGL (w.adicCompletion K) n)) h
    simp only [Measure.smul_apply, hμ1, hμ2] at h3
    have h4 : Measure.haarScalarFactor μ1 μ2 = 1 := by
      have : ((Measure.haarScalarFactor μ1 μ2 : NNReal) : ENNReal) = 1 := by
        rw [h3]; simp [ENNReal.smul_def]
      exact_mod_cast this
    rw [h4, one_smul] at h
    exact h
  obtain rfl : H1 = H2 := satakeTransform_injective (s1.trans s2.symm)
  funext x
  rw [← e1, ← e2]

private theorem powE_one {n : ℕ} (i : Fin n) : powE 1 i = X i := by
  unfold powE
  rw [AlgEquiv.symm_apply_eq]
  apply Subtype.ext
  simp [esymmAlgEquiv_apply, esymmAlgHom_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem over_iff (v : Pl F) (w : Pl E) : w.asIdeal.LiesOver v.asIdeal ↔ w.under (𝓞 F) = v := by
  constructor
  · intro h
    exact HeightOneSpectrum.ext h.over.symm
  · rintro rfl
    exact ⟨rfl⟩

private theorem resDeg_split (v : Pl F) (hs : Split E v) (w : PlacesOver E v) : resDeg F w.1 = 1 := by
  have h := finrank_eq_ramificationIdx_mul_inertiaDeg E v w.1
  have h1 : Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = 1 :=
    Module.finrank_of_bijective_algebraMap ⟨(completionMap v w.1).injective, hs w⟩
  rw [h1] at h
  exact Nat.eq_one_of_mul_eq_one_left h.symm

private theorem resDeg_inert (v : Pl F) (hu : Unr E v) (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w) :
    resDeg F w.1 = Module.finrank F E := by
  have he : w.1.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_iff.2 (hu w)
  rw [← sum_ramificationIdx_mul_inertiaDeg E v, Finset.sum_eq_single w (fun b _ hb => absurd (hw b) hb) (by simp), he, one_mul]
  rfl

open Classical in
private theorem prod_filter {M : Type} [CommMonoid M] (κ : Finset (Pl E)) (v : Pl F) (a : Pl E → M) :
    ∏ w ∈ κ.filter (fun w => w.under (𝓞 F) = v), a w = ∏ w : PlacesOver E v, if w.1 ∈ κ then a w.1 else 1 := by
  rw [← Finset.prod_filter]
  symm
  refine Finset.prod_bij (fun w _ => w.1) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact ⟨hw, (over_iff v w.1).1 w.2⟩
  · intro w _ w' _ h
    exact Subtype.ext h
  · intro w hw
    simp only [Finset.mem_filter] at hw
    exact ⟨⟨w, (over_iff v w).2 hw.2⟩, by simp [hw.1], rfl⟩
  · intro w _
    rfl

end UpperTheory.ConvolutionTheory.GM.LocalAllPlaces

open UpperTheory.ConvolutionTheory.GM.LocalAllPlaces in
theorem UpperTheory.ConvolutionTheory.GM.locAll :
    LocUnit → LocAll := by
  classical
  intro hU F E _ _ _ _ _ _ _ _ σ hσ hp n hn κ hκ t₀ ht D
  have key : ∀ w : Pl E, ∃ γ : MvPolynomial (Fin n) ℂ,
      (w ∈ κ → eval (fun i : Fin n => (t₀ w).esymm (i + 1)) γ ≠ 0) ∧
      (w ∈ κ → ∀ (v : Pl F) (hw : w.asIdeal.LiesOver v.asIdeal), ¬ Split E v →
        ∀ p : MvPolynomial (Fin n) ℂ, p.totalDegree ≤ D → ∀ h f, IsSph w (γ * p) h →
          IsSph v (aeval (powE (Module.finrank F E)) (γ * p)) f →
          MatchAt σ v 1 (fun g => h (cmp (⟨w, hw⟩ : PlacesOver E v) g)) f) := by
    intro w
    by_cases hw : w ∈ κ
    · by_cases hs : Split E (w.under (𝓞 F))
      · refine ⟨1, fun _ => by simp, fun _ v hv hns => ?_⟩
        obtain rfl := (over_iff v w).1 hv
        exact absurd hs hns
      · obtain ⟨γ, h1, h2⟩ := UpperTheory.ConvolutionTheory.H.locHeckeInert F E σ hσ hp n hn _ (hκ w hw) hs ⟨w, ⟨rfl⟩⟩ (t₀ w)
          (ht w hw).1 (ht w hw).2 D
        refine ⟨γ, fun _ => h1, fun _ v hv _ => ?_⟩
        obtain rfl := (over_iff v w).1 hv
        exact h2
    · exact ⟨1, fun h => absurd h hw, fun h => absurd h hw⟩
  choose γ hγ1 hγ2 using key
  refine ⟨γ, hγ1, fun p hpD v hv h f hh hh' hf => ?_⟩
  rw [prod_filter] at hf
  by_cases hs : Split E v
  · refine UpperTheory.ConvolutionTheory.L1.locHeckeSplit F E σ hσ hp n hn v hs (fun w => if w.1 ∈ κ then γ w.1 * p w.1 else 1)
      (fun w => h w.1) f (fun w => ?_) ?_
    · by_cases hw : w.1 ∈ κ
      · simpa only [if_pos hw] using hh _ hw
      · simp only [if_neg hw, hh' _ hw]
        exact (sphEx E n hn w.1).2.1
    · rw [finprod_eq_prod_of_fintype]
      convert hf using 2 with w
      have : (powE 1 : Fin n → MvPolynomial (Fin n) ℂ) = X := funext powE_one
      rw [resDeg_split v hs w, this, aeval_X_left_apply]
  · obtain ⟨w, hw⟩ := UpperTheory.V.Z.Tf.Orb.placeUniq_holds F E hp v hs
    rw [Finset.prod_eq_single w (fun b _ hb => absurd (hw b) hb) (by simp)] at hf
    have e : (prodFn fun w : PlacesOver E v => h w.1) = fun g => h w.1 (cmp w g) := by
      funext g
      exact finprod_eq_single _ w fun b hb => absurd (hw b) hb
    rw [e]
    by_cases hk : w.1 ∈ κ
    · rw [if_pos hk, resDeg_inert v hv w hw] at hf
      exact hγ2 w.1 hk v w.2 hs (p w.1) (hpD _ hk) _ f (hh _ hk) hf
    · rw [if_neg hk] at hf
      rw [sph_unique v 1 _ _ hf (sphEx F n hn v).2.1, hh' _ hk]
      have e2 : (fun g => (GLnLocal.integralGL (w.1.adicCompletion E) n : Set _).indicator
          (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ) (cmp w g)) =
          (unitSet E n v).indicator 1 := by
        funext g
        have : g ∈ unitSet E n v ↔ cmp w g ∈ (GLnLocal.integralGL (w.1.adicCompletion E) n : Set _) :=
          ⟨fun hg => hg w, fun hg w' => by rw [hw w']; exact hg⟩
        by_cases hg : g ∈ unitSet E n v
        · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (this.1 hg)]; rfl
        · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt this.2 hg)]
      rw [e2]
      exact hU F E σ hσ hp n hn v hv
