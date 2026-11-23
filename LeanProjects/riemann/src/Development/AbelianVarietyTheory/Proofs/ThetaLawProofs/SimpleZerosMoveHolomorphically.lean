import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

open Filter Topology

namespace GlobalTheory.HolZeros

noncomputable def coords {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) :
    (Fin g → ℝ) × (Fin g → ℝ) :=
  ((fun i => (w i).re) - (τ.map Complex.re).mulVec
      ((τ.map Complex.im)⁻¹.mulVec fun i => (w i).im),
    (τ.map Complex.im)⁻¹.mulVec fun i => (w i).im)

noncomputable def comb {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : (Fin g → ℝ) × (Fin g → ℝ)) :
    Fin g → ℂ :=
  (fun i => (x.1 i : ℂ)) + τ.mulVec (fun i => (x.2 i : ℂ))

theorem re_comb {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : (Fin g → ℝ) × (Fin g → ℝ)) :
    (fun i => (comb τ x i).re) = x.1 + (τ.map Complex.re).mulVec x.2 := by
  ext i
  simp [comb, Matrix.mulVec, dotProduct]

theorem im_comb {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : (Fin g → ℝ) × (Fin g → ℝ)) :
    (fun i => (comb τ x i).im) = (τ.map Complex.im).mulVec x.2 := by
  ext i
  simp [comb, Matrix.mulVec, dotProduct]

theorem coords_comb {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit (τ.map Complex.im).det)
    (x : (Fin g → ℝ) × (Fin g → ℝ)) : coords τ (comb τ x) = x := by
  simp only [coords, re_comb, im_comb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h,
    Matrix.one_mulVec]
  ext1
  · simp
  · rfl

theorem comb_coords {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit (τ.map Complex.im).det)
    (w : Fin g → ℂ) : comb τ (coords τ w) = w := by
  have h1 := re_comb τ (coords τ w)
  have h2 := im_comb τ (coords τ w)
  simp only [coords, sub_add_cancel] at h1
  simp only [coords, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec] at h2
  ext i
  exact Complex.ext (congrFun h1 i) (congrFun h2 i)

theorem continuousAt_coords {g : ℕ} {P : Type*} [TopologicalSpace P]
    {τ : P → Matrix (Fin g) (Fin g) ℂ} {w : P → Fin g → ℂ} {p : P} (hτ : Continuous τ)
    (hw : ContinuousAt w p) (h : IsUnit ((τ p).map Complex.im).det) :
    ContinuousAt (fun q => coords (τ q) (w q)) p := by
  have him : Continuous fun q => (τ q).map Complex.im := hτ.matrix_map Complex.continuous_im
  have hre : Continuous fun q => (τ q).map Complex.re := hτ.matrix_map Complex.continuous_re
  have hinv : ContinuousAt (fun q => ((τ q).map Complex.im)⁻¹) p := by
    refine ContinuousAt.comp (f := fun q => (τ q).map Complex.im) ?_ him.continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ h.ne_zero
  have hmv : Continuous fun x : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => x.1.mulVec x.2 :=
    continuous_fst.matrix_mulVec continuous_snd
  have hwi : ContinuousAt (fun q i => (w q i).im) p :=
    continuousAt_pi.2 fun i => Complex.continuous_im.continuousAt.comp (continuousAt_pi.1 hw i)
  have hwr : ContinuousAt (fun q i => (w q i).re) p :=
    continuousAt_pi.2 fun i => Complex.continuous_re.continuousAt.comp (continuousAt_pi.1 hw i)
  have hb := hmv.continuousAt.comp (hinv.prodMk hwi)
  exact (hwr.sub (hmv.continuousAt.comp (hre.continuousAt.prodMk hb))).prodMk hb

theorem continuous_comb {g : ℕ} {P : Type*} [TopologicalSpace P]
    {τ : P → Matrix (Fin g) (Fin g) ℂ} {x : P → (Fin g → ℝ) × (Fin g → ℝ)} (hτ : Continuous τ)
    (hx : Continuous x) : Continuous fun q => comb (τ q) (x q) := by
  unfold comb
  exact (by fun_prop : Continuous fun q i => ((x q).1 i : ℂ)).add
    (hτ.matrix_mulVec (by fun_prop))

theorem exists_implicit {g : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [CompleteSpace P] (F : Fin g → P → (Fin g → ℂ) → ℂ) (p₀ : P) (z₀ : Fin g → ℂ)
    (hF : ∀ i, ContDiffAt ℂ 1 (fun q : P × (Fin g → ℂ) => F i q.1 q.2) (p₀, z₀))
    (h0 : ∀ i, F i p₀ z₀ = 0)
    (hd : (Matrix.of fun i k => fderiv ℂ (F i p₀) z₀ (Pi.single k 1)).det ≠ 0) :
    ∃ z : P → Fin g → ℂ, z p₀ = z₀ ∧ (∀ᶠ p in 𝓝 p₀, DifferentiableAt ℂ z p) ∧
      (∀ᶠ p in 𝓝 p₀, ∀ i, F i p (z p) = 0) ∧
      (∀ᶠ p in 𝓝 p₀, (Matrix.of fun i k => fderiv ℂ (F i p) (z p) (Pi.single k 1)).det ≠ 0) ∧
      ∀ᶠ q in 𝓝 (p₀, z₀), (∀ i, F i q.1 q.2 = 0) → z q.1 = q.2 := by
  set f : P × (Fin g → ℂ) → Fin g → ℂ := fun q i => F i q.1 q.2 with hf
  have cdf : ContDiffAt ℂ 1 f (p₀, z₀) := contDiffAt_pi.2 hF
  have key : ∀ q : P × (Fin g → ℂ), DifferentiableAt ℂ f q → ∀ i v,
      fderiv ℂ (F i q.1) q.2 v = fderiv ℂ f q (0, v) i := by
    intro q hq i v
    have h1 := HasFDerivAt.comp (f := fun y => (q.1, y)) q.2
      (hasFDerivAt_pi'.1 hq.hasFDerivAt i) (hasFDerivAt_prodMk_right (𝕜 := ℂ) q.1 q.2)
    have h2 : fderiv ℂ (F i q.1) q.2 = _ := h1.fderiv
    rw [h2]
    simp
  have hinv : (fderiv ℂ f (p₀, z₀) ∘L ContinuousLinearMap.inr ℂ P (Fin g → ℂ)).IsInvertible := by
    set L := fderiv ℂ f (p₀, z₀) ∘L ContinuousLinearMap.inr ℂ P (Fin g → ℂ) with hL
    have hdet : L.det ≠ 0 := by
      rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix' ]
      convert hd using 2
      ext i k
      rw [Matrix.of_apply, key (p₀, z₀) (cdf.differentiableAt one_ne_zero)]
      simp [hL, LinearMap.toMatrix'_apply]
    exact ⟨L.toContinuousLinearEquivOfDetNeZero hdet, rfl⟩
  have hf0 : f (p₀, z₀) = 0 := funext h0
  have hz := cdf.contDiffAt_implicitFunction one_ne_zero hinv
  have hz0 := cdf.implicitFunction_apply_self one_ne_zero hinv
  set z := cdf.implicitFunction one_ne_zero hinv with hzdef
  refine ⟨z, hz0, ?_, ?_, ?_, ?_⟩
  · exact (hz.eventually (by simp)).mono fun p hp => hp.differentiableAt one_ne_zero
  · filter_upwards [cdf.eventually_apply_implicitFunction one_ne_zero hinv] with p hp i
    exact congrFun (hp.trans hf0) i
  · have ht : Tendsto (fun p => (p, z p)) (𝓝 p₀) (𝓝 (p₀, z₀)) := by
      have := (continuousAt_id.prodMk hz.continuousAt).tendsto
      simp only [id] at this hz0
      rwa [hz0] at this
    have hc : ContinuousAt (fderiv ℂ f) (p₀, z₀) := cdf.continuousAt_fderiv one_ne_zero
    have hc2 : ContinuousAt (fun q => (Matrix.of fun i k =>
        fderiv ℂ f q (0, Pi.single k 1) i).det) (p₀, z₀) := by
      refine (continuous_id.matrix_det).continuousAt.comp (f := fun q => (Matrix.of fun i k =>
        fderiv ℂ f q (0, Pi.single k 1) i)) ?_
      refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun k => ?_
      exact continuousAt_pi.1 (hc.clm_apply continuousAt_const) i
    have hne : ∀ᶠ q in 𝓝 (p₀, z₀), (Matrix.of fun i k =>
        fderiv ℂ f q (0, Pi.single k 1) i).det ≠ 0 := by
      refine hc2.eventually_ne ?_
      simpa only [← key (p₀, z₀) (cdf.differentiableAt one_ne_zero)] using hd
    filter_upwards [ht.eventually hne, ht.eventually (cdf.eventually (by simp))] with p h1 h2
    simpa only [← key (p, z p) (h2.differentiableAt one_ne_zero)] using h1
  · filter_upwards [cdf.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv] with q hq h
    exact hq.1 ((funext h).trans hf0.symm)

theorem comb_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x y : (Fin g → ℝ) × (Fin g → ℝ)) :
    comb τ (x + y) = comb τ x + comb τ y := by
  ext i
  simp [comb, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  ring

theorem comb_int {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (m m' : Fin g → ℤ) :
    comb τ (fun i => (m i : ℝ), fun i => (m' i : ℝ)) =
      (fun i => (m i : ℂ)) + τ.mulVec (fun i => (m' i : ℂ)) := by
  simp [comb]

theorem IsLevel.zero_iff {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} {n : ℕ}
    {F : (Fin g → ℂ) → ℂ} (h : IsLevel τ a b n F) (m m' : Fin g → ℤ) (z : Fin g → ℂ) :
    F (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (m' i : ℂ)))) = 0 ↔ F z = 0 := by
  rw [h.2, mul_eq_zero, or_iff_right (pow_ne_zero _ (Complex.exp_ne_zero _))]

theorem simple_zeros_move_holomorphically :
    ∀ (g n d : ℕ) (a b : Fin g → ℂ) (F : Fin g → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ) (p₀ : (Fin g → Fin g → ℂ)) (z₀ : Fin d → Fin g → ℂ), p₀ ∈ Key.phDom g → (∀ i, HolFam (Key.phDom g) (F i)) → (∀ i, ∀ p ∈ Key.phDom g, IsLevel (per p) a b n (F i p)) → let Good : (Fin g → Fin g → ℂ) → (Fin d → Fin g → ℂ) → Prop := fun p z => (∀ e i, F i p (z e) = 0) ∧ (∀ e, (Matrix.of fun i k => fderiv ℂ (F i p) (z e) (Pi.single k 1)).det ≠ 0) ∧ (∀ e e' (m m' : Fin g → ℤ), z e = z e' + ((fun i => (m i : ℂ)) + (per p).mulVec (fun i => (m' i : ℂ))) → e = e') ∧ ∀ y, (∀ i, F i p y = 0) → ∃ (e : Fin d) (m m' : Fin g → ℤ), y = z e + ((fun i => (m i : ℂ)) + (per p).mulVec (fun i => (m' i : ℂ))); Good p₀ z₀ → ∃ (W : Set (Fin g → Fin g → ℂ)) (z : (Fin g → Fin g → ℂ) → Fin d → Fin g → ℂ), IsOpen W ∧ p₀ ∈ W ∧ W ⊆ Key.phDom g ∧ z p₀ = z₀ ∧ DifferentiableOn ℂ z W ∧ ∀ p ∈ W, Good p (z p) := by
  intro g n d a b F p₀ z₀ hp₀ hF hL Good hG
  obtain ⟨h0, hd, hdist, hex⟩ := hG
  have hdom : Key.phDom g ∈ 𝓝 p₀ := (GlobalTheory.isOpen_phDom g).mem_nhds hp₀
  have hcd : ∀ i y, ContDiffAt ℂ 1
      (fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) => F i q.1 q.2) (p₀, y) := fun i y =>
    GlobalTheory.SCV.contDiffAt_of_differentiableOn (hF i) (prod_mem_nhds hdom univ_mem) 1
  choose ζ hζ0 hζd hζz hζj hζu using fun e =>
    exists_implicit F p₀ (z₀ e) (fun i => hcd i _) (h0 e) (hd e)
  have hτ : Continuous fun p : Fin g → Fin g → ℂ => per p :=
    GlobalTheory.differentiable_phSym_coords.continuous
  have hun : ∀ p ∈ Key.phDom g, IsUnit ((per p).map Complex.im).det := fun p hp =>
    (Matrix.isUnit_iff_isUnit_det _).1 hp.2.isUnit

  have hS : IsClosed {x : (Fin g → ℝ) × (Fin g → ℝ) | ∀ i,
      x.1 i ∈ Set.range ((↑) : ℤ → ℝ) ∧ x.2 i ∈ Set.range ((↑) : ℤ → ℝ)} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => IsClosed.inter ?_ ?_
    · exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage
        (f := fun x : (Fin g → ℝ) × (Fin g → ℝ) => x.1 i) (by fun_prop)
    · exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage
        (f := fun x : (Fin g → ℝ) × (Fin g → ℝ) => x.2 i) (by fun_prop)
  have hD : ∀ e e', ∀ᶠ p in 𝓝 p₀, ∀ m m' : Fin g → ℤ, ζ e p = ζ e' p +
      ((fun i => (m i : ℂ)) + (per p).mulVec (fun i => (m' i : ℂ))) → e = e' := by
    intro e e'
    by_cases hee : e = e'
    · exact Eventually.of_forall fun _ _ _ _ => hee
    have hc := continuousAt_coords (w := fun p => ζ e p - ζ e' p) hτ
      ((hζd e).self_of_nhds.continuousAt.sub (hζd e').self_of_nhds.continuousAt) (hun p₀ hp₀)
    have hn : coords (per p₀) (ζ e p₀ - ζ e' p₀) ∈ {x : (Fin g → ℝ) × (Fin g → ℝ) | ∀ i,
        x.1 i ∈ Set.range ((↑) : ℤ → ℝ) ∧ x.2 i ∈ Set.range ((↑) : ℤ → ℝ)}ᶜ := by
      intro h
      choose m hm using fun i => (h i).1
      choose m' hm' using fun i => (h i).2
      refine hee (hdist e e' m m' ?_)
      have h1 : coords (per p₀) (ζ e p₀ - ζ e' p₀) = (fun i => (m i : ℝ), fun i => (m' i : ℝ)) :=
        Prod.ext (funext fun i => (hm i).symm) (funext fun i => (hm' i).symm)
      rw [← comb_int, ← h1, comb_coords (hun p₀ hp₀), hζ0, hζ0, add_sub_cancel]
    filter_upwards [hc.eventually (hS.isOpen_compl.mem_nhds hn), hdom] with p hp hpd m m' h
    refine absurd ?_ hp
    rw [h, add_sub_cancel_left, ← comb_int, coords_comb (hun p hpd)]
    exact fun i => ⟨⟨m i, rfl⟩, ⟨m' i, rfl⟩⟩

  have hK : IsCompact (Set.Icc (0 : (Fin g → ℝ) × (Fin g → ℝ)) 1) := isCompact_Icc
  have hcc : Continuous fun q : (Fin g → Fin g → ℂ) × ((Fin g → ℝ) × (Fin g → ℝ)) =>
      comb (per q.1) q.2 := continuous_comb (hτ.comp continuous_fst) continuous_snd
  have hE : ∀ᶠ p in 𝓝 p₀, ∀ x ∈ Set.Icc (0 : (Fin g → ℝ) × (Fin g → ℝ)) 1,
      (∀ i, F i p (comb (per p) x) = 0) → ∃ (e : Fin d) (m m' : Fin g → ℤ), comb (per p) x =
        ζ e p + ((fun i => (m i : ℂ)) + (per p).mulVec (fun i => (m' i : ℂ))) := by
    refine hK.eventually_forall_of_forall_eventually fun x₀ _ => ?_
    by_cases hz : ∀ i, F i p₀ (comb (per p₀) x₀) = 0
    · obtain ⟨e, m, m', he⟩ := hex _ hz
      have hc2 : Continuous fun q : (Fin g → Fin g → ℂ) × ((Fin g → ℝ) × (Fin g → ℝ)) =>
          (q.1, comb (per q.1) q.2 -
            comb (per q.1) (fun i => (m i : ℝ), fun i => (m' i : ℝ))) :=
        continuous_fst.prodMk (hcc.sub (continuous_comb (hτ.comp continuous_fst) continuous_const))
      have ht := hc2.tendsto (p₀, x₀)
      simp only [comb_int, he, add_sub_cancel_right] at ht
      filter_upwards [ht.eventually (hζu e), continuousAt_fst.eventually
        (show ∀ᶠ p in 𝓝 (p₀, x₀).1, p ∈ Key.phDom g from hdom)] with q hq hqd hq0
      refine ⟨e, m, m', ?_⟩
      rw [hq fun i => ?_, sub_add_cancel]
      rw [← IsLevel.zero_iff (hL i q.1 hqd) m m', sub_add_cancel]
      exact hq0 i
    · push Not at hz
      obtain ⟨i, hi⟩ := hz
      have hc : ContinuousAt (fun q : (Fin g → Fin g → ℂ) × ((Fin g → ℝ) × (Fin g → ℝ)) =>
          F i q.1 (comb (per q.1) q.2)) (p₀, x₀) :=
        ContinuousAt.comp (f := fun q : (Fin g → Fin g → ℂ) × ((Fin g → ℝ) × (Fin g → ℝ)) =>
          (q.1, comb (per q.1) q.2)) (x := (p₀, x₀)) (hcd i (comb (per p₀) x₀)).continuousAt
          (continuous_fst.prodMk hcc).continuousAt
      filter_upwards [hc.eventually_ne hi] with q hq h
      exact absurd (h i) hq
  have hall : ∀ᶠ p in 𝓝 p₀, p ∈ Key.phDom g ∧ DifferentiableAt ℂ (fun p e => ζ e p) p ∧
      Good p (fun e => ζ e p) := by
    filter_upwards [hdom, eventually_all.2 hζd, eventually_all.2 hζz, eventually_all.2 hζj,
      eventually_all.2 fun e => eventually_all.2 (hD e), hE] with p hp h1 h2 h3 h4 h5
    refine ⟨hp, differentiableAt_pi.2 h1, h2, h3, h4, fun y hy => ?_⟩
    set c := coords (per p) y with hc
    let x : (Fin g → ℝ) × (Fin g → ℝ) := (fun i => Int.fract (c.1 i), fun i => Int.fract (c.2 i))
    have hy' : y = comb (per p) x + ((fun i => ((⌊c.1 i⌋ : ℤ) : ℂ)) +
        (per p).mulVec (fun i => ((⌊c.2 i⌋ : ℤ) : ℂ))) := by
      rw [← comb_int, ← comb_add, ← comb_coords (hun p hp) y, ← hc]
      congr 1
      ext i <;> simp [x]
    obtain ⟨e, m, m', he⟩ := h5 x
      ⟨⟨fun i => Int.fract_nonneg _, fun i => Int.fract_nonneg _⟩,
        ⟨fun i => (Int.fract_lt_one _).le, fun i => (Int.fract_lt_one _).le⟩⟩ fun i => by
      rw [← IsLevel.zero_iff (hL i p hp) (fun i => ⌊c.1 i⌋) (fun i => ⌊c.2 i⌋), ← hy']
      exact hy i
    refine ⟨e, fun i => m i + ⌊c.1 i⌋, fun i => m' i + ⌊c.2 i⌋, ?_⟩
    rw [hy', he, add_assoc, ← comb_int, ← comb_int, ← comb_int, ← comb_add]
    congr 2
    ext i <;> simp
  obtain ⟨W, hW, hWo, hW0⟩ := eventually_nhds_iff.1 hall
  exact ⟨W, fun p e => ζ e p, hWo, hW0, fun p hp => (hW p hp).1, funext hζ0,
    fun p hp => (hW p hp).2.1.differentiableWithinAt, fun p hp => (hW p hp).2.2⟩

end GlobalTheory.HolZeros
