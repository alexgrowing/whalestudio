import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.WhittakerHecke.RatIdeleAbsRealIdeleNatIdeleUnitIdeles
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.EulReal
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

noncomputable section
namespace UpperTheory.FacI
private abbrev PE := IdeleGroup.prodEquiv ℚ
private def rv (a : (InfiniteAdeleRing ℚ)ˣ) : ℝ := ((Ad3.GP.aR a : ℝˣ) : ℝ)

private theorem map_val : Measure.map (Units.val : ℝˣ → ℝ) Ad3.mulR =
    volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by
  have he := GroundTheory.Global.measurableEmbedding_units_val (F := ℝ)
  have hr : Set.range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      simp
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  have hac : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹) ≪ volume :=
    withDensity_absolutelyContinuous _ _
  have h0 : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹) {0} = 0 := hac (by simp)
  rw [Ad3.mulR, he.map_comap, hr]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  simpa using h0

private theorem measEmb_rv : MeasurableEmbedding rv :=
  (GroundTheory.Global.measurableEmbedding_units_val (F := ℝ)).comp Ad3.GP.measurableEmbedding_aR

private theorem map_rv : Measure.map rv (infiniteIdeleMeasure ℚ) =
    volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by
  have h1 := Ad3.GP.measurableEmbedding_aR.measurable
  have h2 := (GroundTheory.Global.measurableEmbedding_units_val (F := ℝ)).measurable
  rw [← map_val, ← Ad3.GP.map_aR, Measure.map_map h2 h1]
  rfl

private theorem integrable_rv {g : ℝ → ℂ} (h : Integrable (fun x : ℝ => g x / ((|x| : ℝ) : ℂ))) :
    Integrable (fun a => g (rv a)) (infiniteIdeleMeasure ℚ) := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by fun_prop
  have h1 : Integrable g (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹) := by
    rw [integrable_withDensity_iff_integrable_smul' hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg x)), Complex.real_smul]
    push_cast
    rw [div_eq_inv_mul]
  rw [← map_rv] at h1
  exact measEmb_rv.integrable_map_iff.1 h1

private theorem integral_rv (g : ℝ → ℂ) :
    ∫ a, g (rv a) ∂(infiniteIdeleMeasure ℚ) = ∫ x : ℝ, g x / ((|x| : ℝ) : ℂ) := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by fun_prop
  rw [← measEmb_rv.integral_map (g := g), map_rv,
    integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg x)), Complex.real_smul]
  push_cast
  rw [div_eq_inv_mul]

private theorem iy_rv (a : (InfiniteAdeleRing ℚ)ˣ) : iy (rv a) = PE.symm (a, 1) := by
  have h0 : rv a ≠ 0 := (Ad3.GP.aR a).ne_zero
  apply Units.ext
  refine Prod.ext ?_ ?_
  · simp only [iy, dif_neg h0]
    change (1 : InfiniteAdeleRing ℚ) - TR.infEq ℚ 1 + TR.infEq ℚ (fun _ => rv a) = (a : InfiniteAdeleRing ℚ)
    rw [map_one, sub_self, zero_add]
    funext w
    rw [Subsingleton.elim w Ad3.GP.wR]
    exact (Ad3.GP.eR.symm_apply_apply _)
  · simp only [iy, dif_neg h0]
    change (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) - 0 + 0 = 1
    rw [sub_zero, add_zero]

private theorem exists_rv (r : ℝ) (h : r ≠ 0) : ∃ a, rv a = r := by
  refine ⟨Ad3.GP.aRh.symm (Units.mk0 r h), ?_⟩
  have : Ad3.GP.aR (Ad3.GP.aRh.symm (Units.mk0 r h)) = Units.mk0 r h := by
    rw [← Ad3.GP.coe_aRh]
    exact Ad3.GP.aRh.apply_symm_apply _
  simp [rv, this]

private def TF (L : ℕ) : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := (fun u => PE.symm (1, u)) ⁻¹' TT L

private def ev (v : H.P ℚ) (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : H.Kv v := H.cp v ((PE.symm (1, u) : IdeleGroup ℚ) : A ℚ)

private theorem continuous_ev (v : H.P ℚ) : Continuous (ev v) := by
  have hf : Continuous (H.cp v) := by
    show Continuous (fun x => pLoc ℚ v (pFin ℚ x))
    exact (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact hf.comp (Units.continuous_val.comp (PE.symm.continuous.comp (Continuous.prodMk_right 1)))

private theorem mem_TF {L : ℕ} {u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} :
    u ∈ TF L ↔ ∀ v : H.P ℚ, Valued.v (ev v u) = 1 ∧ Valued.v (ev v u - 1) ≤ Valued.v ((L : ℕ) : H.Kv v) := by
  constructor
  · rintro ⟨⟨_, h1⟩, h2⟩ v
    refine ⟨h1 v, ?_⟩
    have := h2 v
    rw [Dv, map_sub, map_one] at this
    exact this
  · intro h
    refine ⟨⟨rfl, fun v => (h v).1⟩, fun v => ?_⟩
    rw [Dv, map_sub, map_one]
    exact (h v).2

private theorem isClosed_TF {L : ℕ} (hL : 0 < L) : IsClosed (TF L) := by
  have e : TF L = ⋂ v : H.P ℚ, ({u | Valued.v (ev v u) = 1} ∩ {u | Valued.v (ev v u - 1) ≤ Valued.v ((L : ℕ) : H.Kv v)}) := by
    ext u
    simp only [mem_TF, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [e]
  refine isClosed_iInter fun v => IsClosed.inter ?_ ?_
  · have := ((Valued.isClopen_sphere (H.Kv v) (r := 1) one_ne_zero).preimage (continuous_ev v)).isClosed
    convert this using 1
    ext u
    simp
  · have hc0 : ((L : ℕ) : H.Kv v) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
    have := ((Valued.isClopen_closedBall (H.Kv v) (r := Valued.v.restrict ((L : ℕ) : H.Kv v)) (by simp [hc0])).preimage
      ((continuous_ev v).sub continuous_const : Continuous fun u => ev v u - 1)).isClosed
    convert this using 1
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.restrict_le_iff]
    exact Iff.rfl

private theorem TF_subset (L : ℕ) : TF L ⊆ finiteIntegralUnits ℚ := by
  intro u hu
  rw [SetLike.mem_coe, mem_finiteIntegralUnits]
  intro v
  have h1 : Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := (mem_TF.1 hu v).1
  have h2 : ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v * (u : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 :=
    congrArg (fun z : FiniteAdeleRing (𝓞 ℚ) ℚ => z v) (Units.inv_mul u)
  have h3 : Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
    have := congrArg Valued.v h2
    rwa [map_mul, h1, mul_one, map_one] at this
  exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h1.le, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h3.le⟩

private theorem measure_TF_lt (L : ℕ) : finiteIdeleMeasure ℚ (TF L) < ⊤ :=
  lt_of_le_of_lt (measure_mono (TF_subset L)) (by rw [finiteIdeleMeasure_finiteIntegralUnits]; simp)

private def WW (L : ℕ) : Set (IdeleGroup ℚ) := PE ⁻¹' (Set.univ ×ˢ TF L)

private theorem symm_mem_WW {L : ℕ} {q : (InfiniteAdeleRing ℚ)ˣ × (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} :
    PE.symm q ∈ WW L ↔ q.2 ∈ TF L := by
  simp [WW, Set.mem_preimage, Set.mem_prod]

private theorem symm_split (q : (InfiniteAdeleRing ℚ)ˣ × (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    PE.symm q = iy (rv q.1) * PE.symm (1, q.2) := by
  rw [iy_rv, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

private theorem core {L : ℕ} (hL : 0 < L) (p : IdeleGroup ℚ) (f : IdeleGroup ℚ → ℂ)
    (hinv : ∀ τ ∈ TT L, ∀ y : IdeleGroup ℚ, f (y * τ) = f y)
    (hint : Integrable (fun r : ℝ => f (iy r * p) / ((|r| : ℝ) : ℂ))) :
    Integrable ((WW L).indicator fun z => f (z * p)) (ideleMeasure ℚ) ∧
      ∫ z, (WW L).indicator (fun z => f (z * p)) z ∂(ideleMeasure ℚ) =
        (cT L : ℂ) * ∫ r : ℝ, f (iy r * p) / ((|r| : ℝ) : ℂ) := by
  have hTm : MeasurableSet (TF L) := (isClosed_TF hL).measurableSet
  set ind : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ := (TF L).indicator fun _ => 1 with hind
  have hG := integrable_rv (g := fun r => f (iy r * p)) hint
  have hI : Integrable ind (finiteIdeleMeasure ℚ) :=
    (integrable_indicator_iff hTm).2 (integrableOn_const (measure_TF_lt L).ne)
  have key : ∀ q, (WW L).indicator (fun z => f (z * p)) (PE.symm q) = f (iy (rv q.1) * p) * ind q.2 := by
    intro q
    by_cases hq : q.2 ∈ TF L
    · rw [Set.indicator_of_mem (symm_mem_WW.2 hq), hind, Set.indicator_of_mem hq, mul_one, symm_split,
        mul_right_comm]
      exact hinv _ hq _
    · rw [Set.indicator_of_notMem (fun h => hq (symm_mem_WW.1 h)), hind, Set.indicator_of_notMem hq, mul_zero]
  have emb : MeasurableEmbedding PE.symm := PE.symm.toHomeomorph.measurableEmbedding
  constructor
  · refine (emb.integrable_map_iff (g := (WW L).indicator fun z => f (z * p))).2 ?_
    have := (hG.mul_prod hI)
    refine this.congr (Eventually.of_forall fun q => ?_)
    exact (key q).symm
  · rw [integral_ideleMeasure]
    simp_rw [key]
    rw [integral_prod_mul (fun a => f (iy (rv a) * p)) ind, integral_rv (fun r => f (iy r * p)), mul_comm]
    congr 1
    rw [hind, integral_indicator hTm, setIntegral_const, Measure.real, cT]
    simp [TF, Measure.real]

private theorem iy_mul_mem_WW {L : ℕ} {r : ℝ} (hr : r ≠ 0) {τ : (A ℚ)ˣ} (hτ : τ ∈ TT L) : iy r * τ ∈ WW L := by
  obtain ⟨a, rfl⟩ := exists_rv r hr
  have h1 : (PE τ).1 = 1 := Units.ext hτ.1.1
  have h2 : PE.symm (1, (PE τ).2) = τ := by
    rw [← h1]
    exact PE.symm_apply_apply τ
  have h3 : iy (rv a) * τ = PE.symm (a, (PE τ).2) := by
    rw [iy_rv, ← h2, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, h2]
  rw [h3, symm_mem_WW]
  show PE.symm (1, (PE τ).2) ∈ TT L
  rw [h2]
  exact hτ

private theorem exists_of_mem_WW {L : ℕ} {z : IdeleGroup ℚ} (hz : z ∈ WW L) :
    ∃ (r : ℝ) (τ : (A ℚ)ˣ), r ≠ 0 ∧ τ ∈ TT L ∧ z = iy r * τ := by
  have e : PE.symm (PE z) = z := PE.symm_apply_apply z
  rw [← e, symm_mem_WW] at hz
  exact ⟨rv (PE z).1, PE.symm (1, (PE z).2), (Ad3.GP.aR _).ne_zero, hz, by rw [← symm_split, e]⟩

private theorem re_of_TT {L : ℕ} {τ : (A ℚ)ˣ} (hτ : τ ∈ TT L) : re (τ : A ℚ) = 1 := by
  show (TR.infEq ℚ).symm ((τ : A ℚ).1) Rat.infinitePlace = 1
  rw [hτ.1.1, map_one]
  rfl

private theorem sep {L n m : ℕ} (hn : 0 < n) (hm : 0 < m) {r r' : ℝ} (hr : r ≠ 0) (hr' : r' ≠ 0) {τ τ' : (A ℚ)ˣ}
    (hτ : τ ∈ TT L) (hτ' : τ' ∈ TT L) (h : iy r * pin n * τ = iy r' * pin m * τ') : n = m := by
  obtain ⟨a1, a2, a3, a4⟩ := UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles
  have hre : ∀ (s : ℝ) (k : ℕ) (σ : (A ℚ)ˣ), s ≠ 0 → 0 < k → σ ∈ TT L → re ((iy s * pin k * σ : (A ℚ)ˣ) : A ℚ) = s := by
    intro s k σ hs hk hσ
    have : re ((iy s * pin k * σ : (A ℚ)ˣ) : A ℚ) = re ((iy s * pin k : (A ℚ)ˣ) : A ℚ) * re (σ : A ℚ) := by
      simp only [re, Units.val_mul (iy s * pin k) σ, map_mul, Pi.mul_apply]
    rw [this, a4 s k hs hk, re_of_TT hσ, mul_one]
  have hab : ∀ (s : ℝ) (k : ℕ) (σ : (A ℚ)ˣ), s ≠ 0 → 0 < k → σ ∈ TT L → ab (iy s * pin k * σ) = |s| * (k : ℝ)⁻¹ := by
    intro s k σ hs hk hσ
    have : ab (iy s * pin k * σ) = ab (iy s) * ab (pin k) * ab σ := by
      simp only [ab, map_mul]
      rfl
    rw [this, a1 s hs, a2 k hk, a3 σ hσ.1, mul_one]
  have e1 : r = r' := by rw [← hre r n τ hr hn hτ, h, hre r' m τ' hr' hm hτ']
  have e2 := hab r n τ hr hn hτ
  rw [h, hab r' m τ' hr' hm hτ', e1] at e2
  have h0 : |r'| ≠ 0 := abs_ne_zero.2 hr'
  have e3 : (m : ℝ)⁻¹ = (n : ℝ)⁻¹ := mul_left_cancel₀ h0 e2
  exact_mod_cast (inv_injective e3).symm

end UpperTheory.FacI

open UpperTheory.FacI in
theorem UpperTheory.hasSum_coprime_integral_eq_idele_integral :
    ∀ (L N : ℕ), 0 < L → ∀ f : IdeleGroup ℚ → ℂ, (∀ τ ∈ TT L, ∀ y : IdeleGroup ℚ, f (y * τ) = f y) →
        (∀ y : IdeleGroup ℚ, f y ≠ 0 → ∃ (n : ℕ) (r : ℝ) (τ : (A ℚ)ˣ), 0 < n ∧ n.Coprime N ∧ r ≠ 0 ∧ τ ∈ TT L ∧ y = iy r * pin n * τ) →
        (∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, Integrable (fun r : ℝ => f (iy r * pin n) / ((|r| : ℝ) : ℂ))) →
        Summable (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ∫ r : ℝ, ‖f (iy r * pin n) / ((|r| : ℝ) : ℂ)‖) →
        HasSum (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => (cT L : ℂ) * ∫ r : ℝ, f (iy r * pin n) / ((|r| : ℝ) : ℂ)) (∫ y, f y ∂(ideleMeasure ℚ)) := by
  intro L N hL f hinv hsupp hint hsum
  let K : {n : ℕ // 0 < n ∧ n.Coprime N} → IdeleGroup ℚ → ℂ := fun n => (WW L).indicator fun z => f (z * pin n)
  let F : {n : ℕ // 0 < n ∧ n.Coprime N} → IdeleGroup ℚ → ℂ := fun n y => K n (y * (pin n)⁻¹)
  have hcore := fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => core hL (pin n) f hinv (hint n)
  have hFint : ∀ n, Integrable (F n) (ideleMeasure ℚ) := fun n => (hcore n).1.comp_mul_right (pin n)⁻¹
  have hFint' : ∀ n, ∫ y, F n y ∂(ideleMeasure ℚ) = (cT L : ℂ) * ∫ r : ℝ, f (iy r * pin n) / ((|r| : ℝ) : ℂ) := fun n => by
    rw [← (hcore n).2]
    exact integral_mul_right_eq_self (K n) (pin n)⁻¹
  have hnorm : ∀ n, ∫ y, ‖F n y‖ ∂(ideleMeasure ℚ) = cT L * ∫ r : ℝ, ‖f (iy r * pin n) / ((|r| : ℝ) : ℂ)‖ := by
    intro n
    have hi : Integrable (fun r : ℝ => (fun y => ((‖f y‖ : ℝ) : ℂ)) (iy r * pin n) / ((|r| : ℝ) : ℂ)) := by
      refine (hint n).norm.ofReal.congr (Eventually.of_forall fun r => ?_)
      simp [abs_abs]
    have hc := (core hL (pin n) (fun y => ((‖f y‖ : ℝ) : ℂ))
      (fun τ hτ y => by simp only [hinv τ hτ y]) hi).2
    have e1 : ∫ y, ‖F n y‖ ∂(ideleMeasure ℚ) = ∫ y, ‖K n y‖ ∂(ideleMeasure ℚ) :=
      integral_mul_right_eq_self (fun z => ‖K n z‖) (pin n)⁻¹
    have e2 : ∀ z, (WW L).indicator (fun z => ((‖f (z * pin n)‖ : ℝ) : ℂ)) z = ((‖K n z‖ : ℝ) : ℂ) := by
      intro z
      by_cases hz : z ∈ WW L
      · simp [K, Set.indicator_of_mem hz]
      · simp [K, Set.indicator_of_notMem hz]
    have e3 : ∀ r : ℝ, ((‖f (iy r * pin n)‖ : ℝ) : ℂ) / ((|r| : ℝ) : ℂ) = ((‖f (iy r * pin n) / ((|r| : ℝ) : ℂ)‖ : ℝ) : ℂ) := by
      intro r
      simp [abs_abs]
    simp_rw [e2, e3] at hc
    rw [integral_complex_ofReal, integral_complex_ofReal] at hc
    rw [e1]
    exact_mod_cast hc
  have hs := hasSum_integral_of_summable_integral_norm hFint (by simp_rw [hnorm]; exact hsum.mul_left _)
  have hsumf : ∀ y, ∑' n, F n y = f y := by
    intro y
    by_cases hy : f y = 0
    · rw [hy]
      convert tsum_zero with n
      show (WW L).indicator (fun z => f (z * pin n)) (y * (pin n)⁻¹) = 0
      by_cases hz : y * (pin n)⁻¹ ∈ WW L
      · rw [Set.indicator_of_mem hz, inv_mul_cancel_right, hy]
      · rw [Set.indicator_of_notMem hz]
    · obtain ⟨n, r, τ, hn, hc, hr, hτ, rfl⟩ := hsupp y hy
      have hmem : iy r * pin n * τ * (pin n)⁻¹ ∈ WW L := by
        have : iy r * pin n * τ * (pin n)⁻¹ = iy r * τ := by
          rw [mul_right_comm, mul_inv_cancel_right]
        rw [this]
        exact iy_mul_mem_WW hr hτ
      rw [tsum_eq_single (⟨n, hn, hc⟩ : {n : ℕ // 0 < n ∧ n.Coprime N})]
      · show (WW L).indicator (fun z => f (z * pin n)) (iy r * pin n * τ * (pin n)⁻¹) = _
        rw [Set.indicator_of_mem hmem, inv_mul_cancel_right]
      · intro m hm
        show (WW L).indicator (fun z => f (z * pin m)) (iy r * pin n * τ * (pin m)⁻¹) = 0
        refine Set.indicator_of_notMem (fun h => hm (Subtype.ext ?_)) _
        obtain ⟨r', τ', hr', hτ', e⟩ := exists_of_mem_WW h
        have e' : iy r * pin n * τ = iy r' * pin m * τ' := by
          rw [mul_right_comm (iy r'), ← e, inv_mul_cancel_right]
        exact (sep hn m.2.1 hr hr' hτ hτ' e').symm
  simp_rw [hFint', hsumf] at hs
  exact hs

end
