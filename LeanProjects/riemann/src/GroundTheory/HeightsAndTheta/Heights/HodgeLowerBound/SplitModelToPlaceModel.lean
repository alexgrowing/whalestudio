import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.EventuallyInFrameDomain
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Example
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped Matrix ComplexOrder

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ} {y : (Σ k, ι k) → Ω}
  {W : ChartBundle ℤ (segreCoord y) N E} {Xo : Set ((Σ k, ι k) → ℂ)}

namespace HermMetric

section ToTwin

variable {P : Ideal (MRing ι)} {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} {χ : Fin nc → SncChart P n Bd}

open Classical in

def gramMatrixInFamily (hA : HermMetric y W Xo χ) (z : (Σ k, ι k) → ℂ) (b : Fin N → E) :
    Matrix (Fin N) (Fin N) ℂ :=
  if hz : ∃ l, InFrameDomain y (hA.chart l) (hA.fr l) z then
    if hS : ∃ S : Matrix (Fin N) (Fin N) Ω, ∀ q, b q = ∑ p, S p q • hA.b hz.choose p then
      (HermMetricEq.valM y hS.choose z)ᴴ * hA.gram hz.choose z * HermMetricEq.valM y hS.choose z
    else 0
  else 0

theorem gramMatrix_change_of_frame (hA : HermMetric y W Xo χ) (hXo : Xo ⊆ mcPts (mCoordIdeal y))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ Xo) {l : Fin hA.m} (hd : InFrameDomain y (hA.chart l) (hA.fr l) z)
    {b : Fin N → E} {S : Matrix (Fin N) (Fin N) Ω}
    (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) z) (hb : ∀ q, b q = ∑ p, S p q • hA.b l p) :
    hA.gramMatrixInFamily z b = (HermMetricEq.valM y S z)ᴴ * hA.gram l z * HermMetricEq.valM y S z := by
  have hzP := hXo hz
  have hex : ∃ l, InFrameDomain y (hA.chart l) (hA.fr l) z := ⟨l, hd⟩
  have hd0 : InFrameDomain y (hA.chart hex.choose) (hA.fr hex.choose) z := hex.choose_spec
  obtain ⟨T, hT, hTe⟩ := HermMetricEq.exists_coeff (hA.isFrame hex.choose) hzP hd0
    (HermMetricEq.isFrameAt_of_isFrameOver (hA.isFrame l) hzP hd).1
  have hbT : ∀ q, b q = ∑ p, (T * S) p q • hA.b hex.choose p := by
    intro q
    rw [hb q]
    simp only [hTe, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => ?_
    rw [mul_comm]
  have hS' : ∃ S' : Matrix (Fin N) (Fin N) Ω, ∀ q, b q = ∑ p, S' p q • hA.b hex.choose p :=
    ⟨T * S, hbT⟩
  have hchoose : hS'.choose = T * S := HermMetricEq.coeff_unique (hA.isFrame hex.choose).2.2.2.1
    fun q => (hS'.choose_spec q).symm.trans (hbT q)
  have hTS : HermMetricEq.valM y (T * S) z = HermMetricEq.valM y T z * HermMetricEq.valM y S z :=
    HermMetricEq.valM_eq hzP (HermMetricEq.isValueAt_mul (fun p q => (hT p q).isValueAt hzP)
      (fun p q => (hS p q).isValueAt hzP))
  have hcompat := hA.compat hex.choose l z hz hd0 hd T hTe (HermMetricEq.valM y T z)
    (fun p q => HermMetricEq.isValueAt_iff.2 ((hT p q).isValueAt hzP))
  rw [gramMatrixInFamily, dif_pos hex, dif_pos hS', hchoose, hTS, hcompat]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

def SmoothAlongHolo (hA : HermMetric y W Xo χ) : Prop :=
  ∀ (m : ℕ) (O : Set (Fin m → ℂ)) (γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ), IsOpen O →
    AnalyticOnNhd ℂ γ O → (∀ w ∈ O, γ w ∈ Xo) → ∀ w ∈ O, ∀ l,
      InFrameDomain y (hA.chart l) (hA.fr l) (γ w) → ∀ p q,
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => hA.gram l (γ w') p q) w

theorem contDiffAt_valAt {m : ℕ} {O : Set (Fin m → ℂ)} {γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ}
    (hO : IsOpen O) (hγ : AnalyticOnNhd ℂ γ O) (hU : ∀ w ∈ O, γ w ∈ mcPts (mCoordIdeal y))
    {w : Fin m → ℂ} (hw : w ∈ O) {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (γ w)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => IndefiniteRowSideFullHecke.LowerBoundFree.valAt y a (γ w')) w := by
  obtain ⟨v, d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  have hcoord : ∀ p, AnalyticAt ℂ (fun w' => γ w' p) w := fun p =>
    ((ContinuousLinearMap.proj p : ((Σ k, ι k) → ℂ) →L[ℂ] ℂ).analyticAt (γ w)).comp (hγ w hw)
  have hG := analyticAt_eval_comp (F := γ) hcoord g
  have hH := analyticAt_eval_comp (F := γ) hcoord h
  have hF : AnalyticAt ℂ (fun w' => eval (γ w') (map (Int.castRingHom ℂ) g) /
      eval (γ w') (map (Int.castRingHom ℂ) h)) w := hG.div hH hz
  have hev : (fun w' => IndefiniteRowSideFullHecke.LowerBoundFree.valAt y a (γ w')) =ᶠ[𝓝 w] fun w' =>
      eval (γ w') (map (Int.castRingHom ℂ) g) / eval (γ w') (map (Int.castRingHom ℂ) h) := by
    have h1 : ∀ᶠ w' in 𝓝 w, eval (γ w') (map (Int.castRingHom ℂ) h) ≠ 0 :=
      hH.continuousAt.eventually_ne hz
    filter_upwards [h1, hO.mem_nhds hw] with w' h1 h2
    exact IndefiniteRowSideFullHecke.LowerBoundFree.valAt_eq (hU w' h2)
      ⟨d, g, h, hg, hh, hy, hyg, h1, by rw [div_mul_cancel₀ _ h1]⟩
  exact (hF.contDiffAt.restrict_scalars ℝ).congr_of_eventuallyEq hev

def toIndefiniteRowSideFullHecke (hA : HermMetric y W Xo χ) (hXo : Xo ⊆ mcPts (mCoordIdeal y)) (hsm : hA.SmoothAlongHolo) :
    IndefiniteRowSideFullHecke.LowerBoundFree.HermMetricOn y W Xo where
  H := hA.gramMatrixInFamily
  posDef z hz b hb := by
    have hzP := hXo hz
    obtain ⟨l, hd⟩ := hA.cover z hz
    obtain ⟨S, hS, hSe⟩ := HermMetricEq.exists_coeff (hA.isFrame l) hzP hd hb.1
    choose U hU hUe using fun q =>
      hb.2 _ ((HermMetricEq.isFrameAt_of_isFrameOver (hA.isFrame l) hzP hd).1 q)
    have hSU : S * Matrix.of (fun p q => U q p) = 1 := by
      refine HermMetricEq.coeff_unique (hA.isFrame l).2.2.2.1 fun q => ?_
      have h1 : ∑ p, (1 : Matrix (Fin N) (Fin N) Ω) p q • hA.b l p = hA.b l q := by
        simp [Matrix.one_apply, ite_smul]
      rw [h1]
      conv_rhs => rw [hUe q]
      simp only [hSe, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => ?_
      rw [mul_comm]
    have hval : HermMetricEq.valM y S z * HermMetricEq.valM y (Matrix.of fun p q => U q p) z = 1 := by
      ext p q
      have h1 := HermMetricEq.isValueAt_mul (Sz := HermMetricEq.valM y S z)
        (Tz := HermMetricEq.valM y (Matrix.of fun p q => U q p) z)
        (fun p q => (hS p q).isValueAt hzP) (fun p q => (hU q p).isValueAt hzP) p q
      rw [hSU] at h1
      exact IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hzP h1 (HermMetricEq.isValueAt_one_matrix p q)
    have hinj : Function.Injective (HermMetricEq.valM y S z).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hval))
    rw [gramMatrix_change_of_frame hA hXo hz hd hS hSe]
    exact (hA.posDef l z hz hd).conjTranspose_mul_mul_same hinj
  frameChange z hz b g gz hb hg _ := by
    have hzP := hXo hz
    obtain ⟨l, hd⟩ := hA.cover z hz
    obtain ⟨S, hS, hSe⟩ := HermMetricEq.exists_coeff (hA.isFrame l) hzP hd hb.1
    have hSg : ∀ q, (∑ p, g p q • b p) = ∑ p, (S * g) p q • hA.b l p := by
      intro q
      simp only [hSe, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => ?_
      rw [mul_comm]
    have hv := HermMetricEq.isValueAt_mul (Sz := HermMetricEq.valM y S z)
      (fun p q => (hS p q).isValueAt hzP) hg
    have hreg : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y ((S * g) p q) z := fun p q => ⟨_, hv p q⟩
    rw [gramMatrix_change_of_frame hA hXo hz hd hreg (b := fun q => ∑ p, g p q • b p) hSg, gramMatrix_change_of_frame hA hXo hz hd hS hSe,
      HermMetricEq.valM_eq hzP hv]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  scale z hz s hs hsz b hb := by
    have hzP := hXo hz
    obtain ⟨l, hd⟩ := hA.cover z hz
    obtain ⟨S, hS, hSe⟩ := HermMetricEq.exists_coeff (hA.isFrame l) hzP hd hb.1
    have hd' := HermMetricEq.inFrameDomain_smul s hs hd
    have hS' : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) (fun p => s p.1 * z p) :=
      fun p q => HermMetricEq.regularAt_smul s hs (hS p q)
    have hv : HermMetricEq.valM y S (fun p => s p.1 * z p) = HermMetricEq.valM y S z :=
      HermMetricEq.valM_eq (hXo hsz) fun p q => ((hS p q).isValueAt hzP).smul s hs
    have ht : hA.gram l (fun p => s p.1 * z p) = hA.gram l z := hA.torus l z hz hd s hs
    rw [gramMatrix_change_of_frame hA hXo hsz hd' hS' hSe, gramMatrix_change_of_frame hA hXo hz hd hS hSe, hv, ht]
  conj z hz hcz b hb := by
    have hzP := hXo hz
    obtain ⟨l, hd⟩ := hA.cover z hz
    obtain ⟨S, hS, hSe⟩ := HermMetricEq.exists_coeff (hA.isFrame l) hzP hd hb.1
    have hd' := HermMetricEq.inFrameDomain_conj hd
    have hS' : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) (fun p => starRingEnd ℂ (z p)) :=
      fun p q => HermMetricEq.regularAt_conj (hS p q)
    have hv : HermMetricEq.valM y S (fun p => starRingEnd ℂ (z p)) =
        (HermMetricEq.valM y S z).map (starRingEnd ℂ) :=
      HermMetricEq.valM_eq (hXo hcz) fun p q => ((hS p q).isValueAt hzP).conj
    have ht : hA.gram l (fun p => starRingEnd ℂ (z p)) = (hA.gram l z).map (starRingEnd ℂ) :=
      hA.conj l z hz hd
    rw [gramMatrix_change_of_frame hA hXo hcz hd' hS' hSe, gramMatrix_change_of_frame hA hXo hz hd hS hSe, hv, ht]
    ext p q
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]
  smooth m O γ hO hγ hγU w hw b hb p q := by
    have hU : ∀ w ∈ O, γ w ∈ mcPts (mCoordIdeal y) := fun w hw => hXo (hγU w hw)
    obtain ⟨l, hd⟩ := hA.cover _ (hγU w hw)
    obtain ⟨S, hS, hSe⟩ := HermMetricEq.exists_coeff (hA.isFrame l) (hU w hw) hd hb.1
    have hcont : ContinuousAt γ w := (hγ w hw).continuousAt
    have hev : ∀ᶠ w' in 𝓝 w, w' ∈ O ∧ InFrameDomain y (hA.chart l) (hA.fr l) (γ w') ∧
        ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) (γ w') := by
      filter_upwards [hO.mem_nhds hw, HermMetricEq.eventually_inFrameDomain hcont hd,
        Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q =>
          HermMetricEq.eventually_regularAt hcont (hS p q)] with w' h1 h2 h3
      exact ⟨h1, h2, h3⟩
    have heq : (fun w' => hA.gramMatrixInFamily (γ w') b p q) =ᶠ[𝓝 w] fun w' =>
        ((HermMetricEq.valM y S (γ w'))ᴴ * hA.gram l (γ w') * HermMetricEq.valM y S (γ w')) p q := by
      filter_upwards [hev] with w' hw'
      obtain ⟨h1, h2, h3⟩ := hw'
      rw [gramMatrix_change_of_frame hA hXo (hγU w' h1) h2 h3 hSe]
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq
    have hval : ∀ a : Ω, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (γ w) →
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => IndefiniteRowSideFullHecke.LowerBoundFree.valAt y a (γ w')) w :=
      fun a ha => contDiffAt_valAt hO hγ hU hw ha
    have hcv : ∀ a : Ω, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (γ w) →
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w' => star (IndefiniteRowSideFullHecke.LowerBoundFree.valAt y a (γ w'))) w := by
      intro a ha
      have hc := (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt.comp w
        (hval a ha)
      have hfun : (fun x => star (IndefiniteRowSideFullHecke.LowerBoundFree.valAt y a (γ x))) =
          Complex.conjCLE ∘ fun w' => IndefiniteRowSideFullHecke.LowerBoundFree.valAt y a (γ w') := by
        funext x
        simp
      rw [hfun]
      exact hc
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, HermMetricEq.valM, Matrix.of_apply]
    exact ContDiffAt.sum fun r _ => ContDiffAt.mul (ContDiffAt.sum fun s _ =>
      ContDiffAt.mul (hcv _ (hS s p)) (hsm m O γ hO hγ hγU w hw l hd s r)) (hval _ (hS r q))

theorem metricOn_gram_eq (hA : HermMetric y W Xo χ) (hXo : Xo ⊆ mcPts (mCoordIdeal y))
    (hsm : hA.SmoothAlongHolo) (l : Fin hA.m) {z : (Σ k, ι k) → ℂ} (hz : z ∈ Xo)
    (hd : InFrameDomain y (hA.chart l) (hA.fr l) z) :
    (hA.toIndefiniteRowSideFullHecke hXo hsm).H z (hA.b l) = hA.gram l z := by
  have h1 : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y ((1 : Matrix (Fin N) (Fin N) Ω) p q) z :=
    fun p q => ⟨_, HermMetricEq.isValueAt_one_matrix p q⟩
  have hb : ∀ q, hA.b l q = ∑ p, (1 : Matrix (Fin N) (Fin N) Ω) p q • hA.b l p := fun q => by
    simp [Matrix.one_apply, ite_smul]
  show hA.gramMatrixInFamily z (hA.b l) = _
  rw [gramMatrix_change_of_frame hA hXo hz hd h1 hb,
    HermMetricEq.valM_eq (hXo hz) (HermMetricEq.isValueAt_one_matrix (y := y) (z := z))]
  simp

end ToTwin

section OfTwin

theorem subset_of_open (hopen : ∃ V : Set ((Σ k, ι k) → ℂ), IsOpen V ∧ Xo = mcPts (mCoordIdeal y) ∩ V) :
    Xo ⊆ mcPts (mCoordIdeal y) := by
  obtain ⟨V, -, hV⟩ := hopen
  rw [hV]
  exact Set.inter_subset_left

def split_model_to_place_model (hB : IndefiniteRowSideFullHecke.LowerBoundFree.HermMetricOn y W Xo)
    (hopen : ∃ V : Set ((Σ k, ι k) → ℂ), IsOpen V ∧ Xo = mcPts (mCoordIdeal y) ∩ V)
    (htorus : ∀ z ∈ Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ Xo)
    (hconj : ∀ z ∈ Xo, conjVec z ∈ Xo)
    {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} (χ : Fin nc → SncChart (mCoordIdeal y) n Bd)
    (m : ℕ) (chart : Fin m → (k : K) → ι k) (fr : Fin m → Ω) (b : Fin m → Fin N → E)
    (isFrame : ∀ l, IsFrameOver y W (chart l) (fr l) (b l))
    (cover : ∀ z ∈ Xo, ∃ l, InFrameDomain y (chart l) (fr l) z)
    (logBound : ∀ a, ∀ t₀ : Fin n → ℂ, ‖t₀‖ ≤ 1 / 2 →
      ∃ l, InFrameDomain y (chart l) (fr l) ((χ a).γ t₀) ∧
      ∃ ε > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ t : Fin n → ℂ, ‖t - t₀‖ < ε → ‖t‖ < 1 →
        (χ a).γ t ∈ Xo → InFrameDomain y (chart l) (fr l) ((χ a).γ t) →
        ((hB.H ((χ a).γ t) (b l))⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef ∧
        (((C * (χ a).logR t : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
          (hB.H ((χ a).γ t) (b l))⁻¹).PosSemidef ∧
        ∀ p q, ‖fderiv ℝ (fun t' => hB.H ((χ a).γ t') (b l) p q) t‖ ≤
          C * Real.exp ((χ a).logR t / 2)) :
    HermMetric y W Xo χ where
  m := m
  chart := chart
  fr := fr
  b := b
  isFrame := isFrame
  gram l z := hB.H z (b l)
  cover := cover
  posDef l z hz hd := hB.posDef z hz _
    (HermMetricEq.isFrameAt_of_isFrameOver (isFrame l) (subset_of_open hopen hz) hd)
  compat l l' z hz hd hd' S hS Sz hSz := by
    have hb' : (fun q => ∑ p, S p q • b l p) = b l' := funext fun q => (hS q).symm
    have h := hB.frameChange z hz (b l) S Sz
      (HermMetricEq.isFrameAt_of_isFrameOver (isFrame l) (subset_of_open hopen hz) hd)
      (fun p q => HermMetricEq.isValueAt_iff.1 (hSz p q))
      (by rw [hb']; exact HermMetricEq.isFrameAt_of_isFrameOver (isFrame l') (subset_of_open hopen hz) hd')
    rw [hb'] at h
    exact h
  torus l z hz hd c hc := hB.scale z hz c hc (htorus z hz c hc) (b l)
    (HermMetricEq.isFrameAt_of_isFrameOver (isFrame l) (subset_of_open hopen hz) hd)
  conj l z hz hd := hB.conj z hz (hconj z hz) (b l)
    (HermMetricEq.isFrameAt_of_isFrameOver (isFrame l) (subset_of_open hopen hz) hd)
  smooth a l t ht hγt hd p q := by
    obtain ⟨V, hV, hXoV⟩ := hopen
    have hO : IsOpen (Metric.ball (0 : Fin n → ℂ) 1 ∩ (χ a).γ ⁻¹' V) :=
      (χ a).analytic.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hV
    have hγO : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1 ∩ (χ a).γ ⁻¹' V, (χ a).γ w ∈ Xo := by
      intro w hw
      rw [hXoV]
      exact ⟨(χ a).mem w hw.1, hw.2⟩
    have htO : t ∈ Metric.ball (0 : Fin n → ℂ) 1 ∩ (χ a).γ ⁻¹' V := by
      refine ⟨ht, ?_⟩
      have h := hγt
      rw [hXoV] at h
      exact h.2
    have hzP : (χ a).γ t ∈ mcPts (mCoordIdeal y) := (χ a).mem t ht
    exact hB.smooth n _ (χ a).γ hO ((χ a).analytic.mono Set.inter_subset_left) hγO t htO (b l)
      (HermMetricEq.isFrameAt_of_isFrameOver (isFrame l) hzP hd) p q
  logBound := logBound

theorem logBound_metricOn {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)}
    {χ : Fin nc → SncChart (mCoordIdeal y) n Bd} (hA : HermMetric y W Xo χ)
    (hopen : ∃ V : Set ((Σ k, ι k) → ℂ), IsOpen V ∧ Xo = mcPts (mCoordIdeal y) ∩ V)
    (hsm : hA.SmoothAlongHolo) :
    ∀ a, ∀ t₀ : Fin n → ℂ, ‖t₀‖ ≤ 1 / 2 →
      ∃ l, InFrameDomain y (hA.chart l) (hA.fr l) ((χ a).γ t₀) ∧
      ∃ ε > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ t : Fin n → ℂ, ‖t - t₀‖ < ε → ‖t‖ < 1 →
        (χ a).γ t ∈ Xo → InFrameDomain y (hA.chart l) (hA.fr l) ((χ a).γ t) →
        (((hA.toIndefiniteRowSideFullHecke (subset_of_open hopen) hsm).H ((χ a).γ t) (hA.b l))⁻¹ -
          (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef ∧
        (((C * (χ a).logR t : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
          ((hA.toIndefiniteRowSideFullHecke (subset_of_open hopen) hsm).H ((χ a).γ t) (hA.b l))⁻¹).PosSemidef ∧
        ∀ p q, ‖fderiv ℝ (fun t' => (hA.toIndefiniteRowSideFullHecke (subset_of_open hopen) hsm).H ((χ a).γ t') (hA.b l) p q) t‖ ≤
          C * Real.exp ((χ a).logR t / 2) := by
  intro a t₀ ht₀
  obtain ⟨l, hd₀, ε, hε, c, hc, C, hC, hb⟩ := hA.logBound a t₀ ht₀
  refine ⟨l, hd₀, ε, hε, c, hc, C, hC, fun t h1 h2 h3 h4 => ?_⟩
  have hH := metricOn_gram_eq hA (subset_of_open hopen) hsm l h3 h4
  obtain ⟨hb1, hb2, hb3⟩ := hb t h1 h2 h3 h4
  refine ⟨by rw [hH]; exact hb1, by rw [hH]; exact hb2, fun p q => ?_⟩
  have ht : t ∈ Metric.ball (0 : Fin n → ℂ) 1 := by rwa [mem_ball_zero_iff]
  have hcont : ContinuousAt (χ a).γ t := ((χ a).analytic t ht).continuousAt
  obtain ⟨V, hV, hXoV⟩ := id hopen
  have hev : ∀ᶠ t' in 𝓝 t, (χ a).γ t' ∈ Xo ∧
      InFrameDomain y (hA.chart l) (hA.fr l) ((χ a).γ t') := by
    have h3' := h3
    rw [hXoV] at h3'
    have hV' : ∀ᶠ t' in 𝓝 t, (χ a).γ t' ∈ V := hcont.preimage_mem_nhds (hV.mem_nhds h3'.2)
    filter_upwards [hV', Metric.isOpen_ball.mem_nhds ht,
      HermMetricEq.eventually_inFrameDomain hcont h4] with t' h5 h6 h7
    refine ⟨?_, h7⟩
    rw [hXoV]
    exact ⟨(χ a).mem t' h6, h5⟩
  have hfeq : (fun t' => (hA.toIndefiniteRowSideFullHecke (subset_of_open hopen) hsm).H ((χ a).γ t') (hA.b l) p q) =ᶠ[𝓝 t]
      fun t' => hA.gram l ((χ a).γ t') p q := by
    filter_upwards [hev] with t' ht'
    rw [metricOn_gram_eq hA _ hsm l ht'.1 ht'.2]
  rw [hfeq.fderiv_eq]
  exact hb3 p q

def roundTrip {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)}
    {χ : Fin nc → SncChart (mCoordIdeal y) n Bd} (hA : HermMetric y W Xo χ)
    (hopen : ∃ V : Set ((Σ k, ι k) → ℂ), IsOpen V ∧ Xo = mcPts (mCoordIdeal y) ∩ V)
    (htorus : ∀ z ∈ Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ Xo)
    (hconj : ∀ z ∈ Xo, conjVec z ∈ Xo) (hsm : hA.SmoothAlongHolo) : HermMetric y W Xo χ :=
  split_model_to_place_model (hA.toIndefiniteRowSideFullHecke (subset_of_open hopen) hsm) hopen htorus hconj χ hA.m hA.chart hA.fr hA.b hA.isFrame
    hA.cover (logBound_metricOn hA hopen hsm)

end OfTwin

namespace Example

open Line

theorem lineMetric_smoothAlongHolo : lineMetric.SmoothAlongHolo := by
  intro m O γ _ _ _ w _ l _ p q
  show ContDiffAt ℝ _ (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ) p q) w
  exact contDiffAt_const

theorem lineXo_open : ∃ V : Set ((Σ _ : Unit, Fin 2) → ℂ), IsOpen V ∧
    mcPts (mCoordIdeal yLine) \ ∅ = mcPts (mCoordIdeal yLine) ∩ V :=
  ⟨Set.univ, isOpen_univ, by simp⟩

theorem lineXo_torus : ∀ z ∈ mcPts (mCoordIdeal yLine) \ ∅, ∀ c : Unit → ℂ, (∀ k, c k ≠ 0) →
    torusSmul c z ∈ mcPts (mCoordIdeal yLine) \ ∅ := by
  intro z hz c hc
  obtain ⟨i, hi⟩ := mem_mcPts_line.1 hz.1
  exact ⟨mem_mcPts_line.2 ⟨i, mul_ne_zero (hc ()) hi⟩, Set.notMem_empty _⟩

theorem lineXo_conj : ∀ z ∈ mcPts (mCoordIdeal yLine) \ ∅,
    conjVec z ∈ mcPts (mCoordIdeal yLine) \ ∅ := by
  intro z hz
  obtain ⟨i, hi⟩ := mem_mcPts_line.1 hz.1
  exact ⟨mem_mcPts_line.2 ⟨i, (map_ne_zero _).2 hi⟩, Set.notMem_empty _⟩

def projLineConstantMetric : IndefiniteRowSideFullHecke.LowerBoundFree.HermMetricOn yLine (trivialBundle (segreCoord yLine) 2)
    (mcPts (mCoordIdeal yLine) \ ∅) :=
  lineMetric.toIndefiniteRowSideFullHecke Set.sdiff_subset lineMetric_smoothAlongHolo

def lineRoundTrip : HermMetric yLine (trivialBundle (segreCoord yLine) 2)
    (mcPts (mCoordIdeal yLine) \ ∅) lineChart :=
  lineMetric.roundTrip lineXo_open lineXo_torus lineXo_conj lineMetric_smoothAlongHolo

end Example

end HermMetric

end GroundTheory.Heights₂.Heights.LowerBoundFree
