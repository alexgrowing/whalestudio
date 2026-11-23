import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralTailBoundExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshPullbackHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveAtlasPositivePotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBdPullbackBoundary

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open ReciprocityTheory.AnForm.P GlobalTheory.Mean4O
open scoped ENNReal

namespace GlobalTheory.LogResCurv

noncomputable section

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem pshOff_of_isPsh (B : FinHolAtlas e Y) (Z : Set Y) (P : LocPot Y) (h : IsPsh B P) : PshOff B Z P :=
  fun j y hy _ w => h _ j y ⟨hy, P.mem_U _⟩ w

theorem add_ofFun_zero (P : LocPot Y) : P = P + LocPot.ofFun (fun _ => 0) := by
  cases P with
  | mk U hU hm φ =>
    show LocPot.mk U hU hm φ = LocPot.mk (fun x => U x ∩ Set.univ) _ _ (fun x y => φ x y + 0)
    congr 1 <;> funext x <;> simp

theorem pullback_add_ofFun (μ : Y → X) (hμ : Continuous μ) (P : LocPot X) (w : X → ℝ) :
    (P + LocPot.ofFun w).pullback μ hμ = P.pullback μ hμ + LocPot.ofFun (fun y => w (μ y)) := rfl

theorem psh_mono (B : FinHolAtlas e Y) {Om P : LocPot Y}
    (hO : IsPotential B Om) (hOp : IsPsh B Om) (hP : IsPotential B P) {C C' : ℝ}
    (h : IsPsh B (Om.rsmul C + P)) (hC : C ≤ C') : IsPsh B (Om.rsmul C' + P) := by
  have h1 := isPshAdd B (Om.rsmul (C' - C)) (Om.rsmul C + P) (isPotentialRsmul B _ Om hO)
    (isPotentialAdd B _ _ (isPotentialRsmul B _ Om hO) hP) (isPshRsmul B _ Om (by linarith) hO hOp) h
  refine TailBoundAlt.isPsh_congr B _ _ h1 (fun x z hz => ⟨hz.1, hz.1, hz.2⟩) ?_
  funext x z
  show C' * Om.φ x z + P.φ x z = (C' - C) * Om.φ x z + (C * Om.φ x z + P.φ x z)
  ring

theorem mInt_congr_null (B : FinHolAtlas e Y) (Φ : Fin e → LocPot Y) (Z : Set Y)
    (hZ : ∀ j, volume ((B.chart j).target ∩ (B.chart j).symm ⁻¹' Z) = 0) (g g' : Y → ℝ)
    (h : ∀ x, x ∉ Z → g x = g' x) : mInt B Φ g = mInt B Φ g' := by
  unfold mInt integralWith
  split_ifs with hP
  · refine Finset.sum_congr rfl fun j _ => ?_
    refine setIntegral_congr_ae (B.chart j).open_target.measurableSet ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hZ j)] with y hy hyt
    have hz : (B.chart j).symm y ∉ Z := fun h' => hy ⟨hyt, h'⟩
    rw [h _ hz]
  · rfl

theorem smooth_comp_holo {d n : ℕ} (A : FinHolAtlas d X) (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ)
    (f : X → ℝ) (hf : A.Smooth f) : B.Smooth (fun y => f (μ y)) := by
  have hp := isPotentialPullback A B μ hμ _ (isPotential_ofFun A f hf)
  intro j t ht
  exact hp.1 ((B.chart j).symm t) j t ht

theorem continuous_of_smooth (B : FinHolAtlas e Y) {g : Y → ℝ} (hg : B.Smooth g) : Continuous g :=
  continuous_iff_continuousAt.2 fun y => LeviFormBoundaryTopology.continuousAt_of_smoothOn B isOpen_univ hg (Set.mem_univ y)

theorem listForm_add (B : FinHolAtlas e Y) {Z : Set Y} {r : Y → ℝ} {Om θ : LocPot Y} {K : ℝ} {u : Y → ℝ}
    (hθ : IsPotential B θ) (h1 : IsPsh B (Om.rsmul K + θ)) (h2 : IsPsh B (Om.rsmul K + θ.rsmul (-1)))
    (hu : B.Smooth u) (hb : ∀ x, x ∉ Z → -(K * Real.log (r x)) ≤ u x ∧ u x ≤ 0)
    (hp : IsPsh B (θ + LocPot.ofFun u)) : ListForm B Z r Om K (θ + LocPot.ofFun u) :=
  ⟨θ, u, rfl, hθ, h1, h2, fun j => (hu j).mono fun _ hy => ⟨hy.1, trivial⟩, hb, Or.inl hu,
    pshOff_of_isPsh B Z _ hp⟩

theorem listForm_self (B : FinHolAtlas e Y) {Z : Set Y} {r : Y → ℝ} {Om θ : LocPot Y} {K : ℝ}
    (hK : 0 ≤ K) (hr : ∀ x, x ∉ Z → Real.exp 1 ≤ r x)
    (hθ : IsPotential B θ) (h1 : IsPsh B (Om.rsmul K + θ)) (h2 : IsPsh B (Om.rsmul K + θ.rsmul (-1)))
    (hp : IsPsh B θ) : ListForm B Z r Om K θ := by
  have h := listForm_add B (Z := Z) (r := r) (u := fun _ => 0) hθ h1 h2 (fun _ => contDiffOn_const)
    (fun x hx => ⟨by
      have : 0 ≤ Real.log (r x) := Real.log_nonneg ((Real.one_le_exp zero_le_one).trans (hr x hx))
      have := mul_nonneg hK this
      linarith, le_rfl⟩) (add_ofFun_zero θ ▸ hp)
  rwa [← add_ofFun_zero θ] at h

theorem mInt_nonpos_off [CompactSpace Y] [T2Space Y] (B : FinHolAtlas e Y) (Φ : Fin e → LocPot Y)
    (hΦ : ∀ i, IsPotential B (Φ i)) (hp : ∀ i, IsPsh B (Φ i)) (Z : Set Y)
    (hZ : ∀ j, volume ((B.chart j).target ∩ (B.chart j).symm ⁻¹' Z) = 0) {g : Y → ℝ} (hg : Continuous g)
    (h0 : ∀ x, x ∉ Z → g x ≤ 0) : mInt B Φ g ≤ 0 := by
  rw [mInt_congr_null B Φ Z hZ g (fun x => min (g x) 0) fun x hx => (min_eq_left (h0 x hx)).symm]
  exact TailBoundAlt.mInt_nonpos B Φ hΦ hp _ (hg.min continuous_const) fun _ => min_le_right _ _

theorem mInt_lower_of_tail [CompactSpace Y] [T2Space Y] (B : FinHolAtlas e Y) {Z : Set Y} {r : Y → ℝ} {Om : LocPot Y}
    (hB : IsBd B Z r Om) {K C : ℝ} (hK : 0 ≤ K) (hT : Tail B Z r Om K C) (Φ : Fin e → LocPot Y)
    (hΦ : ∀ i, IsPotential B (Φ i)) (hp : ∀ i, IsPsh B (Φ i)) (hl : ∀ i, ListForm B Z r Om K (Φ i))
    {g : Y → ℝ} (hg : Continuous g) (hb : ∀ x, x ∉ Z → -(K * Real.log (r x)) ≤ g x) :
    -(K * (C * Real.log (Real.exp 1) ^ (e + 1) / Real.exp 1)) ≤ mInt B Φ g := by
  obtain ⟨hint, -, htail⟩ := hT Φ hl
  have h1 := htail (Real.exp 1) le_rfl
  have hcut : (GlobalTheory.Mean4O.cut Z {x | Real.exp 1 ≤ r x} fun x => Real.log (r x)) = GlobalTheory.Mean4O.cut Z Set.univ fun x => Real.log (r x) := by
    unfold GlobalTheory.Mean4O.cut
    congr 1
    ext x
    exact ⟨fun h => ⟨trivial, h.2⟩, fun h => ⟨hB.2.2.2.2.2.1 x h.2, h.2⟩⟩
  rw [hcut] at h1
  have hlin := mIntLinear B Φ hΦ K _ g hint (mIntegrableCont B Φ hΦ g hg)
  have hnn := mIntNonneg B Φ hΦ hp (fun x => max (K * GlobalTheory.Mean4O.cut Z Set.univ (fun x => Real.log (r x)) x + g x) 0)
    fun _ => le_max_right _ _
  rw [← mInt_congr_null B Φ Z hB.2.1 (fun x => K * GlobalTheory.Mean4O.cut Z Set.univ (fun x => Real.log (r x)) x + g x) _
    (fun x hx => (max_eq_left (by
      rw [GlobalTheory.Mean4O.cut, Set.indicator_of_mem (show x ∈ Set.univ ∩ Zᶜ from ⟨trivial, hx⟩)]
      linarith [hb x hx])).symm), hlin] at hnn
  have := mul_le_mul_of_nonneg_left h1 hK
  linarith

theorem logNormSec_nonpos {L : LocPot X} {s : X → X → ℂ} {y : X} (h : normSec L s y ≤ 1) : logNormSec L s y ≤ 0 :=
  Real.log_nonpos (by positivity) h

theorem sum_log_le {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, a i ≤ 0) :
    0 ≤ 1 + ∑ i, Real.log (Real.exp 1 - 2 * a i) ∧
    1 + ∑ i, Real.log (Real.exp 1 - 2 * a i) ≤ (1 + m) * Real.log (Real.exp 1 - 2 * ∑ i, a i) := by
  have hs : ∑ i, a i ≤ 0 := Finset.sum_nonpos fun i _ => ha i
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have h1 : 1 ≤ Real.log (Real.exp 1 - 2 * ∑ i, a i) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  have h2 : ∀ i, Real.log (Real.exp 1 - 2 * a i) ≤ Real.log (Real.exp 1 - 2 * ∑ i, a i) := fun i => by
    have : -a i ≤ ∑ i, -a i := Finset.single_le_sum (f := fun i => -a i) (fun j _ => by linarith [ha j])
      (Finset.mem_univ i)
    rw [Finset.sum_neg_distrib] at this
    exact Real.log_le_log (by linarith [ha i]) (by linarith)
  have h3 := Finset.sum_le_sum (s := Finset.univ) fun i _ => h2 i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  have h4 : 0 ≤ ∑ i, Real.log (Real.exp 1 - 2 * a i) :=
    Finset.sum_nonneg fun i _ => Real.log_nonneg (by linarith [ha i])
  constructor <;> linarith

end

theorem curvature_term_bounded : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas (n + 1) Y),
    IsProjective B → ∀ (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y)
    (e : Fin (m + 1) → Fin r → ℕ),
    IsJointSNC B μ (Fin.cons L Λ) (Fin.cons s σ) W e →
    ∀ (w : ℕ → X → ℝ) (K : ℝ), (∀ R, A.Smooth (w R)) → (∀ R, IsPsh A (α + LocPot.ofFun (w R))) →
    (∀ R x, x ∉ boundary σ →
        -(K * (1 + ∑ i, Real.log (rFun (Λ i) (σ i) x))) ≤ w R x ∧ w R x ≤ 0) →
    ∃ C : ℝ, ∀ (R : ℕ) (T : Fin n → LocPot Y), (∀ k, T k = (α + LocPot.ofFun (w R)).pullback μ hμ.1 ∨ T k = α.pullback μ hμ.1) →
      mInt B (Fin.cons (L.pullback μ hμ.1) T) (fun y => w R (μ y)) ≤ C := by
  intro d X _ _ _ A m α Λ σ c hS L s hL _ _ n Y _ _ _ B hB μ hμ r W e hJ w K hw hwp hwb
  obtain ⟨hα, hαp, hσ, -⟩ := hS
  obtain ⟨Om, hO, hOpos⟩ := GlobalTheory.FubiniStudyPot.exists_posPot (n + 1) Y B hB
  have hOp := TailBoundAlt.isPsh_of_isPosPot B Om hOpos
  have hint : ∀ i, interior {y | σ i (μ y) (μ y) = 0} = ∅ := fun i => by
    have hsec := GlobalTheory.isSection_pullback_holoMap d (n + 1) X Y A B μ hμ (Λ i) (σ i) (hσ i).2.1
    refine LeviFormBoundaryTopology.interior_bdry_eq_empty (m := e i.succ) (W := W) hsec fun y => ?_
    obtain ⟨χ, h1, h2, κ, h3, h4, h5⟩ := hJ y
    obtain ⟨h6, u, h7, h8, h9⟩ := h5 i.succ
    exact ⟨χ, h1, h2, h6, κ, h3, h4, u, h7, h8, h9⟩
  have hBd := GlobalTheory.isBd_pullback_boundary d X A m Λ σ (fun i => ⟨(hσ i).1, (hσ i).2.1, (hσ i).2.2.2⟩) (n + 1) Y B μ hμ hint
    Om hO hOpos
  set Z := μ ⁻¹' boundary σ with hZ
  set ρ : Y → ℝ := fun y => Real.exp 1 - 2 * ∑ i, logNormSec (Λ i) (σ i) (μ y) with hρ
  have hL' := isPotentialPullback A B μ hμ L hL
  have hα' := isPotentialPullback A B μ hμ α hα
  have hαp' := GlobalTheory.PshPull.isPsh_pullback d X A (n + 1) Y B μ hμ α hα (TailBoundAlt.isPsh_of_isPosPot A α hαp)
  obtain ⟨K₁, hK₁, hLp, -⟩ := TailBoundAlt.exists_psh_chern_bound B Om _ hO hOpos hL'
  obtain ⟨K₂, hK₂, ha1, ha2⟩ := TailBoundAlt.exists_psh_chern_bound B Om _ hO hOpos hα'
  obtain ⟨K₃, hK₃, ho1, ho2⟩ := TailBoundAlt.exists_psh_chern_bound B Om _ hO hOpos hO
  have hKm : 0 ≤ max K 0 * (1 + (m : ℝ)) := by positivity
  set K' := K₂ + K₃ + max K 0 * (1 + (m : ℝ)) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hρe := hBd.2.2.2.2.2.1
  obtain ⟨C, hC⟩ := GlobalTheory.Mean4O.LogTail.tail (n + 1) Y B Z ρ Om hBd K'
  have ha1' := psh_mono B hO hOp hα' ha1 (C' := K') (by linarith)
  have ha2' := psh_mono B hO hOp (isPotentialRsmul B _ _ hα') ha2 (C' := K') (by linarith)
  have hlO : ListForm B Z ρ Om K' Om := listForm_self B hK'0 hρe hO (psh_mono B hO hOp hO ho1 (by linarith))
    (psh_mono B hO hOp (isPotentialRsmul B _ _ hO) ho2 (by linarith)) hOp
  refine ⟨K₁ * (K' * (C * Real.log (Real.exp 1) ^ (n + 1 + 1) / Real.exp 1)), fun R T hT => ?_⟩
  have hg := smooth_comp_holo A B μ hμ _ (hw R)
  have hgc := continuous_of_smooth B hg
  have hgb : ∀ y, y ∉ Z → -(K' * Real.log (ρ y)) ≤ w R (μ y) ∧ w R (μ y) ≤ 0 := fun y hy => by
    obtain ⟨h1, h2⟩ := hwb R (μ y) hy
    refine ⟨le_trans ?_ h1, h2⟩
    obtain ⟨h3, h4⟩ := sum_log_le (fun i => logNormSec (Λ i) (σ i) (μ y))
      fun i => logNormSec_nonpos ((hσ i).2.2.2 _)
    have h5 : 0 ≤ Real.log (ρ y) := Real.log_nonneg ((Real.one_le_exp zero_le_one).trans (hρe y hy))
    have h6 := mul_le_mul (le_max_left K 0) h4 h3 (le_max_right K 0)
    have h7 := mul_nonneg (add_nonneg hK₂ hK₃) h5
    have h8 : K' * Real.log (ρ y) =
        (K₂ + K₃) * Real.log (ρ y) + max K 0 * ((1 + (m : ℝ)) * Real.log (ρ y)) := by rw [hK']; ring
    rw [h8]
    exact neg_le_neg (h6.trans (le_add_of_nonneg_left h7))
  have hwR := isPotentialAdd A _ _ hα (isPotential_ofFun A _ (hw R))
  have hTall : ∀ k, IsPotential B (T k) ∧ IsPsh B (T k) ∧ ListForm B Z ρ Om K' (T k) := fun k => by
    rcases hT k with h | h <;> rw [h]
    · have hp := GlobalTheory.PshPull.isPsh_pullback d X A (n + 1) Y B μ hμ _ hwR (hwp R)
      refine ⟨isPotentialPullback A B μ hμ _ hwR, hp, ?_⟩
      rw [pullback_add_ofFun] at hp ⊢
      exact listForm_add B hα' ha1' ha2' hg hgb hp
    · exact ⟨hα', hαp', listForm_self B hK'0 hρe hα' ha1' ha2' hαp'⟩
  have hTp : ∀ k, IsPotential B (T k) := fun k => (hTall k).1
  have hP := isPotentialAdd B _ _ (isPotentialRsmul B K₁ Om hO) hL'
  have hQ := isPotentialRsmul B (-K₁) Om hO
  have hcons : ∀ P : LocPot Y, IsPotential B P → ∀ i, IsPotential B ((Fin.cons P T : Fin (n + 1) → LocPot Y) i) :=
    fun P hP i => Fin.cases hP hTp i
  have e1 : mInt B (Fin.cons (L.pullback μ hμ.1) T) (fun y => w R (μ y)) =
      mInt B (Fin.cons ((Om.rsmul K₁ + L.pullback μ hμ.1) + Om.rsmul (-K₁)) T) (fun y => w R (μ y)) := by
    refine TailBoundAlt.mInt_congr_phi B _ _ (fun i => Fin.cases ?_ (fun _ => rfl) i) _
    funext x z
    show (L.pullback μ hμ.1).φ x z = (K₁ * Om.φ x z + (L.pullback μ hμ.1).φ x z) + -K₁ * Om.φ x z
    ring
  rw [e1, mIntAdd B _ _ T hP hQ hTp _ (mIntegrableCont B _ (hcons _ hP) _ hgc)
    (mIntegrableCont B _ (hcons _ hQ) _ hgc), mIntRsmul B _ Om T hO hTp]
  have b1 := mInt_nonpos_off B (Fin.cons (Om.rsmul K₁ + L.pullback μ hμ.1) T) (hcons _ hP)
    (fun i => Fin.cases hLp (fun k => (hTall k).2.1) i) Z hBd.2.1 hgc fun y hy => (hgb y hy).2
  have b2 := mInt_lower_of_tail B hBd hK'0 hC (Fin.cons Om T) (hcons _ hO)
    (fun i => Fin.cases hOp (fun k => (hTall k).2.1) i) (fun i => Fin.cases hlO (fun k => (hTall k).2.2) i) hgc
    fun y hy => (hgb y hy).1
  have b3 := mul_le_mul_of_nonneg_left b2 hK₁
  linarith

end GlobalTheory.LogResCurv
