import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncPullbackSectionBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySectionPullbackBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySectionPullbackBoundTwoStatement
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal

namespace GlobalTheory.LogResBound

noncomputable section

theorem log_residue_first_chern_bound : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
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
      mInt B (Fin.cons (L.pullback μ hμ.1) T) (fun y => w R (μ y)) ≤ C := GlobalTheory.T.boundary_section_pullback_bound
theorem divBound : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas (n + 1) Y),
    IsProjective B → ∀ (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y)
    (e : Fin (m + 1) → Fin r → ℕ),
    IsJointSNC B μ (Fin.cons L Λ) (Fin.cons s σ) W e →
    (∀ k, 1 ≤ e 0 k → (∃ i : Fin m, 1 ≤ e i.succ k) → RankDropAlong A μ B (W k)) →
    ∀ (w : ℕ → X → ℝ) (K : ℝ), (∀ R, A.Smooth (w R)) → (∀ R, IsPsh A (α + LocPot.ofFun (w R))) →
    (∀ R x, x ∉ boundary σ →
        -(K * (1 + ∑ i, Real.log (rFun (Λ i) (σ i) x))) ≤ w R x ∧ w R x ≤ 0) →
    ∃ Bk : ∀ k, FinHolAtlas n (W k), (∀ k, HoloMap (Bk k) B Subtype.val) ∧ ∃ C : ℝ,
      ∀ (R : ℕ) (T : Fin n → LocPot Y), (∀ k, T k = (α + LocPot.ofFun (w R)).pullback μ hμ.1 ∨ T k = α.pullback μ hμ.1) → ∀ k, 1 ≤ e 0 k →
        -C ≤ mInt (Bk k) (fun i => (T i).pullback Subtype.val continuous_subtype_val) (fun y => w R (μ y.1)) := GlobalTheory.T.boundary_section_pullback_bound_two
theorem secPull : ∀ (d n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas d X)
    (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (L : LocPot X) (s : X → X → ℂ),
    IsSection A L s → IsSection B (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) := GlobalTheory.T.section_pullback_holomorphic
theorem finCmp : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas n Y)
    (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y) (m₀ : Fin r → ℕ),
    IsSNC B (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) m₀ W →
    ∀ [MeasurableSpace Y] [BorelSpace Y] (Φ : Fin n → LocPot Y), (∀ i, IsPotential B (Φ i)) →
    (∀ i, IsPsh B (Φ i)) →
    ∫⁻ y, absLogNorm L s (μ y) ∂maMeasure B Φ ≤
      ENNReal.ofReal (mInt B Φ (fun y => -logNormSec L s (μ y))) := GlobalTheory.T.snc_pullback_section_bound

theorem mInt_congr_φ {e : ℕ} {Y : Type} [TopologicalSpace Y] (B : FinHolAtlas e Y) (Φ Ψ : Fin e → LocPot Y)
    (h : ∀ i, (Φ i).φ = (Ψ i).φ) (g : Y → ℝ) : mInt B Φ g = mInt B Ψ g := by
  have : ∀ j y, locDens B Φ j y = locDens B Ψ j y := by
    intro j y; simp only [locDens, h]
  simp only [mInt, integralWith, this]

theorem mInt_zero {e : ℕ} {Y : Type} [TopologicalSpace Y] (B : FinHolAtlas e Y) (Φ : Fin e → LocPot Y) :
    mInt B Φ (fun _ => 0) = 0 := by
  simp [mInt, integralWith]

theorem MIntegrable.neg' {e : ℕ} {Y : Type} [TopologicalSpace Y] {B : FinHolAtlas e Y} {Φ : Fin e → LocPot Y}
    {f : Y → ℝ} (h : MIntegrable B Φ f) : MIntegrable B Φ (fun y => -f y) := by
  intro j K hK hc
  have := (h j K hK hc).neg
  simpa [neg_mul] using this

theorem smooth_comp_holo {d n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas d X)
    (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (f : X → ℝ) (hf : A.Smooth f) :
    B.Smooth (fun y => f (μ y)) := by
  have hp := isPotentialPullback A B μ hμ _ (isPotential_ofFun A f hf)
  intro j t ht
  exact hp.1 ((B.chart j).symm t) j t ht

theorem jointSNC_zero {d n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {A : FinHolAtlas d X}
    {B : FinHolAtlas n Y} {μ : Y → X} (hμ : HoloMap B A μ) {m r : ℕ} (L : LocPot X) (Λ : Fin m → LocPot X)
    (s : X → X → ℂ) (σ : Fin m → X → X → ℂ) (W : Fin r → Set Y) (e : Fin (m + 1) → Fin r → ℕ)
    (h : IsJointSNC B μ (Fin.cons L Λ) (Fin.cons s σ) W e) :
    IsSNC B (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) (e 0) W := by
  intro y
  obtain ⟨χ, hc, hy, κ, hinj, hW, hi⟩ := h y
  obtain ⟨hsub, u, hu, hu0, hprod⟩ := hi 0
  simp only [Fin.cons_zero] at hsub hprod
  exact ⟨χ, hc, hy, hsub, κ, hinj, hW, u, hu, hu0, hprod⟩

theorem mix_swap {β : Type} (P Q : β) (n i : ℕ) (hi : i < n + 1) :
    ((fun k : Fin (n + 1) => if (k : ℕ) < i + 1 then P else Q) ∘ Equiv.swap (0 : Fin (n + 1)) ⟨i, hi⟩ =
       Fin.cons P (fun k : Fin n => if (k : ℕ) + 1 ≤ i then P else Q)) ∧
    ((fun k : Fin (n + 1) => if (k : ℕ) < i then P else Q) ∘ Equiv.swap (0 : Fin (n + 1)) ⟨i, hi⟩ =
       Fin.cons Q (fun k : Fin n => if (k : ℕ) + 1 ≤ i then P else Q)) := by
  constructor <;> funext k <;> refine Fin.cases ?_ (fun k => ?_) k <;>
    simp only [Function.comp_apply, Equiv.swap_apply_def, Fin.cons_zero, Fin.cons_succ] <;>
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_succ] <;> omega

theorem step : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas n Y),
    IsProjective B → ∀ (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y)
    (e : Fin (m + 1) → Fin r → ℕ),
    IsJointSNC B μ (Fin.cons L Λ) (Fin.cons s σ) W e →
    (∀ k, 1 ≤ e 0 k → (∃ i : Fin m, 1 ≤ e i.succ k) → RankDropAlong A μ B (W k)) →
    ∀ (w : ℕ → X → ℝ) (K : ℝ), (∀ R, A.Smooth (w R)) → (∀ R, IsPsh A (α + LocPot.ofFun (w R))) →
    (∀ R x, x ∉ boundary σ →
        -(K * (1 + ∑ i, Real.log (rFun (Λ i) (σ i) x))) ≤ w R x ∧ w R x ≤ 0) →
    ∃ C : ℝ, ∀ (R i : ℕ), i < n →
      mInt B (fun k : Fin n => if (k : ℕ) < i + 1 then (α + LocPot.ofFun (w R)).pullback μ hμ.1 else α.pullback μ hμ.1) (fun y => -logNormSec L s (μ y)) ≤
        mInt B (fun k : Fin n => if (k : ℕ) < i then (α + LocPot.ofFun (w R)).pullback μ hμ.1 else α.pullback μ hμ.1) (fun y => -logNormSec L s (μ y)) + C := by
  intro d X _ _ _ A m α Λ σ c hBS L s hL hs hs1 n Y _ _ _ B hproj μ hμ r W e hJ hRD w K hw hpsh hbd
  cases n with
  | zero => exact ⟨0, fun R i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n =>
  obtain ⟨C1, hC1⟩ := log_residue_first_chern_bound d X A m α Λ σ c hBS L s hL hs hs1 n Y B hproj μ hμ r W e hJ w K hw hpsh hbd
  obtain ⟨Bk, hBk, C2, hC2⟩ :=
    divBound d X A m α Λ σ c hBS L s hL hs hs1 n Y B hproj μ hμ r W e hJ hRD w K hw hpsh hbd
  refine ⟨C1 + ∑ k, (e 0 k : ℝ) * C2, fun R i hi => ?_⟩
  have hα : IsPotential A α := hBS.1
  have hL' : IsPotential B (L.pullback μ hμ.1) := isPotentialPullback A B μ hμ L hL
  have hs' := secPull d (n + 1) X Y A B μ hμ L s hs
  have hsnc := jointSNC_zero hμ L Λ s σ W e hJ
  have hΦpot : IsPotential B ((α + LocPot.ofFun (w R)).pullback μ hμ.1) :=
    isPotentialPullback A B μ hμ _ (isPotentialAdd A α _ hα (isPotential_ofFun A _ (hw R)))
  have hapot : IsPotential B (α.pullback μ hμ.1) := isPotentialPullback A B μ hμ α hα
  have hv : B.Smooth (fun y => w R (μ y)) := smooth_comp_holo A B μ hμ (w R) (hw R)
  have hsw := mix_swap ((α + LocPot.ofFun (w R)).pullback μ hμ.1) (α.pullback μ hμ.1) n i hi
  obtain ⟨T, hT⟩ : ∃ T : Fin n → LocPot Y,
      T = fun k : Fin n => if (k : ℕ) + 1 ≤ i then (α + LocPot.ofFun (w R)).pullback μ hμ.1 else α.pullback μ hμ.1 := ⟨_, rfl⟩
  rw [← hT] at hsw
  have hTmix : ∀ k, T k = (α + LocPot.ofFun (w R)).pullback μ hμ.1 ∨ T k = α.pullback μ hμ.1 := by
    intro k; rw [hT]; dsimp only; split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hTpot : ∀ k, IsPotential B (T k) := fun k => by
    rcases hTmix k with h | h <;> rw [h] <;> assumption
  have hcons : ∀ P : LocPot Y, IsPotential B P → ∀ k, IsPotential B ((Fin.cons P T : Fin (n + 1) → LocPot Y) k) :=
    fun P hP k => by
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hP
      · simpa using hTpot k
  have hint : ∀ Φ : Fin (n + 1) → LocPot Y, (∀ k, IsPotential B (Φ k)) →
      MIntegrable B Φ (fun y => -logNormSec L s (μ y)) :=
    fun Φ hΦ => MIntegrable.neg' (logNormIntegrable B _ _ (e 0) W hL' hs' hsnc Φ hΦ)
  have e1 : mInt B (fun k : Fin (n + 1) => if (k : ℕ) < i + 1 then (α + LocPot.ofFun (w R)).pullback μ hμ.1 else α.pullback μ hμ.1) (fun y => -logNormSec L s (μ y)) =
      mInt B (Fin.cons ((α + LocPot.ofFun (w R)).pullback μ hμ.1) T) (fun y => -logNormSec L s (μ y)) := by
    rw [← mIntSymm B _ (Equiv.swap (0 : Fin (n + 1)) ⟨i, hi⟩), hsw.1]
  have e2 : mInt B (fun k : Fin (n + 1) => if (k : ℕ) < i then (α + LocPot.ofFun (w R)).pullback μ hμ.1 else α.pullback μ hμ.1) (fun y => -logNormSec L s (μ y)) =
      mInt B (Fin.cons (α.pullback μ hμ.1) T) (fun y => -logNormSec L s (μ y)) := by
    rw [← mIntSymm B _ (Equiv.swap (0 : Fin (n + 1)) ⟨i, hi⟩), hsw.2]
  have e3 : mInt B (Fin.cons ((α + LocPot.ofFun (w R)).pullback μ hμ.1) T) (fun y => -logNormSec L s (μ y)) =
      mInt B (Fin.cons (α.pullback μ hμ.1 + LocPot.ofFun (fun y => w R (μ y))) T) (fun y => -logNormSec L s (μ y)) :=
    mInt_congr_φ B _ _ (fun k => by refine Fin.cases ?_ (fun k => ?_) k <;> rfl) _
  have e4 := mIntAdd B (α.pullback μ hμ.1) (LocPot.ofFun (fun y => w R (μ y))) T hapot (isPotential_ofFun B _ hv) hTpot
    (fun y => -logNormSec L s (μ y)) (hint _ (hcons _ hapot)) (hint _ (hcons _ (isPotential_ofFun B _ hv)))
  have e5 : mInt B (Fin.cons (LocPot.ofFun (fun y => w R (μ y))) T) (fun y => -logNormSec L s (μ y)) =
      -mInt B (Fin.cons (LocPot.ofFun (fun y => w R (μ y))) T) (logNormSec (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z))) := by
    have hc := hcons _ (isPotential_ofFun B _ hv)
    have := mIntLinear B _ hc (-1) (logNormSec (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z))) (fun _ => 0)
      (logNormIntegrable B _ _ (e 0) W hL' hs' hsnc _ hc) (mIntegrableCont B _ hc _ continuous_const)
    rw [mInt_zero] at this
    have hfun : (fun y => -logNormSec L s (μ y)) = (fun x => -1 * logNormSec (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) x + 0) := by
      funext y; simp [logNormSec, LocPot.pullback]
    rw [hfun, this]; ring
  have e6 := poincareLelong B (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) (e 0) W Bk hL' hs' hsnc hBk (fun y => w R (μ y)) hv T hTpot
  have hdiv : ∀ k, -((e 0 k : ℝ) * mInt (Bk k) (fun i => (T i).pullback Subtype.val continuous_subtype_val)
      ((fun y => w R (μ y)) ∘ Subtype.val)) ≤ (e 0 k : ℝ) * C2 := by
    intro k
    rcases Nat.eq_zero_or_pos (e 0 k) with h0 | h0
    · simp [h0]
    · have h1 := hC2 R T hTmix k h0
      change -C2 ≤ mInt (Bk k) (fun i => (T i).pullback Subtype.val continuous_subtype_val)
        ((fun y => w R (μ y)) ∘ Subtype.val) at h1
      have he : (0 : ℝ) ≤ e 0 k := by positivity
      have h2 := mul_le_mul_of_nonneg_left h1 he
      linarith
  have hsum : -(∑ k, (e 0 k : ℝ) * mInt (Bk k) (fun i => (T i).pullback Subtype.val continuous_subtype_val)
      ((fun y => w R (μ y)) ∘ Subtype.val)) ≤ ∑ k, (e 0 k : ℝ) * C2 := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_le_sum (fun k _ => hdiv k)
  have hc1 := hC1 R T hTmix
  rw [e1, e2, e3, e4, e5, e6]
  linarith

theorem bound : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas n Y),
    IsProjective B → ∀ (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y)
    (e : Fin (m + 1) → Fin r → ℕ),
    IsJointSNC B μ (Fin.cons L Λ) (Fin.cons s σ) W e →
    (∀ k, 1 ≤ e 0 k → (∃ i : Fin m, 1 ≤ e i.succ k) → RankDropAlong A μ B (W k)) →
    ∀ (w : ℕ → X → ℝ) (K : ℝ), (∀ R, A.Smooth (w R)) → (∀ R, IsPsh A (α + LocPot.ofFun (w R))) →
    (∀ R x, x ∉ boundary σ →
        -(K * (1 + ∑ i, Real.log (rFun (Λ i) (σ i) x))) ≤ w R x ∧ w R x ≤ 0) →
    ∀ [MeasurableSpace Y] [BorelSpace Y], ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ R,
      ∫⁻ y, absLogNorm L s (μ y) ∂maMeasure B (fun _ => (α + LocPot.ofFun (w R)).pullback μ hμ.1) ≤ C := by
  intro d X _ _ _ A m α Λ σ c hBS L s hL hs hs1 n Y _ _ _ B hproj μ hμ r W e hJ hRD w K hw hpsh hbd _ _
  have hα : IsPotential A α := hBS.1
  obtain ⟨C, hC⟩ := step d X A m α Λ σ c hBS L s hL hs hs1 n Y B hproj μ hμ r W e hJ hRD w K hw hpsh hbd
  have hsnc := jointSNC_zero hμ L Λ s σ W e hJ
  let J : ℕ → ℕ → ℝ := fun R i => mInt B (fun k : Fin n => if (k : ℕ) < i then
    (α + LocPot.ofFun (w R)).pullback μ hμ.1 else α.pullback μ hμ.1) (fun y => -logNormSec L s (μ y))
  have h0 : ∀ R, J R 0 = J 0 0 := by intro R; simp [J]
  have hind : ∀ R i, i ≤ n → J R i ≤ J 0 0 + i * C := by
    intro R i
    induction i with
    | zero => intro _; simp [h0 R]
    | succ i ih =>
      intro hi
      have h1 := hC R i (by omega)
      have h2 := ih (by omega)
      push_cast
      simp only [J] at h1 h2 ⊢
      linarith
  refine ⟨ENNReal.ofReal (J 0 0 + n * C), ENNReal.ofReal_lt_top, fun R => ?_⟩
  have hn : J R n = mInt B (fun _ => (α + LocPot.ofFun (w R)).pullback μ hμ.1)
      (fun y => -logNormSec L s (μ y)) := by simp [J]
  have hp : IsPotential A (α + LocPot.ofFun (w R)) := isPotentialAdd A α _ hα (isPotential_ofFun A _ (hw R))
  refine le_trans (finCmp d X A L s hL hs hs1 n Y B μ hμ r W (e 0) hsnc
    (fun _ => (α + LocPot.ofFun (w R)).pullback μ hμ.1) (fun _ => isPotentialPullback A B μ hμ _ hp)
    (fun _ => GlobalTheory.Mean4O.Deg.psh_pullback A B μ hμ hp (hpsh R))) (ENNReal.ofReal_le_ofReal ?_)
  rw [← hn]
  exact hind R n le_rfl

end

end GlobalTheory.LogResBound
