import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralBoundUnitPotentialsStatement

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory

noncomputable section

namespace GlobalTheory.PotOsc

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem locDens_congr_phi {Φ Ψ : Fin e → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ) (j : Fin A.n)
    (y : Fin e → ℂ) : locDens A Φ j y = locDens A Ψ j y := by
  unfold locDens
  simp only [h]

theorem isPsh_congr {P Q : LocPot X} (hP : IsPsh A P) (hU : ∀ x, P.U x = Q.U x)
    (hφ : ∀ x, P.φ x = Q.φ x) : IsPsh A Q := by
  intro x j y hy w
  have := hP x j y (by rw [hU x]; exact hy) w
  rwa [hφ x] at this

theorem locDens_rsmul_all (Ψ : Fin e → LocPot X) (c : ℝ) (j : Fin A.n) (y : Fin e → ℂ) :
    locDens A (fun i => (Ψ i).rsmul c) j y = c ^ e * locDens A Ψ j y := by
  unfold locDens maDens
  have h : (fun i => hessC (fun y' => ((Ψ i).rsmul c).φ ((A.chart j).symm y)
      ((A.chart j).symm y')) y) = fun i => ((c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ)) *
        hessC (fun y' => (Ψ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y * 1 := by
    funext i
    rw [Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
    exact hessC_const_mul' c _ y
  simp only [h]
  rw [ReciprocityTheory.AnForm.A.mdisc_mul_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
  simp only [mul_one]
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

theorem smooth_continuous {u : X → ℝ} (hu : A.Smooth u) : Continuous u := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hj⟩ := A.cover x
  have hy := (A.chart j).map_source hj
  have h1 : ContinuousAt (u ∘ (A.chart j).symm) (A.chart j x) :=
    ((hu j).continuousOn.continuousAt (((A.chart j).isOpen_inter_preimage_symm isOpen_univ).mem_nhds
      ⟨hy, Set.mem_univ _⟩))
  have h3 : ContinuousAt ((u ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

end GlobalTheory.PotOsc

open GlobalTheory.PotOsc in

theorem GlobalTheory.PotOsc.mInt_le_pow_mul : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Om : LocPot X) (w : X → ℝ) (u : Fin e → X → ℝ) (M : ℝ),
    1 ≤ M → IsPotential A Om → IsPsh A Om → A.Smooth w → (∀ x, w x ≤ 0) →
    IsPsh A (Om + LocPot.ofFun w) →
    (∀ i, A.Smooth (u i) ∧ (∀ x, -M ≤ u i x ∧ u i x ≤ 0) ∧ IsPsh A (Om + LocPot.ofFun (u i))) →
    mInt A (fun i => Om + LocPot.ofFun (u i)) (fun x => -w x) ≤
      M ^ e * (mInt A (fun _ => Om) (fun x => -w x) + e * mInt A (fun _ => Om) (fun _ => 1)) := by
  intro e X _ _ _ A Om w u M hM hO hOp hw hw0 hwp hu
  have hM0 : 0 < M := by linarith
  set v : Fin e → X → ℝ := fun i x => u i x / M with hv
  set Φ : Fin e → LocPot X := fun i => Om + LocPot.ofFun (u i) with hΦ
  set Ψ : Fin e → LocPot X := fun i => Om + LocPot.ofFun (v i) with hΨ
  set Θ : Fin e → LocPot X := fun _ => Om.rsmul (M - 1) with hΘ
  have hΦ1 : ∀ i, IsPotential A (Φ i) := fun i =>
    isPotentialAdd A _ _ hO (isPotential_ofFun A _ (hu i).1)
  have hΦ2 : ∀ i, IsPsh A (Φ i) := fun i => (hu i).2.2
  have hvs : ∀ i, A.Smooth (v i) := fun i j => (hu i).1 j |>.div_const M
  have hΨ1 : ∀ i, IsPotential A (Ψ i) := fun i =>
    isPotentialAdd A _ _ hO (isPotential_ofFun A _ (hvs i))
  have hΘ1 : ∀ i, IsPotential A (Θ i) := fun _ => isPotentialRsmul A _ Om hO
  have hΘ2 : ∀ i, IsPsh A (Θ i) := fun _ => isPshRsmul A _ Om (by linarith) hO hOp
  have hΨ2 : ∀ i, IsPsh A (Ψ i) := by
    intro i
    have h1 : IsPsh A ((Φ i).rsmul (1 / M)) :=
      isPshRsmul A _ _ (by positivity) (hΦ1 i) (hΦ2 i)
    have h2 : IsPsh A (Om.rsmul (1 - 1 / M)) :=
      isPshRsmul A _ Om (by rw [sub_nonneg, div_le_one hM0]; exact hM) hO hOp
    have h3 := isPshAdd A _ _ (isPotentialRsmul A _ _ (hΦ1 i)) (isPotentialRsmul A _ Om hO) h1 h2
    refine isPsh_congr h3 (fun x => ?_) (fun x => ?_)
    · show (Om.U x ∩ Set.univ) ∩ Om.U x = Om.U x ∩ Set.univ
      simp
    · funext z
      show 1 / M * (Om.φ x z + u i z) + (1 - 1 / M) * Om.φ x z = Om.φ x z + u i z / M
      field_simp
      ring
  have hvb : ∀ i, A.Smooth (v i) ∧ (∀ x, -1 ≤ v i x ∧ v i x ≤ 0) ∧
      IsPsh A (Om + LocPot.ofFun (v i)) := by
    intro i
    refine ⟨hvs i, fun x => ⟨?_, ?_⟩, hΨ2 i⟩
    · show -1 ≤ u i x / M
      rw [le_div_iff₀ hM0]; linarith [((hu i).2.1 x).1]
    · show u i x / M ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg ((hu i).2.1 x).2 hM0.le
  have hcl := GlobalTheory.T.mixed_integral_bound_unit_potentials e X A Om w v hO hOp hw hw0 hwp hvb

  have hpt : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y ≤ M ^ e * locDens A Ψ j y := by
    intro j y hy
    have h1 := locDens_le_add A Φ Θ hΦ1 hΦ2 hΘ1 hΘ2 j hy
    have h2 : locDens A (fun i => Φ i + Θ i) j y = locDens A (fun i => (Ψ i).rsmul M) j y := by
      refine locDens_congr_phi (fun i => ?_) j y
      funext x z
      show (Om.φ x z + u i z) + (M - 1) * Om.φ x z = M * (Om.φ x z + u i z / M)
      field_simp
      ring
    rw [h2, locDens_rsmul_all] at h1
    exact h1
  have hgc : Continuous fun x => -w x := (smooth_continuous hw).neg
  have hgΦ := mIntegrableCont A Φ hΦ1 _ hgc
  have hgΨ := mIntegrableCont A Ψ hΨ1 _ hgc
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hcmp : mInt A Φ (fun x => -w x) ≤ M ^ e * mInt A Ψ (fun x => -w x) := by
    rw [mInt_eq_integralWith A _ hne, mInt_eq_integralWith A _ hne]
    unfold integralWith
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_weight A hne.some Φ _ hgΦ j)
      ((integrableOn_weight A hne.some Ψ _ hgΨ j).const_mul _)
      (A.chart j).open_target.measurableSet fun y hy => ?_
    have ha : 0 ≤ hne.some.χ j ((A.chart j).symm y) * -w ((A.chart j).symm y) :=
      mul_nonneg (hne.some.nonneg j _) (neg_nonneg.2 (hw0 _))
    have := mul_le_mul_of_nonneg_left (hpt j y hy) ha
    calc _ = hne.some.χ j ((A.chart j).symm y) * -w ((A.chart j).symm y) * locDens A Φ j y := rfl
      _ ≤ _ := this
      _ = _ := by ring
  calc mInt A Φ (fun x => -w x) ≤ M ^ e * mInt A Ψ (fun x => -w x) := hcmp
    _ ≤ _ := mul_le_mul_of_nonneg_left hcl (pow_nonneg hM0.le e)
