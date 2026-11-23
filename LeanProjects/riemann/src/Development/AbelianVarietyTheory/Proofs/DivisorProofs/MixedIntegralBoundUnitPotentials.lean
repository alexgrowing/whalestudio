import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace GlobalTheory

namespace ChernLevineNirenberg

variable {X : Type} [TopologicalSpace X]

theorem continuous_of_smooth {e : ℕ} (A : FinHolAtlas e X) (f : X → ℝ) (hf : A.Smooth f) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) := by
    have := (hf j).continuousOn
    simp only [Set.preimage_univ, Set.inter_univ] at this
    exact this.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))
  have h2 : ContinuousAt (fun y => (f ∘ (A.chart j).symm) (A.chart j y)) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem mInt_zero {e : ℕ} (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) :
    mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt integralWith
  split_ifs <;> simp

theorem mInt_neg {e : ℕ} [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) (hg : Continuous g) :
    mInt A Φ (fun x => -g x) = -mInt A Φ g := by
  have := mIntLinear A Φ hΦ (-1) g (fun _ => 0) (mIntegrableCont A Φ hΦ g hg)
    (mIntegrableCont A Φ hΦ _ continuous_const)
  rw [mInt_zero] at this
  simpa using this

end ChernLevineNirenberg
end GlobalTheory

namespace GlobalTheory
namespace ChernLevineNirenberg

variable {X : Type} [TopologicalSpace X]

theorem cons_isPotential {n : ℕ} (A : FinHolAtlas (n + 1) X) (P : LocPot X)
    (τ : Fin n → LocPot X) (hP : IsPotential A P) (hτ : ∀ i, IsPotential A (τ i)) :
    ∀ i, IsPotential A ((Fin.cons P τ : Fin (n + 1) → LocPot X) i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hP
  · simpa using hτ j

theorem cons_isPsh {n : ℕ} (A : FinHolAtlas (n + 1) X) (P : LocPot X)
    (τ : Fin n → LocPot X) (hP : IsPsh A P) (hτ : ∀ i, IsPsh A (τ i)) :
    ∀ i, IsPsh A ((Fin.cons P τ : Fin (n + 1) → LocPot X) i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hP
  · simpa using hτ j

theorem step {n : ℕ} [CompactSpace X] [T2Space X] (A : FinHolAtlas (n + 1) X) (Om : LocPot X)
    (τ : Fin n → LocPot X) (w v : X → ℝ) (hOm : IsPotential A Om) (hOmP : IsPsh A Om)
    (hτ : ∀ i, IsPotential A (τ i)) (hτP : ∀ i, IsPsh A (τ i)) (hw : A.Smooth w)
    (hwP : IsPsh A (Om + LocPot.ofFun w)) (hv : A.Smooth v) (hv1 : ∀ x, -1 ≤ v x)
    (hv0 : ∀ x, v x ≤ 0) :
    mInt A (Fin.cons (Om + LocPot.ofFun v) τ) (fun x => -w x) ≤
        mInt A (Fin.cons Om τ) (fun x => -w x) + mInt A (Fin.cons Om τ) (fun _ => 1) := by
  have cw := continuous_of_smooth A w hw
  have cv := continuous_of_smooth A v hv
  have pv := isPotential_ofFun A v hv
  have pw := isPotential_ofFun A w hw
  have pOmw := isPotentialAdd A Om _ hOm pw
  have I : ∀ P, IsPotential A P → ∀ g : X → ℝ, Continuous g →
      MIntegrable A (Fin.cons P τ) g := fun P hP g hg =>
    mIntegrableCont A _ (cons_isPotential A P τ hP hτ) g hg
  have h1 := mIntAdd A Om (LocPot.ofFun v) τ hOm pv hτ (fun x => -w x)
    (I _ hOm _ cw.neg) (I _ pv _ cw.neg)
  have h1' : mInt A (Fin.cons (LocPot.ofFun v) τ) (fun x => -w x) =
      -mInt A (Fin.cons (LocPot.ofFun v) τ) w :=
    mInt_neg A _ (cons_isPotential A _ τ pv hτ) w cw
  have h2 := byPartsSymm A w v hw hv τ hτ
  have h3 := mIntAdd A Om (LocPot.ofFun w) τ hOm pw hτ v (I _ hOm _ cv) (I _ pw _ cv)
  have h4 : mInt A (Fin.cons Om τ) v ≤ 0 := by
    have := mIntNonneg A (Fin.cons Om τ) (cons_isPotential A _ τ hOm hτ)
      (cons_isPsh A _ τ hOmP hτP) (fun x => -v x) (fun x => by linarith [hv0 x])
    rw [mInt_neg A _ (cons_isPotential A _ τ hOm hτ) v cv] at this
    linarith
  have h5 : 0 ≤ mInt A (Fin.cons (Om + LocPot.ofFun w) τ) v +
      mInt A (Fin.cons (Om + LocPot.ofFun w) τ) (fun _ => 1) := by
    have := mIntNonneg A (Fin.cons (Om + LocPot.ofFun w) τ) (cons_isPotential A _ τ pOmw hτ)
      (cons_isPsh A _ τ hwP hτP) (fun x => 1 * v x + 1) (fun x => by linarith [hv1 x])
    rw [mIntLinear A _ (cons_isPotential A _ τ pOmw hτ) 1 v (fun _ => 1) (I _ pOmw _ cv)
      (I _ pOmw _ continuous_const)] at this
    linarith
  have h6 := mIntAdd A Om (LocPot.ofFun w) τ hOm pw hτ (fun _ => 1)
    (I _ hOm _ continuous_const) (I _ pw _ continuous_const)
  have h7 := stokes A w hw τ hτ
  linarith

theorem step_mass {n : ℕ} [CompactSpace X] [T2Space X] (A : FinHolAtlas (n + 1) X)
    (Om : LocPot X) (τ : Fin n → LocPot X) (v : X → ℝ) (hOm : IsPotential A Om)
    (hτ : ∀ i, IsPotential A (τ i)) (hv : A.Smooth v) :
    mInt A (Fin.cons (Om + LocPot.ofFun v) τ) (fun _ => 1) =
      mInt A (Fin.cons Om τ) (fun _ => 1) := by
  have pv := isPotential_ofFun A v hv
  have h6 := mIntAdd A Om (LocPot.ofFun v) τ hOm pv hτ (fun _ => 1)
    (mIntegrableCont A _ (cons_isPotential A _ τ hOm hτ) _ continuous_const)
    (mIntegrableCont A _ (cons_isPotential A _ τ pv hτ) _ continuous_const)
  have h7 := stokes A v hv τ hτ
  linarith

theorem mInt_front {n : ℕ} (A : FinHolAtlas (n + 1) X) (Φ : Fin (n + 1) → LocPot X)
    (k : Fin (n + 1)) (g : X → ℝ) :
    mInt A Φ g = mInt A (Fin.cons (Φ k) (Fin.tail (Φ ∘ Equiv.swap 0 k))) g := by
  rw [← mIntSymm A Φ (Equiv.swap 0 k) g]
  congr 1
  conv_lhs => rw [← Fin.cons_self_tail (Φ ∘ Equiv.swap 0 k)]
  simp [Equiv.swap_apply_left]

theorem tail_update {n : ℕ} (Φ : Fin (n + 1) → LocPot X) (k : Fin (n + 1)) (P : LocPot X) :
    Fin.tail (Function.update Φ k P ∘ Equiv.swap 0 k) = Fin.tail (Φ ∘ Equiv.swap 0 k) := by
  funext j
  simp only [Fin.tail, Function.comp_apply]
  apply Function.update_of_ne
  intro h
  have := (Equiv.swap 0 k).injective (h.trans (Equiv.swap_apply_left 0 k).symm)
  exact Fin.succ_ne_zero j this

end ChernLevineNirenberg
end GlobalTheory

namespace GlobalTheory
namespace ChernLevineNirenberg

variable {X : Type} [TopologicalSpace X]

def mixedFactors {e : ℕ} (Om : LocPot X) (v : Fin e → X → ℝ) (S : Finset (Fin e)) :
    Fin e → LocPot X :=
  fun i => if i ∈ S then Om + LocPot.ofFun (v i) else Om

theorem bound_succ {n : ℕ} [CompactSpace X] [T2Space X] (A : FinHolAtlas (n + 1) X)
    (Om : LocPot X) (w : X → ℝ) (v : Fin (n + 1) → X → ℝ) (hOm : IsPotential A Om)
    (hOmP : IsPsh A Om) (hw : A.Smooth w) (hwP : IsPsh A (Om + LocPot.ofFun w))
    (hv : ∀ i, A.Smooth (v i) ∧ (∀ x, -1 ≤ v i x ∧ v i x ≤ 0) ∧
      IsPsh A (Om + LocPot.ofFun (v i))) (S : Finset (Fin (n + 1))) :
    mInt A (mixedFactors Om v S) (fun x => -w x) ≤
        mInt A (fun _ => Om) (fun x => -w x) + S.card * mInt A (fun _ => Om) (fun _ => 1) ∧
      mInt A (mixedFactors Om v S) (fun _ => 1) = mInt A (fun _ => Om) (fun _ => 1) := by
  have hP : ∀ S i, IsPotential A (mixedFactors Om v S i) ∧ IsPsh A (mixedFactors Om v S i) := by
    intro S i
    unfold mixedFactors
    split_ifs
    · exact ⟨isPotentialAdd A Om _ hOm (isPotential_ofFun A _ (hv i).1), (hv i).2.2⟩
    · exact ⟨hOm, hOmP⟩
  induction S using Finset.induction_on with
  | empty =>
    have : mixedFactors Om v ∅ = fun _ => Om := by funext i; simp [mixedFactors]
    rw [this]; simp
  | insert k S hk ih =>
    have hkS : mixedFactors Om v S k = Om := by simp [mixedFactors, hk]
    have hupd : mixedFactors Om v (insert k S) =
        Function.update (mixedFactors Om v S) k (Om + LocPot.ofFun (v k)) := by
      funext i
      by_cases h : i = k
      · subst h; simp [mixedFactors]
      · simp [mixedFactors, h, Function.update_of_ne h]
    set τ := Fin.tail (mixedFactors Om v S ∘ Equiv.swap 0 k) with hτdef
    have hτ : ∀ j, IsPotential A (τ j) ∧ IsPsh A (τ j) := fun j => hP S _
    have eS : ∀ g, mInt A (mixedFactors Om v S) g = mInt A (Fin.cons Om τ) g := by
      intro g; rw [mInt_front A _ k g, hkS]
    have eI : ∀ g, mInt A (mixedFactors Om v (insert k S)) g =
        mInt A (Fin.cons (Om + LocPot.ofFun (v k)) τ) g := by
      intro g
      rw [mInt_front A _ k g, hupd, tail_update, Function.update_self]
    have s1 := step A Om τ w (v k) hOm hOmP (fun j => (hτ j).1) (fun j => (hτ j).2) hw hwP
      (hv k).1 (fun x => ((hv k).2.1 x).1) (fun x => ((hv k).2.1 x).2)
    have s2 := step_mass A Om τ (v k) hOm (fun j => (hτ j).1) (hv k).1
    rw [eI, eI, s2, ← eS]
    rw [← eS, ← eS] at s1
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, ih2⟩
    rw [Finset.card_insert_of_notMem hk]
    push_cast
    rw [ih2] at s1
    linarith

theorem cln_bound : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Om : LocPot X) (w : X → ℝ) (v : Fin e → X → ℝ),
    IsPotential A Om → IsPsh A Om → A.Smooth w → (∀ x, w x ≤ 0) →
    IsPsh A (Om + LocPot.ofFun w) →
    (∀ i, A.Smooth (v i) ∧ (∀ x, -1 ≤ v i x ∧ v i x ≤ 0) ∧ IsPsh A (Om + LocPot.ofFun (v i))) →
    mInt A (fun i => Om + LocPot.ofFun (v i)) (fun x => -w x) ≤
      mInt A (fun _ => Om) (fun x => -w x) + e * mInt A (fun _ => Om) (fun _ => 1) := by
  intro e X _ _ _ A Om w v hOm hOmP hw _ hwP hv
  cases e with
  | zero =>
    have : (fun i : Fin 0 => Om + LocPot.ofFun (v i)) = fun _ => Om := funext fun i => i.elim0
    rw [this]; simp
  | succ n =>
    have h := (bound_succ A Om w v hOm hOmP hw hwP hv Finset.univ).1
    have hu : mixedFactors Om v Finset.univ = fun i => Om + LocPot.ofFun (v i) := by
      funext i; simp [mixedFactors]
    rw [hu, Finset.card_univ, Fintype.card_fin] at h
    exact h

end ChernLevineNirenberg
end GlobalTheory
