import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

def MixFamZeroStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (Φ : LocPot X) (w : X → ℝ),
    mixFam e 0 Φ w = fun _ => Φ

theorem mixFam_zero : MixFamZeroStatement := by
  intro e X _ Φ w
  funext k
  simp [mixFam]

def MixFamSuccStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (Φ : LocPot X) (w : X → ℝ) (i : ℕ) (hi : i < e),
    mixFam e (i + 1) Φ w = Function.update (mixFam e i Φ w) ⟨i, hi⟩ (Φ + LocPot.ofFun w) ∧
      mixFam e i Φ w ⟨i, hi⟩ = Φ

theorem mixFam_succ : MixFamSuccStatement := by
  intro e X _ Φ w i hi
  refine ⟨?_, by simp [mixFam]⟩
  funext k
  by_cases hk : k = ⟨i, hi⟩
  · subst hk
    simp [mixFam]
  · rw [Function.update_of_ne hk]
    have hk' : k.val ≠ i := fun h => hk (Fin.ext h)
    simp only [mixFam]
    by_cases h1 : k.val < i
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]

def MIntUpdateAddStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (F : Fin (e + 1) → LocPot X) (k : Fin (e + 1)) (P Q : LocPot X),
    (∀ i, IsPotential A (F i)) → IsPotential A P → IsPotential A Q → ∀ g : X → ℝ, Continuous g →
      mInt A (Function.update F k (P + Q)) g =
        mInt A (Function.update F k P) g + mInt A (Function.update F k Q) g

theorem update_comp_swap {e : ℕ} {X : Type} [TopologicalSpace X] (F : Fin (e + 1) → LocPot X)
    (k : Fin (e + 1)) (P : LocPot X) :
    Function.update F k P ∘ Equiv.swap 0 k = Fin.cons P (Fin.tail (F ∘ Equiv.swap 0 k)) := by
  funext j
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp
  · simp only [Function.comp_apply, Fin.cons_succ, Fin.tail]
    rw [Function.update_of_ne]
    rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    exact Fin.succ_ne_zero j'

theorem mInt_update_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X)
    (F : Fin (e + 1) → LocPot X) (k : Fin (e + 1)) (P : LocPot X) (g : X → ℝ) :
    mInt A (Function.update F k P) g = mInt A (Fin.cons P (Fin.tail (F ∘ Equiv.swap 0 k))) g := by
  rw [← update_comp_swap, mIntSymm]

theorem mInt_update_add : MIntUpdateAddStatement := by
  intro e X _ _ _ A F k P Q hF hP hQ g hg
  have hΦ : ∀ i, IsPotential A (Fin.tail (F ∘ Equiv.swap 0 k) i) := fun i => hF _
  rw [mInt_update_eq, mInt_update_eq A F k P, mInt_update_eq A F k Q]
  exact mIntAdd A P Q _ hP hQ hΦ g (mIntegrableCont A _ (fun i => Fin.cases hP hΦ i) g hg)
    (mIntegrableCont A _ (fun i => Fin.cases hQ hΦ i) g hg)

def MIntUpdateNonposStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (F : Fin (e + 1) → LocPot X) (k : Fin (e + 1)) (v : X → ℝ),
    A.Smooth v → (∀ i, IsPotential A (F i)) → (∀ i, i ≠ k → IsPsh A (F i)) →
      mInt A (Function.update F k (LocPot.ofFun v)) v ≤ 0

theorem mInt_update_nonpos : MIntUpdateNonposStatement := by
  intro e X _ _ _ A F k v hv hF hpsh
  have hΦ : ∀ i, IsPotential A (Fin.tail (F ∘ Equiv.swap 0 k) i) := fun i => hF _
  have hne : ∀ i : Fin e, Equiv.swap 0 k i.succ ≠ k := by
    intro i
    rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    exact Fin.succ_ne_zero i
  have hΦp : ∀ i, IsPsh A (Fin.tail (F ∘ Equiv.swap 0 k) i) := fun i => hpsh _ (hne i)
  rw [mInt_update_eq]
  exact byPartsNonpos A v hv _ hΦ hΦp

theorem energyStep : EnergyStepStatement := by
  intro e X _ _ _ A Φ w hΦ hw hΦp hΦwp i hi
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hi' : i < e' + 1 := by omega
  obtain ⟨hupd, hposition⟩ := mixFam_succ Φ w i hi'
  have hwP : IsPotential A (LocPot.ofFun w) := isPotential_ofFun A w hw
  have hΦw : IsPotential A (Φ + LocPot.ofFun w) := isPotentialAdd A _ _ hΦ hwP
  have hF : ∀ k, IsPotential A (mixFam (e' + 1) i Φ w k) := by
    intro k; simp only [mixFam]; split_ifs
    · exact hΦw
    · exact hΦ
  have hFp : ∀ k, IsPsh A (mixFam (e' + 1) i Φ w k) := by
    intro k; simp only [mixFam]; split_ifs
    · exact hΦwp
    · exact hΦp
  rw [hupd, mInt_update_add A _ _ Φ (LocPot.ofFun w) hF hΦ hwP w (projLine_continuous_of_smooth A hw)]
  have h1 : Function.update (mixFam (e' + 1) i Φ w) ⟨i, hi'⟩ Φ = mixFam (e' + 1) i Φ w := by
    exact Function.update_eq_self_iff.2 hposition.symm
  rw [h1]
  have h2 := mInt_update_nonpos A (mixFam (e' + 1) i Φ w) ⟨i, hi'⟩ w hw hF (fun k _ => hFp k)
  linarith

theorem energySum : EnergySumStatement := by
  intro e X _ _ _ A Φ w hΦ hw hΦp hΦwp
  have hmono : ∀ i, i ≤ e → mInt A (mixFam e i Φ w) w ≤ mInt A (fun _ => Φ) w := by
    intro i
    induction i with
    | zero => intro _; rw [mixFam_zero]
    | succ i ih =>
      intro hi
      exact (energyStep A Φ w hΦ hw hΦp hΦwp i hi).trans (ih (by omega))
  calc ∑ i ∈ Finset.range (e + 1), mInt A (mixFam e i Φ w) w
      ≤ ∑ i ∈ Finset.range (e + 1), mInt A (fun _ => Φ) w :=
        Finset.sum_le_sum fun i hi => hmono i (by simpa [Nat.lt_succ_iff] using hi)
    _ = ((e : ℝ) + 1) * mInt A (fun _ => Φ) w := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end

end ReciprocityTheory.AnForm.P
