import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.AddExt

theorem nat_comb {ι : Type} (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) {x0 : ι → ℕ} (hx0 : x0 ∈ S)
    (T : Finset S) (n : S → ℕ) :
    x0 + ∑ s ∈ T, n s • (s : ι → ℕ) ∈ S ∧
      c (x0 + ∑ s ∈ T, n s • (s : ι → ℕ)) = c x0 + ∑ s ∈ T, (n s : ℝ) * c s := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [hx0]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    suffices key : ∀ k : ℕ, x0 + (k • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ)) ∈ S ∧
        c (x0 + (k • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ))) =
          c x0 + ((k : ℝ) * c a + ∑ s ∈ T, (n s : ℝ) * c s) from key (n a)
    intro k
    induction k with
    | zero => simpa using ih
    | succ k ihk =>
      have e : x0 + ((k+1) • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ)) =
          (x0 + (k • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ))) + a := by
        rw [succ_nsmul]; abel
      rw [e]
      obtain ⟨h1, h2⟩ := hS _ ihk.1 _ a.2
      refine ⟨h1, ?_⟩
      rw [h2, ihk.2]; push_cast; ring

theorem ker_le {ι : Type} (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) {x0 : ι → ℕ} (hx0 : x0 ∈ S)
    (l : S →₀ ℤ)
    (hl : Finsupp.linearCombination ℤ (fun s : S => fun i => ((s : ι → ℕ) i : ℤ)) l = 0) :
    Finsupp.linearCombination ℤ (fun s : S => c s) l = 0 := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl ⊢
  obtain ⟨p, hp⟩ : ∃ p : S → ℕ, ∀ s, p s = (l s).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : S → ℕ, ∀ s, q s = (-l s).toNat := ⟨_, fun _ => rfl⟩
  have hpq : ∀ s, l s = (p s : ℤ) - q s := fun s => by
    rw [hp, hq]; omega
  have heq : ∑ s ∈ l.support, p s • (s : ι → ℕ) = ∑ s ∈ l.support, q s • (s : ι → ℕ) := by
    funext i
    have := congrFun hl i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hpq, sub_mul] at this
    rw [Finset.sum_sub_distrib, sub_eq_zero] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast this
  have h1 := (nat_comb S c hS hx0 l.support p).2
  have h2 := (nat_comb S c hS hx0 l.support q).2
  rw [heq, h2] at h1
  have h3 : ∑ s ∈ l.support, (p s : ℝ) * c s = ∑ s ∈ l.support, (q s : ℝ) * c s := by linarith
  simp only [hpq, zsmul_eq_mul, Int.cast_sub, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib, h3, sub_self]

theorem exists_linear : ∀ (ι : Type) [Fintype ι] (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ),
    (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) →
      ∃ κ : ι → ℝ, ∀ x ∈ S, c x = ∑ i, (x i : ℝ) * κ i := by
  intro ι _ S c hS
  classical
  rcases S.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
  · exact ⟨0, by simp [hE]⟩
  let v : S → ι → ℤ := fun s i => ((s : ι → ℕ) i : ℤ)
  let A : (S →₀ ℤ) →+ (ι → ℤ) := (Finsupp.linearCombination ℤ v).toAddMonoidHom
  let C : (S →₀ ℤ) →+ ℝ := (Finsupp.linearCombination ℤ (fun s : S => c s)).toAddMonoidHom
  have hker : A.ker ≤ C.ker := fun l hl =>
    AddMonoidHom.mem_ker.mpr (ker_le S c hS hx0 l (AddMonoidHom.mem_ker.mp hl))
  letI : DivisibleBy ℝ ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => ⟨u / n, by
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      show n • (u / (n : ℝ)) = u
      rw [nsmul_eq_mul]; field_simp⟩
  letI : DivisibleBy ℝ ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom
    (QuotientAddGroup.kerLift A) (QuotientAddGroup.kerLift_injective A)
    (QuotientAddGroup.lift A.ker C hker)
  refine ⟨fun i => g (Pi.single i 1), fun x hx => ?_⟩
  have h1 := DFunLike.congr_fun hg (QuotientAddGroup.mk (Finsupp.single ⟨x, hx⟩ 1))
  have hA : A (Finsupp.single ⟨x, hx⟩ 1) = ∑ i, ((x i : ℤ)) • (Pi.single i (1:ℤ) : ι → ℤ) := by
    ext j; simp [A, v, Finset.sum_apply, Pi.single_apply]
  have hC : C (Finsupp.single ⟨x, hx⟩ 1) = c x := by simp [C]
  simp only [AddMonoidHom.comp_apply, QuotientAddGroup.kerLift_mk, QuotientAddGroup.lift_mk] at h1
  rw [hA, hC, map_sum] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, zsmul_eq_mul, Int.cast_natCast]

end GlobalTheory.AddExt
