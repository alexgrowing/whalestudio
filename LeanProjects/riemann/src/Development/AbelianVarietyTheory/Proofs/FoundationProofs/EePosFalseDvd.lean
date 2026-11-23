import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.UpSplit

open GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

theorem cmul_add_left (f g h : ℕ → K) (n : ℕ) : cmul (f + g) h n = cmul f h n + cmul g h n := by
  simp [cmul, add_mul, sum_add_distrib]

theorem cmul_add_right (f g h : ℕ → K) (n : ℕ) : cmul f (g + h) n = cmul f g n + cmul f h n := by
  simp [cmul, mul_add, sum_add_distrib]

theorem cmul_vp_vp (p : ℕ) (hp : 0 < p) (f g : ℕ → K) (r : ℕ) :
    cmul (vp p f) (vp p g) (p * r) = cmul f g r := by
  unfold cmul
  symm
  have h1 : ∀ j ∈ range (r + 1), f j * g (r - j) = vp p f (p * j) * vp p g (p * r - p * j) := by
    intro j _
    simp only [vp, dvd_mul_right, if_true, ← Nat.mul_sub, Nat.mul_div_cancel_left _ hp]
  rw [sum_congr rfl h1, ← sum_image (f := fun i => vp p f i * vp p g (p * r - i)) (g := fun j => p * j)
    (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h)]
  apply sum_subset
  · intro i hi
    simp only [mem_image, mem_range] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    have : j ≤ r := by omega
    have := Nat.mul_le_mul_left p this
    omega
  · intro i hi hni
    simp only [mem_image, mem_range, not_exists, not_and] at hi hni
    by_cases hpi : p ∣ i
    · obtain ⟨j, rfl⟩ := hpi
      exact absurd rfl (hni j (by
        have : p * j ≤ p * r := by omega
        have := Nat.le_of_mul_le_mul_left this hp
        omega))
    · simp [vp, hpi]

theorem cmul_zero_left (p : ℕ) (A g : ℕ → K) (hA : ∀ i, p ∣ i → A i = 0) (r : ℕ) :
    cmul A (vp p g) (p * r) = 0 := by
  unfold cmul
  apply sum_eq_zero
  intro i hi
  have hi' : i ≤ p * r := Nat.lt_succ_iff.mp (mem_range.mp hi)
  by_cases hpi : p ∣ i
  · simp [hA i hpi]
  · have : ¬ p ∣ p * r - i := by
      intro h
      apply hpi
      have := Nat.dvd_sub (dvd_mul_right p r) h
      rwa [Nat.sub_sub_self hi'] at this
    simp [vp, this]

theorem cmul_zero_right (p : ℕ) (f B : ℕ → K) (hB : ∀ i, p ∣ i → B i = 0) (r : ℕ) :
    cmul (vp p f) B (p * r) = 0 := by
  unfold cmul
  apply sum_eq_zero
  intro i hi
  have hi' : i ≤ p * r := Nat.lt_succ_iff.mp (mem_range.mp hi)
  by_cases hpi : p ∣ i
  · have : p ∣ p * r - i := Nat.dvd_sub (dvd_mul_right p r) hpi
    simp [hB _ this]
  · simp [vp, hpi]

def ffTerm (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) (n d : ℕ) : K :=
  ψ ((n / d : ℕ) : ZMod (p ^ m)) * ((n / d : ℕ) : K) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (x * t * d) -
     ψ (-((n / d : ℕ) : ZMod (p ^ m))) * (-((n / d : ℕ) : K)) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (-(x * t * d))

theorem ffPos_true (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) (n : ℕ) :
    ffPos N p m k ψ x t ζ true n = ∑ d ∈ n.divisors, if ¬ p ∣ n / d then ffTerm N p m k ψ x t ζ n d else 0 := by
  simp [ffPos, ffTerm]

theorem ffPos_false (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) (n : ℕ) :
    ffPos N p m k ψ x t ζ false n =
      ∑ d ∈ n.divisors, if ¬ p ∣ d ∧ ¬ p ∣ n / d then ffTerm N p m k ψ x t ζ n d else 0 := by
  simp [ffPos, ffTerm]

theorem ffPos_split (N p m k : ℕ) [hp : Fact p.Prime] (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K)
    (n : ℕ) (hn : n ≠ 0) :
    ffPos N p m k ψ x t ζ true n = ffPos N p m k ψ x t ζ false n +
      (if p ∣ n then ffPos N p m k ψ ((p : ℤ) * x) t ζ true (n / p) else 0) := by
  have hp0 : 0 < p := hp.out.pos
  rw [ffPos_true, ffPos_false]
  have hsplit : (∑ d ∈ n.divisors, if ¬ p ∣ n / d then ffTerm N p m k ψ x t ζ n d else 0) =
      (∑ d ∈ n.divisors, if ¬ p ∣ d ∧ ¬ p ∣ n / d then ffTerm N p m k ψ x t ζ n d else 0) +
      ∑ d ∈ n.divisors, if p ∣ d ∧ ¬ p ∣ n / d then ffTerm N p m k ψ x t ζ n d else 0 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro d _
    by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ n / d <;> simp [h1, h2]
  rw [hsplit]
  congr 1
  split_ifs with hpn
  · obtain ⟨n', rfl⟩ := hpn
    have hn' : n' ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.mul_div_cancel_left _ hp0, ffPos_true]
    symm
    have h1 : ∀ e ∈ n'.divisors, (if ¬ p ∣ n' / e then ffTerm N p m k ψ ((p : ℤ) * x) t ζ n' e else 0) =
        (fun d => if p ∣ d ∧ ¬ p ∣ (p * n') / d then ffTerm N p m k ψ x t ζ (p * n') d else 0) (p * e) := by
      intro e _
      simp only [dvd_mul_right, true_and, Nat.mul_div_mul_left _ _ hp0]
      congr 1
      simp only [ffTerm, Nat.mul_div_mul_left _ _ hp0]
      push_cast
      ring_nf
    rw [sum_congr rfl h1, ← sum_image (f := fun d => if p ∣ d ∧ ¬ p ∣ (p * n') / d then ffTerm N p m k ψ x t ζ (p * n') d else 0)
      (g := fun e => p * e) (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp0 h)]
    apply sum_subset
    · intro d hd
      simp only [mem_image, Nat.mem_divisors] at hd ⊢
      obtain ⟨e, ⟨he, _⟩, rfl⟩ := hd
      exact ⟨Nat.mul_dvd_mul_left p he, by simpa using And.intro hp0.ne' hn'⟩
    · intro d hd hnd
      simp only [mem_image, Nat.mem_divisors, not_exists, not_and] at hd hnd
      split_ifs with hc
      · exfalso
        obtain ⟨e, rfl⟩ := hc.1
        exact hnd e ⟨(Nat.mul_dvd_mul_iff_left hp0).mp hd.1, hn'⟩ rfl
      · rfl
  · apply sum_eq_zero
    intro d hd
    rw [if_neg]
    rintro ⟨h1, _⟩
    exact hpn (h1.trans (Nat.dvd_of_mem_divisors hd))

theorem ffPos_false_dvd (N p m k : ℕ) [hp : Fact p.Prime] (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K)
    (n : ℕ) (hpn : p ∣ n) : ffPos N p m k ψ x t ζ false n = 0 := by
  rw [ffPos_false]
  apply sum_eq_zero
  intro d hd
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rw [← Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)] at hpn
  rcases (Nat.Prime.dvd_mul hp.out).mp hpn with h | h
  · exact h1 h
  · exact h2 h

def eeTerm (p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) (d : ℕ) : K :=
  ψ⁻¹ ((d : ℕ) : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (t * d) -
     ψ⁻¹ (-((d : ℕ) : ZMod (p ^ m))) * (ζ ^ (p ^ m)) ^ (-(t * d))

theorem eePos_true (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) (n : ℕ) :
    eePos N p m ψ t ζ true n = ∑ d ∈ n.divisors, if ¬ p ∣ d then eeTerm p m ψ t ζ d else 0 := by
  simp [eePos, eeTerm]

theorem eePos_false (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) (n : ℕ) :
    eePos N p m ψ t ζ false n = ∑ d ∈ n.divisors, if ¬ p ∣ n / d ∧ ¬ p ∣ d then eeTerm p m ψ t ζ d else 0 := by
  simp [eePos, eeTerm]

theorem eePos_split (N p m : ℕ) [hp : Fact p.Prime] (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K)
    (n : ℕ) (hn : n ≠ 0) :
    eePos N p m ψ t ζ true n = eePos N p m ψ t ζ false n +
      (if p ∣ n then eePos N p m ψ t ζ true (n / p) else 0) := by
  have hp0 : 0 < p := hp.out.pos
  rw [eePos_true, eePos_false]
  have hsplit : (∑ d ∈ n.divisors, if ¬ p ∣ d then eeTerm p m ψ t ζ d else 0) =
      (∑ d ∈ n.divisors, if ¬ p ∣ n / d ∧ ¬ p ∣ d then eeTerm p m ψ t ζ d else 0) +
      ∑ d ∈ n.divisors, if p ∣ n / d ∧ ¬ p ∣ d then eeTerm p m ψ t ζ d else 0 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro d _
    by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ n / d <;> simp [h1, h2]
  rw [hsplit]
  congr 1
  split_ifs with hpn
  · obtain ⟨n', rfl⟩ := hpn
    have hn' : n' ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.mul_div_cancel_left _ hp0, eePos_true]
    symm
    apply sum_subset_zero_on_sdiff
    · intro d hd
      simp only [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans (dvd_mul_left n' p), by simpa using And.intro hp0.ne' hn'⟩
    · intro d hd0
      obtain ⟨hd, hnd⟩ := mem_sdiff.mp hd0
      rw [Nat.mem_divisors] at hd hnd
      split_ifs with hc
      · exfalso
        obtain ⟨j, hj⟩ := hc.1
        apply hnd
        refine ⟨⟨j, ?_⟩, hn'⟩
        have h3 := Nat.div_mul_cancel hd.1
        rw [hj] at h3
        have : p * n' = p * (d * j) := by rw [← h3]; ring
        exact Nat.eq_of_mul_eq_mul_left hp0 this
      · rfl
    · intro d hd
      have hdn : d ∣ n' := Nat.dvd_of_mem_divisors hd
      have : p ∣ p * n' / d := by
        rw [Nat.mul_div_assoc _ hdn]; exact dvd_mul_right _ _
      simp [this]
  · apply sum_eq_zero
    intro d hd
    rw [if_neg]
    rintro ⟨h1, _⟩
    exact hpn (h1.trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))

theorem eePos_false_dvd (N p m : ℕ) [hp : Fact p.Prime] (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K)
    (n : ℕ) (hpn : p ∣ n) : eePos N p m ψ t ζ false n = 0 := by
  rw [eePos_false]
  apply sum_eq_zero
  intro d hd
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rw [← Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)] at hpn
  rcases (Nat.Prime.dvd_mul hp.out).mp hpn with h | h
  · exact h1 h
  · exact h2 h

theorem ffSer_split (N p m k : ℕ) [hp : Fact p.Prime] (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) :
    ffSer N p m k ψ x t ζ = (fun n => if n = 0 then 0 else ffPos N p m k ψ x t ζ false n) +
      vp p (ffSer N p m k ψ ((p : ℤ) * x) t ζ) := by
  funext n
  simp only [Pi.add_apply]
  by_cases hn : n = 0
  · subst hn; simp [ffSer, vp]
  · simp only [ffSer, hn, if_false, vp]
    rw [ffPos_split N p m k ψ x t ζ n hn]
    congr 1
    split_ifs with h1 h2
    · exact absurd h2 (by
        obtain ⟨j, rfl⟩ := h1
        have : j ≠ 0 := by rintro rfl; simp at hn
        simpa [Nat.mul_div_cancel_left _ hp.out.pos] using this)
    · rfl
    · rfl

theorem eeSer_split (N p m : ℕ) [hp : Fact p.Prime] (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) :
    eeSer N p m ψ t ζ = (fun n => if n = 0 then 0 else eePos N p m ψ t ζ false n) +
      vp p (eeSer N p m ψ t ζ) := by
  funext n
  simp only [Pi.add_apply]
  by_cases hn : n = 0
  · subst hn; simp [eeSer, vp]
  · simp only [eeSer, hn, if_false, vp]
    rw [eePos_split N p m ψ t ζ n hn]
    congr 1
    split_ifs with h1 h2
    · exact absurd h2 (by
        obtain ⟨j, rfl⟩ := h1
        have : j ≠ 0 := by rintro rfl; simp at hn
        simpa [Nat.mul_div_cancel_left _ hp.out.pos] using this)
    · rfl
    · rfl

end GlobalTheory.KummerEisensteinGalois.UpSplit

namespace GlobalTheory.KummerEisensteinGalois

open GlobalTheory.KummerEisensteinGalois.UpSplit in

theorem up_xSer_eq : ∀ (p : ℕ) [Fact p.Prime] (N m k : ℕ) (K : Type) [Field K] [CharZero K]
    (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K), IsPrimitiveRoot ζ (N * p ^ m) → 0 < N → ¬ p ∣ N →
    1 ≤ m → 3 ≤ k → ∀ r : ℕ,
    up p (xSer N p m k ψ x t ζ) r = up p (coPt N p m k ψ x t ζ) r + xSer N p m k ψ (p * x) t ζ r := by
  intro p hp N m k K _ _ ψ x t ζ _ _ _ _ _ r
  have hp0 : 0 < p := hp.out.pos
  have hX : xSer N p m k ψ x t ζ =
      cmul ((fun n => if n = 0 then 0 else ffPos N p m k ψ x t ζ false n) + vp p (ffSer N p m k ψ ((p : ℤ) * x) t ζ))
        ((fun n => if n = 0 then 0 else eePos N p m ψ t ζ false n) + vp p (eeSer N p m ψ t ζ)) := by
    rw [xSer]
    exact congrArg₂ cmul (ffSer_split N p m k ψ x t ζ) (eeSer_split N p m ψ t ζ)
  have hA : ∀ i, p ∣ i → (fun n => if n = 0 then 0 else ffPos N p m k ψ x t ζ false n) i = 0 := by
    intro i hi; simp only; split_ifs
    · rfl
    · exact ffPos_false_dvd N p m k ψ x t ζ i hi
  have hB : ∀ i, p ∣ i → (fun n => if n = 0 then 0 else eePos N p m ψ t ζ false n) i = 0 := by
    intro i hi; simp only; split_ifs
    · rfl
    · exact eePos_false_dvd N p m ψ t ζ i hi
  rw [up, hX, cmul_add_left, cmul_add_right, cmul_add_right, cmul_zero_left p _ _ hA, cmul_zero_right p _ _ hB,
    cmul_vp_vp p hp0, up, coPt, xSer]
  ring

end GlobalTheory.KummerEisensteinGalois
