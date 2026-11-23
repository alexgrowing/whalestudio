import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.FormalId

variable {R : Type} [CommRing R]

theorem uo_mul_vo (l : ℕ) (hl : 0 < l) (a b : ℕ → R) : Uo l (mul a (Vo l b)) = mul (Uo l a) b := by
  funext n
  simp only [Uo, mul, Vo, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun p => (l * p.1, l * p.2)) (fun p => (p.1 / l, p.2 / l))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    exact ⟨by rw [← mul_add, hp], dvd_mul_right _ _⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    have h3 : l ∣ p.1 := by
      have : l ∣ p.1 + p.2 := by rw [h1]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_left h2).mp this
    rw [← Nat.add_div_of_dvd_right h3, h1, Nat.mul_div_cancel_left _ hl]
  · intro p _
    simp [Nat.mul_div_cancel_left _ hl]
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨h1, h2⟩ := hp
    have h3 : l ∣ p.1 := by
      have : l ∣ p.1 + p.2 := by rw [h1]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_left h2).mp this
    ext <;> simp [Nat.mul_div_cancel' h3, Nat.mul_div_cancel' h2]
  · intro p _
    simp [Nat.mul_div_cancel_left _ hl]

theorem mul_comm' (a b : ℕ → R) : mul a b = mul b a := by
  funext n
  simp only [mul]
  conv_lhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  simp [_root_.mul_comm]

theorem mul_add_right' (a b b' : ℕ → R) : mul a (b + b') = mul a b + mul a b' := by
  funext n
  simp [mul, _root_.mul_add, Finset.sum_add_distrib]

theorem mul_add_left' (a a' b : ℕ → R) : mul (a + a') b = mul a b + mul a' b := by
  rw [mul_comm', mul_add_right', mul_comm' b, mul_comm' b]

theorem mul_lin (a b b' : ℕ → R) (c c' : R) :
    mul a (c • b + c' • b') = c • mul a b + c' • mul a b' := by
  funext n
  simp only [mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring

theorem zero_mul' (b : ℕ → R) : mul 0 b = 0 := by
  funext n; simp [mul]

theorem uo_dep (l : ℕ) (a : ℕ → R) : Uo l (dep l a) = 0 := by
  funext n; simp [Uo, dep]

theorem uo_vo (l : ℕ) (hl : 0 < l) (a : ℕ → R) : Uo l (Vo l a) = a := by
  funext n; simp [Uo, Vo, Nat.mul_div_cancel_left _ hl]

theorem dep_add (l : ℕ) (hl : 0 < l) (a : ℕ → R) : a = dep l a + Vo l (Uo l a) := by
  funext n
  by_cases h : l ∣ n
  · simp [dep, Vo, Uo, h, Nat.mul_div_cancel' h]
  · simp [dep, Vo, Uo, h]

theorem uo_add (l : ℕ) (x y : ℕ → R) : Uo l (x + y) = Uo l x + Uo l y := rfl

theorem uo_mul_dep (l : ℕ) (hl : 0 < l) (a b : ℕ → R) :
    Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b) := by
  have e : Uo l (mul a b) = Uo l (mul (dep l a) (dep l b)) + mul (Uo l a) (Uo l b) := by
    conv_lhs => rw [dep_add l hl a, dep_add l hl b]
    rw [mul_add_left', mul_add_right', mul_add_right', uo_add, uo_add, uo_add,
      uo_mul_vo l hl, uo_dep, zero_mul', mul_comm' (Vo l (Uo l a)) (dep l b), uo_mul_vo l hl, uo_dep,
      zero_mul', uo_mul_vo l hl, uo_vo l hl]
    abel
  rw [e]; abel

theorem to_vo (l k q : ℕ) (c : R) (a : ℕ → R) (hq : q.Coprime l) (hq0 : 0 < q) :
    To k c q (Vo l a) = Vo l (To k c q a) := by
  funext n
  simp only [To, Vo]
  by_cases hn : l ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp
    have h1 : l ∣ q * (l * m) := ⟨q * m, by ring⟩
    rw [if_pos h1, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl,
      show q * (l * m) = l * (q * m) by ring, Nat.mul_div_cancel_left _ hl]
    congr 1
    by_cases hqm : q ∣ m
    · obtain ⟨t, rfl⟩ := hqm
      rw [if_pos ⟨l * t, by ring⟩, if_pos (dvd_mul_right _ _),
        show l * (q * t) = q * (l * t) by ring, Nat.mul_div_cancel_left _ hq0, Nat.mul_div_cancel_left _ hq0,
        if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl]
    · rw [if_neg hqm, if_neg]
      intro h
      exact hqm ((Nat.Coprime.dvd_of_dvd_mul_left hq h))
  · have h1 : ¬ l ∣ q * n := fun h => hn (Nat.Coprime.dvd_of_dvd_mul_left hq.symm h)
    rw [if_neg h1, if_neg hn]
    by_cases hqn : q ∣ n
    · rw [if_pos hqn, if_neg]
      · simp
      · intro h
        obtain ⟨t, ht⟩ := hqn
        apply hn
        rw [ht, Nat.mul_div_cancel_left _ hq0] at h
        exact Dvd.dvd.mul_left h q |> fun h' => by rw [ht]; exact h'
    · simp [hqn]

theorem lam_lin (B : ℕ) (c a b : ℕ → R) (x y : R) :
    lam B c (x • a + y • b) = x * lam B c a + y * lam B c b := by
  simp only [lam, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.EisM.FormalId

theorem GlobalTheory.EisM.formal_identities : ∀ (R : Type) [CommRing R] (l : ℕ), 0 < l → (∀ a b : ℕ → R, Uo l (mul a (Vo l b)) = mul (Uo l a) b) ∧ (∀ a b : ℕ → R, Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b)) ∧ (∀ a b : ℕ → R, mul a b = mul b a) ∧ (∀ (a b b' : ℕ → R) (c c' : R), mul a (c • b + c' • b') = c • mul a b + c' • mul a b') ∧ (∀ (k q : ℕ) (c : R) (a : ℕ → R), q.Coprime l → 0 < q → To k c q (Vo l a) = Vo l (To k c q a)) ∧ (∀ (B : ℕ) (c a b : ℕ → R) (x y : R), lam B c (x • a + y • b) = x * lam B c a + y * lam B c b) := by
  intro R _ l hl
  exact ⟨FormalId.uo_mul_vo l hl, FormalId.uo_mul_dep l hl, FormalId.mul_comm', FormalId.mul_lin,
    fun k q c a hq hq0 => FormalId.to_vo l k q c a hq hq0, FormalId.lam_lin⟩
