import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdicApprox

theorem exists_unit_eq_of_successive_approximation :
    ∀ (O S : Type) [CommRing O] [CommRing S] [Algebra O S] (I : Ideal O) [IsAdicComplete I S] (Q : ℕ → Ideal S) (N₀ : ℕ) (Nm : S → S) (t : S) (P₁ : Sˣ), (∀ m, Q (m + 1) ≤ Q m) → (∀ k, Q (N₀ * k + 1) ≤ Ideal.map (algebraMap O S) (I ^ k)) → Ideal.map (algebraMap O S) I ≤ Q 1 → (∀ x ∈ Q 1, IsUnit (1 + x)) → (∀ (k : ℕ) (x y : S), x - y ∈ Ideal.map (algebraMap O S) (I ^ k) → Nm x - Nm y ∈ Ideal.map (algebraMap O S) (I ^ k)) → t - Nm (P₁ : S) ∈ Q 1 → (∀ m, 1 ≤ m → ∀ P : Sˣ, t - Nm (P : S) ∈ Q m → ∃ P' : Sˣ, (P' : S) - (P : S) ∈ Q m ∧ t - Nm (P' : S) ∈ Q (m + 1)) → ∃ L : Sˣ, Nm (L : S) = t := by
  intro O S _ _ _ I _ Q N₀ Nm t P₁ hQ hN hIQ hU hNm h1 hstep
  have hmono : ∀ {a b : ℕ}, a ≤ b → Q b ≤ Q a := fun h => antitone_nat_of_succ_le hQ h
  have hstep' : ∀ (n : ℕ) (P : {P : Sˣ // t - Nm (P : S) ∈ Q (n + 1)}),
      ∃ P' : {P : Sˣ // t - Nm (P : S) ∈ Q (n + 1 + 1)},
        ((P'.1 : Sˣ) : S) - ((P.1 : Sˣ) : S) ∈ Q (n + 1) := by
    intro n P
    obtain ⟨P', h, h'⟩ := hstep (n + 1) (by omega) P.1 P.2
    exact ⟨⟨P', h'⟩, h⟩
  choose nxt hnxt using hstep'
  let sq : (n : ℕ) → {P : Sˣ // t - Nm (P : S) ∈ Q (n + 1)} :=
    fun n => Nat.rec ⟨P₁, h1⟩ (fun n p => nxt n p) n
  have hsq : ∀ n, (((sq (n + 1)).1 : Sˣ) : S) - (((sq n).1 : Sˣ) : S) ∈ Q (n + 1) :=
    fun n => hnxt n (sq n)
  have hdiff : ∀ m n, m ≤ n → (((sq n).1 : Sˣ) : S) - (((sq m).1 : Sˣ) : S) ∈ Q (m + 1) := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := (Q (m + 1)).add_mem (hmono (by omega : m + 1 ≤ n + 1) (hsq n)) ih
      simpa using this
  have hmem : ∀ {k : ℕ} {x : S}, x ∈ Ideal.map (algebraMap O S) (I ^ k) ↔
      x ∈ (I ^ k • ⊤ : Submodule O S) := by
    intro k x
    rw [Ideal.smul_top_eq_map]
    rfl
  let f : ℕ → S := fun k => (((sq (N₀ * k)).1 : Sˣ) : S)
  have hf : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule O S)] := by
    intro m n h
    rw [SModEq.sub_mem, ← hmem]
    have := hN m (hdiff (N₀ * m) (N₀ * n) (Nat.mul_le_mul_left _ h))
    rw [← neg_sub]
    exact Ideal.neg_mem_iff _ |>.2 this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := I) (M := S)) hf
  have hL' : ∀ n, f n - L ∈ Ideal.map (algebraMap O S) (I ^ n) := fun n => by
    have := hL n
    rw [SModEq.sub_mem] at this
    exact hmem.2 this
  have hNmL : Nm L = t := by
    have hz : t - Nm L = 0 := by
      apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I) (M := S))
      intro n
      rw [SModEq.zero, ← hmem]
      have a1 := hNm n _ _ (hL' n)
      have a2 : t - Nm (f n) ∈ Ideal.map (algebraMap O S) (I ^ n) := hN n (sq (N₀ * n)).2
      have := Ideal.add_mem _ a2 a1
      simpa using this
    exact (sub_eq_zero.1 hz).symm
  have hLQ : L - (P₁ : S) ∈ Q 1 := by
    have b1 : f 1 - L ∈ Q 1 := by
      have := hL' 1
      rw [pow_one] at this
      exact hIQ this
    have b2 : f 1 - (P₁ : S) ∈ Q 1 := hdiff 0 (N₀ * 1) (Nat.zero_le _)
    have := (Q 1).sub_mem b2 b1
    simpa using this
  have hunit : IsUnit L := by
    have hx : ((P₁⁻¹ : Sˣ) : S) * (L - (P₁ : S)) ∈ Q 1 := (Q 1).mul_mem_left _ hLQ
    have hu := (P₁.isUnit).mul (hU _ hx)
    have he : (P₁ : S) * (1 + ((P₁⁻¹ : Sˣ) : S) * (L - (P₁ : S))) = L := by
      rw [mul_add, ← mul_assoc, Units.mul_inv]
      ring
    rwa [he] at hu
  obtain ⟨u, rfl⟩ := hunit
  exact ⟨u, hNmL⟩

end GlobalTheory.CompanionTheory.AdicApprox
