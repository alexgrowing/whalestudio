import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters

open Polynomial

namespace GlobalTheory.FixedMemRange

theorem fixed_mem_range {g : ℕ} [hg : Fact (Nat.Prime g)] {d : ℕ} (hd : 0 < d)
    {w : AlgebraicClosure (ZMod g)} (hw : w ^ g ^ d = w) :
    ∃ k : GaloisField g d,
      ((IsAlgClosed.lift : GaloisField g d →ₐ[ZMod g] AlgebraicClosure (ZMod g)) : GaloisField g d → AlgebraicClosure (ZMod g)) k = w := by
  classical
  set ι : GaloisField g d →ₐ[ZMod g] AlgebraicClosure (ZMod g) := IsAlgClosed.lift with hι
  letI : Fintype (GaloisField g d) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField g d) = g ^ d := by rw [Fintype.card_eq_nat_card]; exact GaloisField.card g d hd.ne'
  have hq : 1 < g ^ d := Nat.one_lt_pow hd.ne' hg.out.one_lt
  set P : (AlgebraicClosure (ZMod g))[X] := X ^ (g ^ d) - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hq
  have hPdeg : P.natDegree = g ^ d := FiniteField.X_pow_card_sub_X_natDegree_eq _ hq
  have hsub : Finset.univ.image ι ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, mem_roots hP0]
    have hk : k ^ g ^ d = k := by
      rw [← hcard]; exact FiniteField.pow_card k
    simp [hP, IsRoot, sub_eq_zero, ← map_pow, hk]
  have hle : P.roots.toFinset.card ≤ (Finset.univ.image ι).card := by
    have hinj : Function.Injective ι := fun a b h => (RingHom.injective ι.toRingHom) h
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard, ← hPdeg]
    exact (Multiset.toFinset_card_le _).trans (card_roots' P)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hwm : w ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP0]
    simp [hP, IsRoot, sub_eq_zero, hw]
  rw [← heq] at hwm
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hwm
  exact ⟨k, hk⟩

theorem main : (let d1 : (g : ℕ) → ℕ → [Fact (Nat.Prime g)] → Type := @(fun (g d : ℕ) [Fact (Nat.Prime g)] ↦ GaloisField g d); let d2 : (g d : ℕ) → [inst : Fact (Nat.Prime g)] → d1 g d →ₐ[ZMod g] Formalism.CyclotomicNorms.Fbar g := @(fun (g d : ℕ) [Fact (Nat.Prime g)] ↦ IsAlgClosed.lift); ∀ {g : ℕ} [hg : Fact (Nat.Prime g)] {d : ℕ}, (0 : ℕ) < d → ∀ {w : Formalism.CyclotomicNorms.Fbar g}, w ^ g ^ d = w → ∃ (k : d1 g d), (d2 g d : d1 g d → Formalism.CyclotomicNorms.Fbar g) k = w) := by
  intro d1 d2 g hg d hd w hw
  exact fixed_mem_range hd hw

end GlobalTheory.FixedMemRange
