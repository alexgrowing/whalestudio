import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

private theorem fix_mul {V : Type} [Monoid V] {l n : ℕ} {x : V} (h : x ^ l ^ n = x) (m : ℕ) : x ^ l ^ (n * m) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

private theorem fix_both {V : Type} [Monoid V] {l : ℕ} {x z : V} (hx : ∃ n : ℕ, 0 < n ∧ x ^ l ^ n = x)
    (hz : ∃ n : ℕ, 0 < n ∧ z ^ l ^ n = z) : ∃ n : ℕ, 0 < n ∧ x ^ l ^ n = x ∧ z ^ l ^ n = z := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hzb⟩ := hz
  refine ⟨a * b, Nat.mul_pos ha hb, fix_mul hxa b, ?_⟩
  rw [Nat.mul_comm]
  exact fix_mul hzb a

theorem UpperTheory.V.Ws.Po.nonAlg :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (Γ : Type) [Group Γ] (R : Type) [CommRing R] [Algebra O R]
      (ρ : Γ →* M4 R) (V : Type) [CommRing V] [IsLocalRing V] [CharP V l] (y : R →+* V), (∀ a ∈ maximalIdeal O, y (algebraMap O R a) = 0) →
      ∀ u ∈ Algebra.adjoin O (mono ρ 0), y u ∈ maximalIdeal V → y u ≠ 0 →
      ∃ x ∈ mono (mapRep y ρ) 0, ∀ n : ℕ, 0 < n → x ^ l ^ n ≠ x := by
  intro l _ O _ _ _ Γ _ R _ _ ρ V _ _ _ y hy u hu hum hu0
  by_contra hcon
  push_neg at hcon
  have key : ∀ v ∈ Algebra.adjoin O (mono ρ 0), ∃ n : ℕ, 0 < n ∧ (y v) ^ l ^ n = y v := by
    intro v hv
    induction hv using Algebra.adjoin_induction with
    | mem x hx =>
      apply hcon
      obtain ⟨L, hL, rfl⟩ := hx
      refine ⟨L, hL, ?_⟩
      rw [map_list_prod, List.map_map]
      rfl
    | algebraMap r =>
      let g : O →+* V := y.comp (algebraMap O R)
      have hg : ∀ a ∈ maximalIdeal O, g a = 0 := hy
      let f : ResidueField O →+* V := Ideal.Quotient.lift (maximalIdeal O) g hg
      have hf : Function.Injective f := f.injective
      haveI : CharP (ResidueField O) l := f.charP hf l
      letI : Fintype (ResidueField O) := Fintype.ofFinite _
      obtain ⟨m, -, hm⟩ := FiniteField.card (ResidueField O) l
      refine ⟨m, m.pos, ?_⟩
      have h1 : y (algebraMap O R r) = f (IsLocalRing.residue O r) :=
        (Ideal.Quotient.lift_mk (maximalIdeal O) g hg).symm
      rw [h1, ← map_pow, ← hm, FiniteField.pow_card]
    | add x z _ _ hx hz =>
      obtain ⟨n, hn, hxn, hzn⟩ := fix_both hx hz
      exact ⟨n, hn, by rw [map_add, add_pow_char_pow, hxn, hzn]⟩
    | mul x z _ _ hx hz =>
      obtain ⟨n, hn, hxn, hzn⟩ := fix_both hx hz
      exact ⟨n, hn, by rw [map_mul, mul_pow, hxn, hzn]⟩
  obtain ⟨n, hn, hun⟩ := key u hu
  obtain ⟨k, hk⟩ : ∃ k, l ^ n = k + 1 + 1 :=
    ⟨l ^ n - 2, by
      have := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
      omega⟩
  apply hu0
  have hmem : y u ^ (k + 1) ∈ maximalIdeal V := Ideal.pow_mem_of_mem _ hum _ (Nat.succ_pos k)
  have hunit : IsUnit (1 - y u ^ (k + 1)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).mp hmem)
  have h0 : y u * (1 - y u ^ (k + 1)) = 0 := by
    rw [mul_sub, mul_one, ← pow_succ', ← hk, hun, sub_self]
  exact hunit.mul_left_eq_zero.mp h0
