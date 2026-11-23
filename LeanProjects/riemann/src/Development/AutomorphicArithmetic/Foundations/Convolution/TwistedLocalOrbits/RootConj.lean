import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

section SlopeTestRemainingChoices

variable {E : Type} [Field E] {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {n : ℕ}

private def Bd (v : Valuation E Γ) (X : Matrix (Fin n) (Fin n) E) (c : Γ) : Prop := ∀ i j, v (X i j) ≤ c

private lemma Bd.add {v : Valuation E Γ} {X Y : Matrix (Fin n) (Fin n) E} {c : Γ} (hX : Bd v X c) (hY : Bd v Y c) :
    Bd v (X + Y) c := fun i j => by
  rw [Matrix.add_apply]; exact v.map_add_le (hX i j) (hY i j)

private lemma Bd.mul {v : Valuation E Γ} {X Y : Matrix (Fin n) (Fin n) E} {c d : Γ} (hX : Bd v X c) (hY : Bd v Y d) :
    Bd v (X * Y) (c * d) := fun i j => by
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun k _ => ?_
  rw [v.map_mul]
  exact mul_le_mul' (hX i k) (hY k j)

private lemma Bd.mono {v : Valuation E Γ} {X : Matrix (Fin n) (Fin n) E} {c d : Γ} (hX : Bd v X c) (h : c ≤ d) :
    Bd v X d := fun i j => (hX i j).trans h

private lemma Bd.one (v : Valuation E Γ) : Bd v (1 : Matrix (Fin n) (Fin n) E) 1 := fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> simp

private lemma val_nat_le (v : Valuation E Γ) (m : ℕ) : v (m : E) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.cast_succ]; exact v.map_add_le ih (by simp)

private lemma Bd.nsmul {v : Valuation E Γ} {X : Matrix (Fin n) (Fin n) E} {c : Γ} (hX : Bd v X c) (m : ℕ) :
    Bd v ((m : E) • X) c := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, v.map_mul]
  simpa using mul_le_mul' (val_nat_le v m) (hX i j)

private lemma Bd.pow_sub {v : Valuation E Γ} {B : Matrix (Fin n) (Fin n) E} {r : Γ} (hr : r ≤ 1)
    (hB : Bd v (B - 1) r) (m : ℕ) : Bd v (B ^ m - 1) r := by
  induction m with
  | zero => intro i j; simp
  | succ m ih =>
    have h1 : Bd v (B ^ m - 1 + 1) 1 := (ih.mono hr).add (Bd.one v)
    have h2 := (hB.mul h1).mono (mul_one r).le
    have e : B ^ (m + 1) - 1 = (B - 1) * (B ^ m - 1 + 1) + (B ^ m - 1) := by
      rw [pow_succ']; noncomm_ring
    rw [e]; exact h2.add ih

private lemma Bd.tele {v : Valuation E Γ} {A B g : Matrix (Fin n) (Fin n) E} {r c : Γ} (hr : r ≤ 1)
    (hA : Bd v (A - 1) r) (hB : Bd v (B - 1) r) (hh : Bd v (A * g - g * B) c) (m : ℕ) :
    Bd v (A ^ m * g - g * B ^ m - (m : E) • (A * g - g * B)) (r * c) := by
  induction m with
  | zero => intro i j; simp
  | succ m ih =>
    have hrc : r * c ≤ c := by simpa using mul_le_mul' hr (le_refl c)
    have h1 := hA.mul ((ih.mono hrc).add (hh.nsmul m))
    have h2 := (hh.mul (hB.pow_sub hr m)).mono (mul_comm c r).le
    have e : A ^ (m + 1) * g - g * B ^ (m + 1) - ((m + 1 : ℕ) : E) • (A * g - g * B) =
        (A - 1) * (A ^ m * g - g * B ^ m - (m : E) • (A * g - g * B) + (m : E) • (A * g - g * B)) +
          (A * g - g * B) * (B ^ m - 1) + (A ^ m * g - g * B ^ m - (m : E) • (A * g - g * B)) := by
      rw [Nat.cast_succ, add_smul, one_smul, pow_succ', pow_succ']
      generalize (m : E) • (A * g - g * B) = Z
      noncomm_ring
    rw [e]; exact (h1.add h2).add ih

private lemma intertwine (v : Valuation E Γ) {A B g : Matrix (Fin n) (Fin n) E} {r : Γ} {q : ℕ} (hq : r < v (q : E))
    (hA : Bd v (A - 1) r) (hB : Bd v (B - 1) r) (h : A ^ q * g = g * B ^ q) : A * g = g * B := by
  rw [← sub_eq_zero]
  ext i0 j0
  obtain ⟨⟨i, j⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v ((A * g - g * B) p.1 p.2)) ⟨(i0, j0), Finset.mem_univ _⟩
  have hh : Bd v (A * g - g * B) (v ((A * g - g * B) i j)) := fun a b => hmax (a, b) (Finset.mem_univ _)
  have ht := Bd.tele (hq.le.trans (val_nat_le v q)) hA hB hh q i j
  rw [h, sub_self, zero_sub, Matrix.neg_apply, v.map_neg, Matrix.smul_apply, smul_eq_mul, v.map_mul] at ht
  have h0 : v ((A * g - g * B) i j) = 0 := by
    by_contra hne
    exact absurd ht (not_le.2 (mul_lt_mul_of_pos_right hq (zero_lt_iff.2 hne)))
  have := hh i0 j0
  rw [h0, le_zero_iff, v.zero_iff] at this
  simpa using this

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Loc.rootConj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (q : ℕ) (r : ValueGroupWithZero E), r < valuation E (q : E) →
      ∀ u ∈ ball n r, ∀ u' ∈ ball n r, ∀ g : GL (Fin n) E, g⁻¹ * u ^ q * g = u' ^ q → g⁻¹ * u * g = u' := by
  intro E _ _ _ _ n q r hq u hu u' hu' g h
  have h1 : u ^ q * g = g * u' ^ q := by rw [← h]; group
  have h2 : (u : Matrix (Fin n) (Fin n) E) * g = g * u' :=
    intertwine (valuation E) hq (fun i j => hu i j) (fun i j => hu' i j)
      (by simpa using congrArg Units.val h1)
  have h3 : u * g = g * u' := Units.ext (by simpa using h2)
  rw [mul_assoc, h3]; group
