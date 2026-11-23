import Mathlib

noncomputable def UpperTheory.Reformulated.B.StrictlyUpperRank.IsStrictUpper.{u_1, u_2} :
    {𝕜 : Type u_1} → [RCLike 𝕜] → {n : Type u_2} → [LinearOrder n] → Matrix n n 𝕜 → Prop :=
    fun {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [inst_1 : LinearOrder n] (X : Matrix n n 𝕜) ↦
      ∀ (i j : n),
        @LE.le n
            (@Preorder.toLE n
              (@PartialOrder.toPreorder n
                (@SemilatticeInf.toPartialOrder n
                  (@Lattice.toSemilatticeInf n (@DistribLattice.toLattice n (@instDistribLatticeOfLinearOrder n inst_1))))))
            j i →
          @Eq 𝕜 (X i j)
            (@OfNat.ofNat 𝕜 (nat_lit 0)
              (@Zero.toOfNat0 𝕜
                (@MulZeroClass.toZero 𝕜
                  (@instMulZeroClassOfSemiring 𝕜
                    (@DivisionSemiring.toSemiring 𝕜
                      (@Semifield.toDivisionSemiring 𝕜
                        (@Field.toSemifield 𝕜
                          (@NormedField.toField 𝕜
                            (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst))))))))))

noncomputable def UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow.{u_2} :
    {n : Type u_2} → [Fintype n] → [LinearOrder n] → n → Nat :=
    fun {n : Type u_2} [Fintype n] [inst_1 : LinearOrder n] (i : n) ↦
      @Finset.card n
        {x : n |
          @LT.lt n
            (@Preorder.toLT n
              (@PartialOrder.toPreorder n
                (@SemilatticeInf.toPartialOrder n
                  (@Lattice.toSemilatticeInf n (@DistribLattice.toLattice n (@instDistribLatticeOfLinearOrder n inst_1))))))
            x i}

theorem UpperTheory.Reformulated.B.StrictlyUpperRank.rank_add_le_of_pow_ne_zero.{u_1, u_2} :
    ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [inst_1 : Fintype n] [inst_2 : LinearOrder n] {X : Matrix n n 𝕜},
      @UpperTheory.Reformulated.B.StrictlyUpperRank.IsStrictUpper 𝕜 inst n inst_2 X →
        ∀ (k : Nat) (i j : n),
          @Ne 𝕜
              (@HPow.hPow (Matrix n n 𝕜) Nat (Matrix n n 𝕜)
                (@instHPow (Matrix n n 𝕜) Nat
                  (@NPow.toPow (Matrix n n 𝕜)
                    (@Monoid.toNPow (Matrix n n 𝕜)
                      (@Semiring.toMonoid (Matrix n n 𝕜)
                        (@Matrix.semiring n 𝕜
                          (@DivisionSemiring.toSemiring 𝕜
                            (@Semifield.toDivisionSemiring 𝕜
                              (@Field.toSemifield 𝕜
                                (@NormedField.toField 𝕜
                                  (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst))))))
                          inst_1 fun (a b : n) ↦ @LinearOrder.toDecidableEq n inst_2 a b)))))
                X k i j)
              (@OfNat.ofNat 𝕜 (nat_lit 0)
                (@Zero.toOfNat0 𝕜
                  (@MulZeroClass.toZero 𝕜
                    (@instMulZeroClassOfSemiring 𝕜
                      (@DivisionSemiring.toSemiring 𝕜
                        (@Semifield.toDivisionSemiring 𝕜
                          (@Field.toSemifield 𝕜
                            (@NormedField.toField 𝕜
                              (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst)))))))))) →
            @LE.le Nat instLENat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow n inst_1 inst_2 i) k)
              (@UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow n inst_1 inst_2 j) := by
  intro 𝕜 _ n _ _ X hX k
  induction k with
  | zero =>
    intro i j h
    have hij : i = j := by
      by_contra hne
      exact h (by rw [pow_zero]; exact Matrix.one_apply_ne hne)
    subst hij
    exact le_rfl
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := ih i l (left_ne_zero_of_mul hl)
    have hlj : l < j := by
      by_contra hle
      exact right_ne_zero_of_mul hl (hX l j (not_lt.mp hle))
    have h2 : UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow l < UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow j := by
      unfold UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.trans hlj
      · have hm := @hsub l (by simpa using hlj)
        simp at hm
    omega
