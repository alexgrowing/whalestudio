import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BRaabe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem fib_iff {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (b' : (ZMod M)ˣ) (b : (ZMod N)ˣ) :
    ZMod.unitsMap h b' = b ↔ (b' : ZMod M).val % N = (b : ZMod N).val := by
  rw [Units.ext_iff, ZMod.unitsMap_def, Units.coe_map]
  simp only [MonoidHom.coe_coe, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ← (ZMod.val_injective N).eq_iff, ZMod.val_natCast]

private theorem fib_sum {N L M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (hM : M = N * L)
    (hc : ∀ n : ℕ, n.Coprime N → n.Coprime M) (f : ℕ → ℚ) (b : (ZMod N)ˣ) :
    ∑ b' ∈ Finset.univ.filter (fun b' : (ZMod M)ˣ => ZMod.unitsMap h b' = b), f (b' : ZMod M).val
      = ∑ j ∈ Finset.range L, f ((b : ZMod N).val + j * N) := by
  have hN : 0 < N := NeZero.pos N
  have hbN : (b : ZMod N).val < N := ZMod.val_lt _
  have hcop : ∀ n : ℕ, ((b : ZMod N).val + n * N).Coprime M := fun n =>
    hc _ (by simpa using ZMod.val_coe_unit_coprime b)
  have hlt : ∀ n ∈ Finset.range L, (b : ZMod N).val + n * N < M := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [hM]
    nlinarith
  symm
  refine Finset.sum_nbij' (fun n => ZMod.unitOfCoprime _ (hcop n)) (fun b' => (b' : ZMod M).val / N)
    ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [fib_iff, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt n hn),
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbN]
  · intro b' _
    rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hN, mul_comm, ← hM]
    exact ZMod.val_lt _
  · intro n hn
    simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (hlt n hn), Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hbN, zero_add]
  · intro b' hb'
    rw [Finset.mem_filter, fib_iff] at hb'
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, ← hb'.2, Nat.mod_add_div', ZMod.natCast_zmod_val]
  · intro n hn
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt n hn)]

private theorem sum_single_eq_single_sum {Γ : Type} [CommGroup Γ] {ι : Type} (s : Finset ι) (g : Γ) (F : ι → ℚ) :
    ∑ x ∈ s, MonoidAlgebra.single g (F x) = MonoidAlgebra.single g (∑ x ∈ s, F x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, ih, Finset.sum_insert ha, MonoidAlgebra.single_add]

private theorem theta_level {Γ : Type} [CommGroup Γ] {N L M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (hM : M = N * L)
    (hc : ∀ n : ℕ, n.Coprime N → n.Coprime M) (φ : (ZMod N)ˣ →* Γ) (k : ℕ) :
    thetaEl k (φ.comp (ZMod.unitsMap h)) = thetaEl k φ := by
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with hL | hL
    · exact absurd (hM.trans (by rw [hL, mul_zero])) (NeZero.ne M)
    · exact hL
  unfold thetaEl sumEl
  congr 1
  rw [← Finset.sum_fiberwise Finset.univ (ZMod.unitsMap h)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hfib : ∀ b' ∈ Finset.univ.filter (fun b' : (ZMod M)ˣ => ZMod.unitsMap h b' = b),
      MonoidAlgebra.single ((φ.comp (ZMod.unitsMap h)) b')⁻¹ (Ek M k (b' : ZMod M))
        = MonoidAlgebra.single (φ b)⁻¹ (Ek M k (b' : ZMod M)) := by
    intro b' hb'
    rw [Finset.mem_filter] at hb'
    rw [MonoidHom.comp_apply, hb'.2]
  rw [Finset.sum_congr rfl hfib, sum_single_eq_single_sum]
  congr 1
  unfold Ek
  rw [← Finset.sum_div, fib_sum h hM hc (fun n => bcoef M k n) b, hM,
    b_raabe N L k _ (NeZero.pos N) hLpos]

theorem UpperTheory.V.Odd.yLevel :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (k a : ℕ) (ha : a.Coprime N), 1 ≤ k → l ∣ N → ∀ (m M : ℕ) [NeZero M] (h : N ∣ M) (ha' : a.Coprime M), M = N * l ^ m → yEl k a ha' (φ.comp (ZMod.unitsMap h)) = yEl k a ha φ := by
  intro l _ Γ _ _ N _ φ k a ha hk hl m M _ h ha' hM
  have hc : ∀ n : ℕ, n.Coprime N → n.Coprime M := by
    intro n hn
    rw [hM]
    exact hn.mul_right ((Nat.Coprime.coprime_dvd_right hl hn).pow_right m)
  unfold yEl
  rw [theta_level h hM hc φ k]
  congr 4
  rw [MonoidHom.comp_apply]
  congr 1
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map]
  simp only [MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.coe_unitOfCoprime]
  exact ZMod.cast_natCast h a
