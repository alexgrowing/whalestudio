import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.AdOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.ArchUp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.DualZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LocHigh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LocLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.NormCnt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.AdicContinuousSumThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LcOfKer

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem sel_arith {V : Type} [Fintype V] (q C L N : ℕ) (hq : 0 < q) (d z : V → ℕ) (v : V)
    (h1 : ∀ w, q ^ (9 + 3 * d w) ≤ z w) (h2 : q ^ (10 + 3 * d v) ≤ C * z v)
    (h3 : q ^ 9 * ∏ w, z w ≤ L * (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V) (h4 : L ≤ N * q ^ 8) :
    q ^ 2 ≤ C * N := by
  classical
  have hv : v ∈ Finset.univ := Finset.mem_univ v
  obtain ⟨E, hE⟩ : ∃ E, E = ∏ w, q ^ (9 + 3 * d w) := ⟨_, rfl⟩
  have hEeq : E = (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V := by
    rw [hE]
    simp only [pow_add, pow_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Finset.prod_pow_eq_pow_sum]
    ring
  have hEpos : 0 < E := by
    rw [hE]
    exact Finset.prod_pos fun w _ => pow_pos hq _
  have key : q * E ≤ C * ∏ w, z w := by
    rw [hE, ← Finset.mul_prod_erase _ _ hv, ← Finset.mul_prod_erase _ _ hv]
    calc _ = q ^ (10 + 3 * d v) * ∏ w ∈ Finset.univ.erase v, q ^ (9 + 3 * d w) := by ring
      _ ≤ (C * z v) * ∏ w ∈ Finset.univ.erase v, z w :=
          Nat.mul_le_mul h2 (Finset.prod_le_prod' fun w _ => h1 w)
      _ = _ := by ring
  have main : q ^ 2 * (q ^ 8 * E) ≤ (C * N) * (q ^ 8 * E) := by
    calc q ^ 2 * (q ^ 8 * E) = q ^ 9 * (q * E) := by ring
      _ ≤ q ^ 9 * (C * ∏ w, z w) := Nat.mul_le_mul_left _ key
      _ = C * (q ^ 9 * ∏ w, z w) := by ring
      _ ≤ C * (L * (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V) := Nat.mul_le_mul_left _ h3
      _ ≤ C * (N * q ^ 8 * (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V) := by gcongr
      _ = (C * N) * (q ^ 8 * E) := by rw [hEeq]; ring
  exact Nat.le_of_mul_le_mul_right main (Nat.mul_pos (pow_pos hq 8) hEpos)

private theorem sel_cut (q a e z n C : ℕ) (hq : 0 < q) (h : q ^ (a + e) ≤ C * n) (h' : n * q ^ 9 ≤ z * q ^ 6) :
    q ^ (a + 3 + e) ≤ C * z := by
  have b : q ^ 6 * q ^ (a + 3 + e) ≤ q ^ 6 * (C * z) :=
    calc q ^ 6 * q ^ (a + 3 + e) = q ^ (a + e) * q ^ 9 := by ring
      _ ≤ C * n * q ^ 9 := Nat.mul_le_mul_right _ h
      _ = C * (n * q ^ 9) := by ring
      _ ≤ C * (z * q ^ 6) := Nat.mul_le_mul_left _ h'
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left b (pow_pos hq _)

private theorem card_mat (A : Type) : Nat.card (Matrix (Fin 3) (Fin 3) A) = Nat.card A ^ 9 := by
  show Nat.card (Fin 3 → Fin 3 → A) = _
  rw [Nat.card_fun, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  ring

theorem UpperTheory.V.Z.J.selLow :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ cw : F.Inf → F.Γ, (∀ w, cw w * cw w = 1 ∧ F.del (cw w) = -1) → GWL { F with cw := cw } → LocE F → ∀ (v : F.V) (i : Fin 2), UnitStep (F.Iv v) (F.eps.comp (F.loc v)) (triOf B v) i → ∃ C : ℕ, ∀ k, 0 < k → (ZN B k).Finite ∧ Nat.card (Ok l O k) ^ 2 ≤ C * (ZN B k).ncard := by
  intro l _ O _ _ _ _ _ F C₀ hF hl ρ B hρ hB hc cw hcw hG hE v i hU
  have T := triOk l O F C₀ hF hl ρ B hρ hB hc
  obtain ⟨C, hC⟩ := locHigh l O (F.Gv v) (F.Iv v) _ (F.dv v) (triOf B v) hl (hE v) (T v).2.1 (T v).1 i hU
  refine ⟨C, fun k hk => ?_⟩
  have hlow := fun w => locLow l O (F.Gv w) (F.Iv w) _ (F.dv w) (triOf B w) hl (hE w) (T w).2.1 (T w).1 k hk
  choose Z hZ1 hZ2 hZ3 hZ4 using fun w => zvCnt l O F C₀ hF hl ρ B hρ hB hc k hk w (hlow w).1
  obtain ⟨hfin, -, hkill, -⟩ := okFin l O hl
  haveI : Finite (Ok l O k) := hfin k
  have hq : 0 < Nat.card (Ok l O k) := Nat.card_pos
  haveI : Finite (Matrix (Fin 3) (Fin 3) (Ok l O k)) := inferInstanceAs (Finite (Fin 3 → Fin 3 → Ok l O k))
  have hk2 : ∀ x : Matrix (Fin 3) (Fin 3) (Ok l O k), l ^ k • x = 0 := fun x => by
    ext a b
    exact hkill k (x a b)
  have hop : IsOpen ((adK B k).ker : Set F.Γ) := by
    first
      | exact adOpen l O F C₀ hF hl B k hc
      | exact (adOpen l O F C₀ hF hl ρ B hρ hB hc k).1
  have hmain : (ZL F (adK B k) fun w => Z w).Finite ∧
      Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) * ∏ w, Nat.card (Z w) ≤
        (ZL F (adK B k) fun w => Z w).ncard * (HomMu l k F.eps (adK B k)).ncard *
        (∏ w, {x | adK B k (cw w) x = x}.ncard) * Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) ^ Fintype.card F.V :=
    hG k hk (Matrix (Fin 3) (Fin 3) (Ok l O k)) (adK B k) hk2 hop Z hZ2 hZ3
  have hZe : (fun w => (Z w : Set (F.Gv w → Matrix (Fin 3) (Fin 3) (Ok l O k)))) = Zv B k := funext hZ1
  rw [hZe, dualZero l O F C₀ hF hl ρ B hρ hB hc k hk, Set.ncard_singleton, mul_one, card_mat] at hmain
  have harch : (∏ w, {x | adK B k (cw w) x = x}.ncard) ≤ (Nat.card (Ok l O k) ^ 3) ^ (∑ w, F.dv w) := by
    have e : ∑ w, F.dv w = Fintype.card F.Inf := hF.card_inf.symm
    rw [e, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod' fun w _ => ?_
    exact archUp l O hl hF.l_odd (B.r (cw w)) (by rw [← map_mul, (hcw w).1, map_one])
      ((B.nu _).trans (hcw w).2) k hk
  refine ⟨hmain.1.subset fun z hz => hz.1, ?_⟩
  refine sel_arith _ C _ _ hq F.dv (fun w => Nat.card (Z w)) v (fun w => ?_) ?_ ?_
    (normCnt l O F C₀ hF hl ρ B hρ hB hc k hk (fun w => ⟨Z w, hZ1 w⟩) hmain.1)
  · have := sel_cut _ 6 (3 * F.dv w) _ _ 1 hq ((hlow w).2.trans (one_mul _).ge) (hZ4 w)
    rwa [one_mul] at this
  · exact sel_cut _ 7 (3 * F.dv v) _ _ C hq (hC k hk) (hZ4 v)
  · exact hmain.2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ harch))
