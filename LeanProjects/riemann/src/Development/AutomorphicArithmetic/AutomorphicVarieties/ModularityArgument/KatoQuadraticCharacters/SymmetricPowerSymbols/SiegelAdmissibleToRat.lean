import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.HolomorphicIntegrality.SgU
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitIndexAddIntVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTower

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem sieg_per {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c : ℕ} {x x' : Fin 2 → ℚ}
    (hx : GlobalTheory.Sieg.admitted c x) (h : ∀ i, ∃ j : ℤ, x' i = x i + j) : siegel X c x' = siegel X c x := by
  choose n hn using h
  have e : sgC c x' = sgC c x := by
    funext z
    rw [show x' = fun i => x i + n i from funext hn]
    exact GlobalTheory.Sieg.Per.sg_add_int c x n _ hx
  unfold siegel
  rw [e]

private theorem siegel_admissible_periodic {c : ℕ} {x x' : Fin 2 → ℚ}
    (hx : GlobalTheory.Sieg.admitted c x) (h : ∀ i, ∃ j : ℤ, x' i = x i + j) : GlobalTheory.Sieg.admitted c x' := by
  choose n hn using h
  rw [show x' = fun i => x i + n i from funext hn]
  exact GlobalTheory.Sieg.Per.isAdmissibleSmoothingFactor_add_intVector hx n

private theorem near {M : ℕ} (hM : 0 < M) (a : ℤ) (y : ZMod M) (h : (a : ZMod M) = y) :
    ∃ j : ℤ, (a : ℚ) / M = (y.val : ℚ) / M + j := by
  haveI : NeZero M := ⟨hM.ne'⟩
  have h1 : ((y.val : ℤ) : ZMod M) = (a : ZMod M) := by rw [h]; simp
  obtain ⟨j, hj⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
  refine ⟨j, ?_⟩
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have h2 : (a : ℚ) - (y.val : ℚ) = M * j := by exact_mod_cast hj
  field_simp
  linear_combination h2

private theorem siegel_admissible_to_rat {c M : ℕ} (hc : 1 < c) (h6 : Nat.Coprime c 6) (hM : 0 < M) (hcM : Nat.Coprime c M) {x : Row M}
    (hx : x ≠ 0) : GlobalTheory.Sieg.admitted c (toQ M x) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have key : ∀ i, (c : ℚ) * toQ M x i ∈ Set.range ((↑) : ℤ → ℚ) → x i = 0 := by
    rintro i ⟨j, hj⟩
    have h1 : (j : ℚ) * M = c * ((x i).val : ℚ) := by
      rw [hj]; unfold toQ; field_simp
    have h2 : j * (M : ℤ) = (c : ℤ) * ((x i).val : ℤ) := by exact_mod_cast h1
    have h3 : (c : ZMod M) * x i = 0 := by
      have := congrArg (Int.cast : ℤ → ZMod M) h2
      simpa using this.symm
    exact ((ZMod.isUnit_iff_coprime c M).2 hcM).mul_right_eq_zero.1 h3
  refine ⟨hc, h6, fun h => hx ?_⟩
  funext i
  fin_cases i
  · exact key 0 h.1
  · exact key 1 h.2

theorem UpperTheory.V.Z.Kato.Sym.sgB :
    UpperTheory.V.Z.Kato.Sym.SgB := by
  intro Ω _ _ _ ε X c M hc h6 hM hcM x hx
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hA := siegel_admissible_to_rat hc h6 hM hcM hx
  refine ⟨KU.sgU Ω ε X c _ hA, fun γ => ?_, fun s => ?_, fun x' h => sieg_per X hA h⟩
  · unfold sg
    rw [SiegelSL.sl_siegel Ω ε X c _ γ hA]
    have hn : ∀ i, ∃ j : ℤ, GlobalTheory.Sieg.act (toQ M x) γ i = toQ M (rt x γ) i + j := by
      intro i
      obtain ⟨j, hj⟩ := near hM (∑ k, ((x k).val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) k i) (rt x γ i)
        (by simp [rt, Matrix.vecMul, dotProduct])
      refine ⟨j, ?_⟩
      unfold toQ
      rw [← hj]
      simp only [GlobalTheory.Sieg.act, Fin.sum_univ_two]
      push_cast
      ring
    have hne : rt x γ ≠ 0 := by
      intro h0
      apply hx
      have : rt (rt x γ) γ⁻¹ = x := by
        unfold rt
        rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul]
        simp
      rw [← this, h0]
      simp [rt]
    exact sieg_per X (siegel_admissible_to_rat hc h6 hM hcM hne) hn
  · obtain ⟨-, -, -, -, -, -, hL⟩ := lgB Ω ε X M hM
    have h0 : IsPrimitiveRoot (eOm ε (1 / (M : ℚ))) M := isPrimitiveRoot_eOm ε hM.ne'
    have hs : s (eOm ε (1 / M)) = eOm ε (((cyc M s).val : ℕ) / M) := by
      rw [(hL s s).2.2 _ h0.pow_eq_one]
      apply ε.injective
      rw [map_pow, GalUnits.eps_eOm, GalUnits.eps_eOm]
      unfold GlobalTheory.Sieg.ee
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hu : cyc M s⁻¹ * cyc M s = 1 := by
      rw [← (hL s⁻¹ s).1, inv_mul_cancel, (hL s s).2.1]
    have hne : gr M s x ≠ 0 := by
      intro h
      apply hx
      have a0 : x 0 = 0 := by simpa [gr] using congrFun h 0
      have a1 : cyc M s * x 1 = 0 := by simpa only [gr, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] using congrFun h 1
      have a2 : x 1 = 0 := by rw [← one_mul (x 1), ← hu, mul_assoc, a1, mul_zero]
      funext i
      fin_cases i
      · exact a0
      · exact a2
    have hB := siegel_admissible_to_rat hc h6 hM hcM hne
    have e1 : toQ M x = ![((x 0).val : ℚ) / M, ((x 1).val : ℚ) / M] := by
      funext i; fin_cases i <;> rfl
    have hn : ∀ i, ∃ j : ℤ, (![((x 0).val : ℚ) / M, (((cyc M s).val * (x 1).val : ℕ) : ℚ) / M] : Fin 2 → ℚ) i =
        toQ M (gr M s x) i + j := by
      intro i
      fin_cases i
      · exact ⟨0, by simp [toQ, gr]⟩
      · obtain ⟨j, hj⟩ := near hM (((cyc M s).val * (x 1).val : ℕ) : ℤ) (cyc M s * x 1) (by simp)
        exact ⟨j, by simpa [toQ, gr] using hj⟩
    unfold sg
    rw [← sieg_per X hB hn, e1]
    exact gal_siegel Ω ε X c M _ _ _ s hM (ZMod.val_lt _) hs (e1 ▸ hA) (siegel_admissible_periodic hB hn)
