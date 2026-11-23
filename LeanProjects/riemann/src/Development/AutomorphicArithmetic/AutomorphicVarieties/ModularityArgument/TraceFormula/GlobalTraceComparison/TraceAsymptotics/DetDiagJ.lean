import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

private theorem prod_lt {R : Type} [CommMonoid R] (p : R) (j : ℕ) :
    ∀ n, ∏ k ∈ Finset.range n, (if k < j then p else 1) = p ^ (min n j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    by_cases h : n < j
    · rw [if_pos h, min_eq_left h.le, min_eq_left (Nat.succ_le_of_lt h), pow_succ]
    · rw [if_neg h, mul_one, min_eq_right (not_lt.1 h), min_eq_right (by omega)]

private theorem det_diagJ {L : Type} [Field L] (n : ℕ) (p : L) {i : ℕ} (hi : i ≤ n) : (diagJ n p i).det = p ^ i := by
  rw [diagJ, det_diagonal, Fin.prod_univ_eq_prod_range (fun k => if k < i then p else 1) n, prod_lt, min_eq_right hi]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem v_le (w : Pl E) (n : ℕ) : ∀ k ∈ GLint (Fin n) (Ov E w),
    Valued.v ((GeneralLinearGroup.det k : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
  rintro _ ⟨x, rfl⟩
  exact (congrArg (fun y => Valued.v y ≤ 1) (det_map (Ov E w).subtype x)).mpr (GeneralLinearGroup.det x).1.2

private theorem v_eq (w : Pl E) (n : ℕ) {k : GLw n w} (hk : k ∈ GLint (Fin n) (Ov E w)) :
    Valued.v ((GeneralLinearGroup.det k : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
  have h3 := v_le w n _ (inv_mem hk)
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 (Units.ne_zero _)))] at h3
  exact le_antisymm (v_le w n k hk) h3

private theorem unifV (w : Pl E) : IsUnifV E w (unif w) :=
  Classical.epsilon_spec (exists_isUnifV w)

private theorem unif_ne (w : Pl E) : unif w ≠ 0 := by
  intro e
  have h := unifV w
  rw [IsUnifV, e, map_zero] at h
  exact WithZero.coe_ne_zero h.symm

private theorem loc_unif (w : Pl E) (μ : HChar E) (hμ : μ.UnrAt w) :
    μ.loc w (Units.mk0 (unif w) (unif_ne w)) = μ.val w := by
  have h : μ.loc w (Units.mk0 (unif w) (unif_ne w) * (atFin w (Formalism.L2.Host.unif w))⁻¹) = 1 := by
    refine hμ _ ?_
    have h1 : Valued.v ((atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = WithZero.exp (-1 : ℤ) :=
      Formalism.L2.Host.unif_spec w
    have h2 : Valued.v (unif w) = WithZero.exp (-1 : ℤ) := unifV w
    rw [IsUnitAt, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h1, Units.val_mk0, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero
  rw [map_mul, map_inv, mul_inv_eq_one] at h
  exact h

private theorem loc_det (w : Pl E) (μ : HChar E) (hμ : μ.UnrAt w) {n i : ℕ} (hi : i ≤ n) (g : GLw n w)
    (h : Tj ℂ n (Ov E w) (unif w) i g ≠ 0) : μ.loc w (GeneralLinearGroup.det g) = μ.val w ^ i := by
  have hm : g ∈ {g : GLw n w | ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * diagJ n (unif w) i * (b : Matrix (Fin n) (Fin n) (w.adicCompletion E))} := by
    by_contra hn
    exact h (Set.indicator_of_notMem hn _)
  obtain ⟨x, hx, y, hy, e⟩ := hm
  have hd : GeneralLinearGroup.det g = GeneralLinearGroup.det x * Units.mk0 (unif w) (unif_ne w) ^ i * GeneralLinearGroup.det y := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, GeneralLinearGroup.val_det_apply]
    rw [e, det_mul, det_mul, det_diagJ _ _ hi]
  rw [hd, map_mul, map_mul, map_pow, hμ _ (v_eq w n hx), hμ _ (v_eq w n hy), loc_unif w μ hμ, one_mul, mul_one]

private theorem chi_eq (w : Pl E) (μ : HChar E) (hμ : μ.UnrAt w) (a b : ℕ) (m : GLw a w × GLw b w) :
    chi μ a b w m = ((μ.loc w (GeneralLinearGroup.det m.1) ^ b * μ.loc w (GeneralLinearGroup.det m.2) ^ a : ℂˣ) : ℂ) := by
  have h1 : μ.loc w (-1) = 1 := hμ _ (by simp [IsUnitAt])
  rw [chi, map_mul, map_mul, map_pow, map_pow, map_pow, h1, one_pow, one_mul]

theorem muTw : MuTw := by
  intro E _ _ _ w μ hμ a b
  refine ⟨fun m hm => ?_, fun m m' => ?_, fun i j m hi hj h => ?_⟩
  · rw [chi_eq w μ hμ, hμ _ (v_eq w a hm.1), hμ _ (v_eq w b hm.2)]
    simp
  · rw [chi_eq w μ hμ, chi_eq w μ hμ, chi_eq w μ hμ, ← Units.val_mul]
    congr 1
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    exact mul_mul_mul_comm _ _ _ _
  · rw [chi_eq w μ hμ, loc_det w μ hμ hi m.1 (left_ne_zero_of_mul h), loc_det w μ hμ hj m.2 (right_ne_zero_of_mul h)]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
