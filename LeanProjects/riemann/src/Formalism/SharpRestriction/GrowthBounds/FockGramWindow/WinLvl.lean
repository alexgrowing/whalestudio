import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.LettersAtUPos

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM Formalism.GM.M.PhiIntegrality Formalism.MainNotions.G.SymmetricFormBlocks
open scoped Nat

section Lvl

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem bnd_phisB (hB : G.BlockOK) (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hz : ∀ i, G.T.z i ≤ 2 * A)
    (j : Fin G.T.t → ℕ) (jp : ℕ) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : Bnd 1 u) :
    Bnd ((p : ℝ) ^ (G.T.t * ((r + 1) * lgN p A r))) (phisB p (r := r) G j jp u) := by
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
  have h := bnd_foldr (p := p) (fun i : Fin G.T.t =>
    Formalism.GM.tiePhi (k := ℚ_[p]) (fun c => (Sum.inl (M.finPos N (G.T.pos i), c) : M.BVar N r G.T.t))
      (fun c => Sum.inl (M.finPos N (G.T.pos i + 1), c))
      ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
      (G.T.z i)) ((r + 1) * lgN p A r) (List.finRange G.T.t)
    (fun i _ k u hu => by
      refine bnd_phi _ _ ?_ ?_ ?_ hr _ _ _ (lgN p A r) ?_ k u hu
      · intro c d h
        simpa using h
      · intro c d h
        simpa using h
      · intro c d h
        simp only [Sum.inl.injEq, Prod.mk.injEq] at h
        have h1 := congrArg Fin.val h.1
        have h2 : min (G.T.pos i) N = min (G.T.pos i + 1) N := h1
        have h3 := hB.2.1 i
        have h4 := G.uPos.2
        omega
      · refine log_le_lgN p A _ ?_
        have h1 := (lettersAt_le G j jp (G.letterAt (G.T.pos i))).trans (hdeg _)
        have h2 := (lettersAt_le G j jp (G.letterAt (G.T.pos i + 1))).trans (hdeg _)
        have h3 := hz i
        omega) 0 u (by simpa using hu)
  rw [List.length_finRange, zero_add] at h
  exact h

theorem int_lvl (hB : G.BlockOK) (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A)
    (hz : ∀ i, G.T.z i ≤ 2 * A) (j : Fin G.T.t → ℕ) (jp : ℕ) (l : ℕ) (hl : l ≤ JN G jp)
    (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : u ∈ Ljj p (r := r) G j jp) (hv : v ∈ Ljj p (r := r) G j jp) :
    ‖(p : ℚ_[p]) ^ (x0N p A r N G.T.t) *
      (mX (fun c => (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)) (fun c => M.xiVar N r G.T.t c) (JN G jp) l
        (phisB p (r := r) G j jp u) v / (degFact G j jp : ℚ_[p]))‖ ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ p := one_le_p
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have h1 := bnd_phisB p G hB A hdeg hz j jp u (Ljj_int p G j jp u hu)
  have h2 := bnd_Xl (fun c => (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)) (fun c => M.xiVar N r G.T.t c)
    (JN G jp) l hl _ (by positivity) _ h1
  have hJ : JN G jp ≤ 2 * A := (min_le_right _ _).trans ((Nat.sub_le _ _).trans hBa)
  have hlog : Nat.log p (JN G jp) ≤ lgN p A r := by
    have := log_le_lgN p (r := r) A (JN G jp) (by omega)
    omega
  have h3 : Bnd ((p : ℝ) ^ (G.T.t * ((r + 1) * lgN p A r) + (r + 1) * lgN p A r)) _ :=
    bnd_mono h2 (by
      rw [← pow_add]
      exact pow_le_pow_right₀ hp1 (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlog) _))
  have h4 := norm_fock_le _ v (degFact G j jp) (degFact_ne_zero G j jp) _
    (((N + 1) * r + (G.T.t + 1) * 2) * lgN p A r) h3 (Ljj_int p G j jp v hv) (Ljj_val p G A hdeg hBa j jp v hv)
  rw [ProjS.fockK_smul_left] at h4
  have hx : G.T.t * ((r + 1) * lgN p A r) + (r + 1) * lgN p A r + ((N + 1) * r + (G.T.t + 1) * 2) * lgN p A r =
      x0N p A r N G.T.t := by
    unfold x0N; ring
  rw [hx] at h4
  unfold mX
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, div_eq_inv_mul (M.fockK _ _)]
  rw [inv_mul_le_iff₀ (pow_pos hp0 _), mul_one]
  exact h4

end Lvl

theorem winLvl : WinLvl := by
  intro p _ N r _ G hB j jp _ A _ hdeg hBa hz n₁ f hf hli horth D hsmall z0 W h k hk hW hWh hJh
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
  have hJ : JN G jp ≤ 2 * A := (min_le_right _ _).trans ((Nat.sub_le _ _).trans hBa)
  have hV : ((min (G.LL.deg G.uPos - jp) (G.B - jp) : ℕ) : ℝ) / ((p : ℝ) - 1) -
      padicValNat p (min (G.LL.deg G.uPos - jp) (G.B - jp)).factorial ≤ (lgN p A r : ℝ) := by
    refine (Formalism.GM.MeanGammaLemmas.legendre' p _).trans ?_
    have := log_le_lgN p (r := r) A (JN G jp) (by omega)
    exact_mod_cast this
  exact win_abs (fun c => (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)) (fun c => M.xiVar N r G.T.t c)
    gramWindow2_proved
    (by intro c d h; simpa using h)
    (by intro c d h; simpa [M.xiVar] using h)
    (by
      intro c d h
      simp only [M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
      exact (Fin.castSucc_lt_last G.uPos).ne h.1)
    hr (G.LL.deg G.uPos - jp) (G.B - jp) (phisB p (r := r) G j jp) (degFact G j jp : ℚ_[p]) n₁ f hli
    (fun b => Ljj_biHom p G hB j jp (f b) (hf b)) (x0N p A r N G.T.t)
    (fun l hl a b => int_lvl p G hB A hdeg hBa hz j jp l hl (f a) (f b) (hf a) (hf b))
    horth D hsmall (lgN p A r : ℝ) hV z0 W h k hk hW hWh hJh

end Formalism.MainNotions.G.GramWindowAlt

end
