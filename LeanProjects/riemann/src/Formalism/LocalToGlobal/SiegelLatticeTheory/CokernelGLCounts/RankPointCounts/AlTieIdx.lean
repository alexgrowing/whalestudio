import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IndexTypC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieFD
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedFinal

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTieIdx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_one_sub_inv_pow_pos (q : ℝ) (hq : 1 < q) (s : Finset ℕ) (hs : ∀ j ∈ s, 1 ≤ j) :
    0 < ∏ j ∈ s, (1 - 1 / q ^ j) :=
  Finset.prod_pos fun j hj => by
    have h1 : 1 < q ^ j := one_lt_pow₀ hq (by have := hs j hj; omega)
    have h2 : 1 / q ^ j < 1 := by rw [div_lt_one (by linarith)]; exact h1
    linarith

theorem cardGL_A (g m : ℕ) [hg : Fact g.Prime] :
    (Nat.card (GL (Fin m) (ZMod g)) : ℝ) = (g : ℝ) ^ (m * m) * ∏ j ∈ Finset.Ioc 0 m, (1 - 1 / (g : ℝ) ^ j) := by
  have hq0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.out.ne_zero
  rw [Matrix.card_GL_field, ZMod.card, Nat.cast_prod]
  have hterm : ∀ i : Fin m, (((g ^ m - g ^ (i : ℕ) : ℕ)) : ℝ) = (g : ℝ) ^ m * (1 - 1 / (g : ℝ) ^ (m - i)) := by
    intro i
    rw [Nat.cast_sub (Nat.pow_le_pow_right hg.out.pos i.2.le), Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one,
      mul_one_div, div_eq_mul_inv, ← pow_sub₀ _ hq0 (Nat.sub_le m i), Nat.sub_sub_self i.2.le]
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun i => 1 - 1 / (g : ℝ) ^ (m - i)) m]
  have h1 : ∏ i ∈ Finset.range m, (1 - 1 / (g : ℝ) ^ (m - i)) =
      ∏ i ∈ Finset.range m, (fun j => 1 - 1 / (g : ℝ) ^ (j + 1)) (m - 1 - i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    show _ = 1 - 1 / (g : ℝ) ^ (m - 1 - i + 1)
    rw [show m - 1 - i + 1 = m - i by omega]
  rw [h1, Finset.prod_range_reflect (fun j => 1 - 1 / (g : ℝ) ^ (j + 1)) m, Finset.range_eq_Ico,
    Finset.prod_Ico_add' (fun j => 1 - 1 / (g : ℝ) ^ j) 0 m 1]
  have h2 : Finset.Ico (0 + 1) (m + 1) = Finset.Ioc 0 m := by ext; simp; omega
  rw [h2]

theorem idx_arith (g r k : ℕ) (hg : g.Prime) :
    (glkC k g : ℝ) * (nnC r k g : ℝ) / (ggC r k g : ℝ) =
      (g : ℝ) ^ (-(((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ)) /
        ∏ i ∈ Finset.Icc (k + 1) (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ i) := by
  have : Fact g.Prime := ⟨hg⟩
  have hq : (1 : ℝ) < g := by exact_mod_cast hg.one_lt
  have hq0 : (g : ℝ) ≠ 0 := by linarith
  have hc : Fintype.card (Formalism.FourierDecayAlt.S3.Idx r k) = 2 * r + k + 1 := by
    simp only [Formalism.FourierDecayAlt.S3.Idx, Formalism.FourierDecayAlt.S3.Mid, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  have hG : (ggC r k g : ℝ) = (Nat.card (GL (Fin (2 * r + k + 1)) (ZMod g)) : ℝ) := by
    unfold ggC
    exact_mod_cast Nat.card_congr
      (Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod g) (ZMod g) (Fintype.equivFinOfCardEq hc)).toMulEquiv)
  have hN : (nnC r k g : ℝ) = (g : ℝ) ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
    unfold nnC
    rw [MassDataIdxStIm.card_isN, ZMod.card]
    push_cast
    try rfl
  unfold glkC
  rw [hG, hN, cardGL_A, cardGL_A]
  have hIcc : Finset.Icc (k + 1) (2 * r + k + 1) = Finset.Ioc k (2 * r + k + 1) := by
    ext; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, ← Finset.prod_Ioc_consecutive _ (Nat.zero_le k) (by omega : k ≤ 2 * r + k + 1)]
  have hA : 0 < ∏ j ∈ Finset.Ioc 0 k, (1 - 1 / (g : ℝ) ^ j) :=
    prod_one_sub_inv_pow_pos _ hq _ (fun j hj => (Finset.mem_Ioc.1 hj).1)
  have hB : 0 < ∏ j ∈ Finset.Ioc k (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ j) :=
    prod_one_sub_inv_pow_pos _ hq _ (fun j hj => by have := (Finset.mem_Ioc.1 hj).1; omega)
  have hpow : (g : ℝ) ^ (k * k) * (g : ℝ) ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) /
      (g : ℝ) ^ ((2 * r + k + 1) * (2 * r + k + 1)) = (g : ℝ) ^ (-(((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ)) := by
    rw [← pow_add, ← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hq0]
    congr 1
    rcases r with _ | s
    · simp; ring
    · simp only [Nat.add_sub_cancel]; push_cast; ring
  rw [← hpow]
  generalize (∏ j ∈ Finset.Ioc 0 k, (1 - 1 / (g : ℝ) ^ j)) = A at hA ⊢
  generalize (∏ j ∈ Finset.Ioc k (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ j)) = B at hB ⊢
  have hA' := hA.ne'
  have hB' := hB.ne'
  have hgn : (g : ℝ) ^ ((2 * r + k + 1) * (2 * r + k + 1)) ≠ 0 := pow_ne_zero _ hq0
  field_simp
  try ring

variable {D : D7} (X : HidaSetting D)

theorem ratio_eq (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal / (MassDataIdxSteps.muP X p (MassDataIdxSteps.KvX X p)).toReal =
      (glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ) / (ggC D.R.rS D.R.k (gOf p) : ℝ) := by
  obtain ⟨j, hj, hj0, hμj, hB0, hBt⟩ := MassDataIdxSteps.measB_of X MassDataIdxSteps.haarIdx MassDataIdxSteps.redIdx u p
    (MassDataIdxSteps.stTop X p) (Formalism.L2.SG.Pf.MassDataX.stK_holds X p) (Formalism.L2.SG.Pf.MassDataX.stRed_holds X p)
    (Formalism.L2.SG.Pf.MassDataX.stImB_holds X hb u p)
  have h1 : (MassDataIdxSteps.muP X p (MassDataIdxSteps.KvX X p)).toReal =
      (j : ℝ) * (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal := by
    rw [hμj, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hpos : (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hB0, hBt⟩
  rw [h1, ← hj]
  rcases eq_or_ne (j : ℝ) 0 with h0 | h0
  · simp [h0]
  · rw [mul_comm (j : ℝ) (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal, mul_comm (j : ℝ),
      div_mul_eq_div_div, div_self hpos, div_mul_eq_div_div, div_self hj0]

theorem gAt_eq (p : TypX X) : gAt X p.1 = gOf p := by
  unfold gAt gOf
  split_ifs <;> rfl

theorem aP_typed (u : D.what₂.Word) (p : TypX X) :
    aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u) =
      ∏ i ∈ Finset.Icc (D.R.k + 1) (2 * D.R.rS + D.R.k + 1), (1 - 1 / (gOf p : ℝ) ^ i) := by
  obtain ⟨hN, hη⟩ := Formalism.L2.SG.Pf.gSplitX_holds X p
  have hT := Formalism.L2.SG.Pf.AlTieFD.T_not_mem X u p
  unfold aP
  rw [if_neg (by unfold Tw; exact hT), X.n_eq, ← Formalism.MainNotions.S.dimS_eq D.R, hη, hN, gAt_eq X p]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

theorem indexTypC_holds (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  intro p
  refine (ratio_eq X hb u p).trans ?_
  rw [idx_arith (gOf p) D.R.rS D.R.k (MassDataIdxSteps.gOf_prime X p), aP_typed X u p, gAt_eq X p]

end Formalism.L2.SG.Pf.AlTieIdx
