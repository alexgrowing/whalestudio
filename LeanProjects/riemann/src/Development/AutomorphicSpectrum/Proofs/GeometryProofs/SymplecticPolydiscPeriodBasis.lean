import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PInjective
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsSymplecticBasisLagrangianBetween
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SymplecticUnipotentShape
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelOfRiemann
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPuncturedExpOrder
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PLogCoverDescent

open Filter Topology Matrix Metric GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Flat
namespace Frame

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ]

theorem single_re (c k : Fin n) :
    ((Pi.single c (2 * Real.pi * Complex.I) : Fin n → ℂ) k).re = 0 := by
  by_cases h : k = c
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem shift_mem (h : a ≤ n) (i : Fin a) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · rw [Pi.add_apply, Complex.add_re, single_re, add_zero]
    exact hw.1 j
  · have hne : k ≠ Fin.castLE h i := by
      intro e
      have : k.val = i.val := by rw [e]; rfl
      omega
    rw [Pi.add_apply, Pi.single_eq_of_ne hne, add_zero]
    exact hw.2 k hk

theorem expCover_shift (h : a ≤ n) (i : Fin a) (w : Fin n → ℂ) :
    expCover a (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = expCover a w := by
  funext k
  unfold expCover
  by_cases hk : k = Fin.castLE h i
  · have : k.val < a := by rw [hk]; exact i.2
    subst hk
    simp only [this, if_true, Pi.add_apply, Pi.single_eq_same]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  · simp [Pi.single_eq_of_ne hk]

theorem exists_seq (h : a ≤ n) : ∃ u : ℕ → Fin n → ℂ, (∀ m, u m ∈ logCover h) ∧
    Tendsto (fun m => expCover a (u m)) atTop (𝓝 0) := by
  refine ⟨fun m k => if k.val < a then -((m : ℂ) + 1) else (((m : ℂ) + 2))⁻¹, fun m => ⟨fun j => ?_, fun k hk => ?_⟩, ?_⟩
  · have : (Fin.castLE h j).val < a := j.2
    simp only [this, if_true, Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · have : ¬ k.val < a := by omega
    simp only [this, if_false, norm_inv]
    have h2 : ‖(m : ℂ) + 2‖ = (m : ℝ) + 2 := by
      have : (m : ℂ) + 2 = ((m + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]; push_cast; ring
    rw [h2]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact inv_lt_one_of_one_lt₀ (by linarith)
  · rw [tendsto_pi_nhds]
    intro k
    simp only [expCover, Pi.zero_apply]
    by_cases hk : k.val < a
    · simp only [hk, if_true]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [Complex.norm_exp, Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
      refine Real.tendsto_exp_atBot.comp ?_
      refine tendsto_neg_atTop_atBot.comp ?_
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    · simp only [hk, if_false]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h2 : ∀ m : ℕ, ‖((m : ℂ) + 2)⁻¹‖ = ((m : ℝ) + 2)⁻¹ := by
        intro m
        have : (m : ℂ) + 2 = ((m + 2 : ℕ) : ℂ) := by push_cast; ring
        rw [norm_inv, this, Complex.norm_natCast]; push_cast; ring
      simp only [h2]
      exact tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

theorem logCover_nonempty (h : a ≤ n) : (logCover h).Nonempty := by
  obtain ⟨u, hu, -⟩ := exists_seq h
  exact ⟨u 0, hu 0⟩

theorem T_fix (L : LogPeriods n a g Λ) (i : Fin a) (x : L.W) : L.T i x = x := by
  obtain ⟨w, hw⟩ := logCover_nonempty L.a_le
  apply GlobalTheory.CompanionTheory.Ar.Flat.LogPeriodsModel.P_injective L hw
  rw [← L.mono i w hw, ← L.s_eq x _ (shift_mem L.a_le i hw), expCover_shift, L.s_eq x w hw]

theorem T_fix_of_smul (L : LogPeriods n a g Λ) (i : Fin a) {c : Λ} {k : ℤ} (hk : k ≠ 0)
    (hc : k • c ∈ L.W) : L.T i c = c := by
  haveI := L.free
  have h := T_fix L i ⟨k • c, hc⟩
  simp only [map_zsmul] at h
  exact smul_right_injective Λ hk h

theorem T_isometry (L : LogPeriods n a g Λ) (i : Fin a) (x y : Λ) :
    L.E (L.T i x) (L.T i y) = L.E x y := by
  obtain ⟨w, hw⟩ := logCover_nonempty L.a_le
  have h1 := L.im w hw (L.T i x) (L.T i y)
  have h2 := L.im _ (shift_mem L.a_le i hw) x y
  rw [expCover_shift, L.mono i w hw, L.mono i w hw, h1] at h2
  exact_mod_cast h2

theorem exists_basis (L : LogPeriods n a g Λ) :
    ∃ (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ),
      (∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧
        L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0) ∧
      (∀ i, ∃ k : ℤ, k ≠ 0 ∧ k • bas (.inl i) ∈ L.W) ∧
      (∀ i k, L.T i (bas (.inl k)) = bas (.inl k)) ∧ (∀ i, (B i)ᵀ = B i) ∧
      ∀ i j, L.T i (bas (.inr j)) = bas (.inr j) + ∑ k, B i j k • bas (.inl k) := by
  haveI := L.free
  haveI := L.fin
  obtain ⟨b0, hb0, hW, -⟩ := exists_symplecticBasis_lagrangian_between g Λ L.E L.alt L.unimod
    L.rank L.W L.coiso
  let u : Fin g ⊕ Fin g → ℤ := Sum.elim (fun _ => 1) (fun _ => -1)
  have hu : ∀ i, IsUnit (u i) := by rintro (i | i) <;> simp [u]
  let bas := b0.isUnitSMul hu
  have hl : ∀ i, bas (.inl i) = b0 (.inl i) := by
    intro i; simp [bas, u, Module.Basis.isUnitSMul_apply]
  have hr : ∀ i, bas (.inr i) = - b0 (.inr i) := by
    intro i; simp [bas, u, Module.Basis.isUnitSMul_apply]
  have hsym : ∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧
      L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧
      L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0 := by
    intro i j
    obtain ⟨h1, h2, h3⟩ := hb0 i j
    refine ⟨by rw [hl, hl, h1], by rw [hr, hr]; simp [h2], ?_⟩
    rw [hl, hr, map_neg, h3]
    split_ifs <;> simp
  have hfix : ∀ i k, L.T i (bas (.inl k)) = bas (.inl k) := by
    intro i k
    obtain ⟨m, hm, hx⟩ := hW k
    rw [hl]
    exact T_fix_of_smul L i hm hx
  have hshape := fun i => symplectic_unipotent_shape g Λ (-L.E) bas
    (fun x => by simp [L.alt x])
    (fun p q => by
      obtain ⟨h1, h2, h3⟩ := hsym p q
      refine ⟨by simp [h1], by simp [h2], ?_⟩
      simp only [LinearMap.neg_apply, h3]
      split_ifs <;> simp)
    (L.T i) (fun x y => by simp [T_isometry L i x y]) (hfix i)
  choose B hBs hBt using hshape
  exact ⟨bas, B, hsym, fun i => by rw [hl]; exact hW i, hfix, hBs, hBt⟩

theorem exists_frame (L : LogPeriods n a g Λ) (c : Fin g → Λ)
    (hc : ∀ i, ∃ k : ℤ, k ≠ 0 ∧ k • c i ∈ L.W) :
    ∃ A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ,
      (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (ball 0 1)) ∧
      ∀ w ∈ logCover L.a_le, ∀ i k, L.P w (c i) k = A (expCover a w) i k := by
  choose m hm hx using hc
  refine ⟨fun z => Matrix.of fun i => ((m i : ℂ))⁻¹ • L.s ⟨m i • c i, hx i⟩ z,
    fun i j => ?_, fun w hw i k => ?_⟩
  · have := (differentiableOn_pi.1 (L.s_hol ⟨_, hx i⟩)) j
    simpa using this.const_mul ((m i : ℂ)⁻¹)
  · have hmne : (m i : ℂ) ≠ 0 := by exact_mod_cast hm i
    simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, L.s_eq _ w hw]
    rw [map_zsmul, Pi.smul_apply, zsmul_eq_mul, inv_mul_cancel_left₀ hmne]

theorem exists_period (L : LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (hsym : ∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧
      L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0)
    (hTa : ∀ i k, L.T i (bas (.inl k)) = bas (.inl k)) (hBs : ∀ i, (B i)ᵀ = B i)
    (hTb : ∀ i j, L.T i (bas (.inr j)) = bas (.inr j) + ∑ k, B i j k • bas (.inl k)) :
    ∃ Q : PeriodPolydisc n a g, (∀ i, Q.B i = B i) ∧ ∀ w ∈ logCover L.a_le, ∀ j,
      L.P w (bas (.inr j)) = ∑ k, Q.τ w j k • L.P w (bas (.inl k)) := by
  let Am : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun w => Matrix.of fun i => L.P w (bas (.inl i))
  let Bm : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun w => Matrix.of fun i => L.P w (bas (.inr i))
  have hS : ∀ w ∈ logCover L.a_le, (Am w).det ≠ 0 ∧ (Bm w * (Am w)⁻¹)ᵀ = Bm w * (Am w)⁻¹ ∧
      ((Bm w * (Am w)⁻¹).map Complex.im).PosDef := by
    intro w hw
    obtain ⟨h1, h2, h3, -⟩ := siegel_of_riemann g (Am w) (Bm w) (L.H (expCover a w)) (L.herm w hw)
      (L.pos w hw) (fun i j => ⟨(L.im w hw (bas (.inl i)) (bas (.inl j))).trans (by simp [(hsym i j).1]),
        (L.im w hw (bas (.inr i)) (bas (.inr j))).trans (by simp [(hsym i j).2.1]),
        (L.im w hw (bas (.inl i)) (bas (.inr j))).trans (by
          rw [(hsym i j).2.2]; split_ifs <;> simp)⟩)
    exact ⟨h1, h2, h3⟩
  have hU : ∀ w ∈ logCover L.a_le, IsUnit (Am w).det := fun w hw => isUnit_iff_ne_zero.2 (hS w hw).1
  have hAm : ∀ i j, DifferentiableOn ℂ (fun w => Am w i j) (logCover L.a_le) :=
    fun i j => (differentiableOn_pi.1 (L.hol (bas (.inl i)))) j
  have hBm : ∀ i j, DifferentiableOn ℂ (fun w => Bm w i j) (logCover L.a_le) :=
    fun i j => (differentiableOn_pi.1 (L.hol (bas (.inr i)))) j
  refine ⟨{ a_le := L.a_le
            τ := fun w => Bm w * (Am w)⁻¹
            analytic := fun p q => ReciprocityTheory.AnForm.Osgood.osgood n _ _ (isOpen_logCover L.a_le)
              (GlobalTheory.differentiableOn_matrix_mul_apply hBm
                (GlobalTheory.differentiableOn_nonsing_inv_apply hAm hU) p q)
            symm := fun w hw => (hS w hw).2.1
            im_posDef := fun w hw => (hS w hw).2.2
            B := B
            B_symm := hBs
            periodic := fun i w hw => ?_ }, fun _ => rfl, fun w hw j => ?_⟩
  · have h1 : Am (w + Pi.single (Fin.castLE L.a_le i) (2 * Real.pi * Complex.I)) = Am w := by
      ext p q
      simp only [Am, Matrix.of_apply, L.mono i w hw, hTa]
    have h2 : Bm (w + Pi.single (Fin.castLE L.a_le i) (2 * Real.pi * Complex.I)) =
        Bm w + (B i).map (Int.cast : ℤ → ℂ) * Am w := by
      ext p q
      simp [Am, Bm, L.mono i w hw, hTb, Matrix.mul_apply, Finset.sum_apply]
    show Bm _ * (Am _)⁻¹ = Bm w * (Am w)⁻¹ + _
    rw [h1, h2, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU w hw), Matrix.mul_one]
  · have h1 : Bm w = (Bm w * (Am w)⁻¹) * Am w := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hU w hw), Matrix.mul_one]
    funext k
    have h2 := congrFun (congrFun h1 j) k
    rw [Matrix.mul_apply] at h2
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact h2

theorem det_frame_ne_zero (L : LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ)
    (Q : PeriodPolydisc n a g) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) (ball 0 1)) (hT0 : Q.IsTau0Ext T0)
    (hTa : ∀ i k, L.T i (bas (.inl k)) = bas (.inl k))
    (hTb : ∀ i j, L.T i (bas (.inr j)) = bas (.inr j) + ∑ k, Q.B i j k • bas (.inl k))
    (hAP : ∀ w ∈ logCover L.a_le, ∀ i k, L.P w (bas (.inl i)) k = A (expCover a w) i k)
    (hQP : ∀ w ∈ logCover L.a_le, ∀ j,
      L.P w (bas (.inr j)) = ∑ k, Q.τ w j k • L.P w (bas (.inl k))) :
    (A 0).det ≠ 0 := by
  obtain ⟨u, hu, hlim⟩ := exists_seq L.a_le
  have h0 : (0 : Fin n → ℂ) ∈ ball (0 : Fin n → ℂ) 1 := mem_ball_self one_pos
  have hAc : ∀ i j, ContinuousAt (fun z => A z i j) 0 := fun i j =>
    (hA i j).continuousOn.continuousAt (ball_mem_nhds 0 one_pos)
  have hTc : ∀ i j, ContinuousAt (fun z => T0 z i j) 0 := fun i j =>
    (hT0.1 i j 0 h0).continuousAt
  have key : ∀ x : L.W, ∃ c : Fin g → ℂ, L.s x 0 = c ᵥ* A 0 := by
    intro x
    set cu : Fin g → ℤ := fun i => bas.repr x (.inl i) with hcu
    set cv : Fin g → ℤ := fun j => bas.repr x (.inr j) with hcv
    have hx : (x : Λ) = ∑ i, cu i • bas (.inl i) + ∑ j, cv j • bas (.inr j) := by
      conv_lhs => rw [← bas.sum_repr (x : Λ)]
      rw [Fintype.sum_sum_type]
    have hBv : ∀ i k, ∑ j, cv j * Q.B i j k = 0 := by
      intro i k
      have h := T_fix L i x
      rw [hx] at h
      simp only [map_add, map_sum, map_zsmul, hTa, hTb, smul_add, Finset.sum_add_distrib] at h
      have h' : ∑ j, cv j • ∑ l, Q.B i j l • bas (.inl l) = 0 := by
        exact add_eq_left.1 (add_left_cancel h)
      have h2 := congrArg (bas.coord (.inl k)) h'
      simpa [Finsupp.single_apply, Module.Basis.coord_apply] using h2
    have hpt : ∀ w ∈ logCover L.a_le, ∀ m, L.s x (expCover a w) m =
        ∑ k, ((cu k : ℂ) + ∑ j, (cv j : ℂ) * T0 (expCover a w) j k) * A (expCover a w) k m := by
      intro w hw m
      have e2 : ∀ k, ∑ j, (cv j : ℂ) * T0 (expCover a w) j k = ∑ j, (cv j : ℂ) * Q.τ w j k := by
        intro k
        have hj : ∀ j, T0 (expCover a w) j k = Q.τ w j k -
            ∑ i : Fin a, (w (Fin.castLE Q.a_le i) / (2 * Real.pi * Complex.I)) * (Q.B i j k : ℂ) := by
          intro j
          rw [← hT0.2 w hw]
          simp [PeriodPolydisc.tau0, Matrix.sub_apply, Matrix.sum_apply]
        simp only [hj, mul_sub, Finset.sum_sub_distrib]
        rw [sub_eq_self]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun i _ => ?_
        have h3 : (∑ j, (cv j : ℂ) * (Q.B i j k : ℂ)) = 0 := by exact_mod_cast hBv i k
        calc _ = (w (Fin.castLE Q.a_le i) / (2 * Real.pi * Complex.I)) *
              ∑ j, (cv j : ℂ) * (Q.B i j k : ℂ) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
          _ = 0 := by rw [h3, mul_zero]
      have e1 : L.P w (x : Λ) = ∑ i, cu i • L.P w (bas (.inl i)) +
          ∑ j, cv j • ∑ k, Q.τ w j k • L.P w (bas (.inl k)) := by
        conv_lhs => rw [hx]
        simp only [map_add, map_sum, map_zsmul, hQP w hw]
      rw [L.s_eq x w hw, e1]
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, hAP w hw,
        Pi.mul_apply, Pi.intCast_apply, add_mul, Finset.sum_add_distrib, e2, Finset.sum_mul,
        Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    refine ⟨fun k => (cu k : ℂ) + ∑ j, (cv j : ℂ) * T0 0 j k, ?_⟩
    funext m
    have hF : ContinuousAt (fun z => ∑ k, ((cu k : ℂ) + ∑ j, (cv j : ℂ) * T0 z j k) * A z k m) 0 :=
      tendsto_finset_sum _ fun k _ => ContinuousAt.mul
        (continuousAt_const.add (tendsto_finset_sum _ fun j _ => continuousAt_const.mul (hTc j k)))
        (hAc k m)
    have hs : ContinuousAt (fun z => L.s x z m) 0 :=
      (differentiableOn_pi.1 (L.s_hol x) m).continuousOn.continuousAt (ball_mem_nhds 0 one_pos)
    have t1 := hs.tendsto.comp hlim
    have t2 := hF.tendsto.comp hlim
    have h := tendsto_nhds_unique t1 (t2.congr fun t => (hpt (u t) (hu t) m).symm)
    simpa [vecMul, dotProduct] using h
  have hspan : Submodule.span ℂ (Set.range fun x => L.s x 0) ≤ LinearMap.range (A 0).vecMulLinear := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := key x
    exact ⟨c, hc.symm⟩
  rw [L.span] at hspan
  have hsurj : Function.Surjective fun v : Fin g → ℂ => v ᵥ* A 0 := by
    intro y
    obtain ⟨c, hc⟩ := hspan (Submodule.mem_top (x := y))
    exact ⟨c, hc⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.vecMul_surjective_iff_isUnit.1 hsurj)).ne_zero

end Frame

theorem exists_markedPeriods_frame : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : GlobalTheory.CompanionTheory.Ar.Flat.LogPeriods n a g Λ), ∃ (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (Q : GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc n a g) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧ L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0) ∧ (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (Metric.ball 0 1)) ∧ (A 0).det ≠ 0 ∧ Q.IsTau0Ext T0 ∧ (∀ i, ((Q.B i).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ i k, L.P w (bas (.inl i)) k = A (GroundTheory.Heights₂.Heights.Regular.expCover a w) i k) ∧ ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ j, L.P w (bas (.inr j)) = ∑ k, Q.τ w j k • L.P w (bas (.inl k)) := by
  intro n a g Λ _ L
  obtain ⟨bas, B, hsym, hW, hTa, hBs, hTb⟩ := Frame.exists_basis L
  obtain ⟨A, hAd, hAP⟩ := Frame.exists_frame L (fun i => bas (.inl i)) hW
  obtain ⟨Q, hQB, hQP⟩ := Frame.exists_period L bas B hsym hTa hBs hTb
  obtain ⟨hpos, T0, hT0⟩ := Tau0Holomorphic.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof
    LogCoverDescent.proof n a g Q
  refine ⟨bas, Q, A, T0, hsym, hAd, ?_, hT0, hpos, hAP, hQP⟩
  exact Frame.det_frame_ne_zero L bas Q A T0 hAd hT0 hTa
    (fun i j => by simp only [hQB]; exact hTb i j) hAP hQP

end GlobalTheory.CompanionTheory.Ar.Flat
