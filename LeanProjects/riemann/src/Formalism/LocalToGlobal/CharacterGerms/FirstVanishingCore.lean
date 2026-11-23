import Formalism.LocalToGlobal.CharacterGerms.CoeffLMulCvFrob
import Formalism.LocalToGlobal.CharacterGerms.FirstVanishingAt

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LogarithmSeriesLinearTerm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem lg0 (Y : FBChart C V O dd) (j : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg j)) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) (Y.lg j) = 0
  rw [Finsupp.mapDomain_zero, Y.lg_lin j 0 (by simp), MvPowerSeries.coeff_zero_X]

theorem exlg (Y : FBChart C V O dd) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex i)) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  rw [uncurry_comp Y.lg_const, Y.ex_lg]
  exact uncurry_X i

theorem ex_lg_at' (Y : FBChart C V O dd) {τ : Type} (A : Fin dd → MvPowerSeries τ C)
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst A (un1 (Y.lg j))) (un1 (Y.ex i)) = A i := by
  have hA' := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
  have hL : MvPowerSeries.HasSubst (fun j => un1 (Y.lg j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (lg0 Y)
  rw [← MvPowerSeries.subst_comp_subst_apply hL hA', exlg Y, MvPowerSeries.subst_X hA']

theorem lin (Y : FBChart C V O dd) (i : Fin dd) (μ : Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ (un1 (Y.lg i)) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  have hinj : Function.Injective (fun x : Fin dd => ((0 : Fin 1), x)) := fun a b h => (Prod.mk.inj h).2
  show MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) μ) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hμ), MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
  congr 1
  apply propext
  rw [← Finsupp.mapDomain_single, (Finsupp.mapDomain_injective hinj).eq_iff]

theorem coeff1_of_lgLin (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) {U : Fin dd → C}
    (hL : Y.LgLin γ U) (i : Fin dd) : PowerSeries.coeff 1 (γ i) = U i := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hlin : Agr 2 (un1 (Y.lg i)) (MvPowerSeries.X i) := fun e he => lin Y i e (by omega)
  have h2 := agr_subst_right (a := γ) hγ0 hlin
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0)] at h2
  have h3 := (hL i).mono (show 2 ≤ V.l ^ 2 by nlinarith)
  have h4 := (h2.symm.trans h3) (Finsupp.single () 1) (by rw [Finsupp.degree_single]; omega)
  change PowerSeries.coeff 1 (γ i) = PowerSeries.coeff 1 _ at h4
  rw [h4, map_smul, coeffX', if_pos rfl, smul_eq_mul, mul_one]

theorem lg_mulCv' (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C}
    (hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0) (n : ℕ) (j : Fin dd) :
    MvPowerSeries.subst (fun k => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F n k))
        (un1 (Y.lg j)) = (n : C) • alongCv γ (un1 (Y.lg j)) := by
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hM : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => mulL Y.B.G.F n q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G n q.2
  have hL0 : ∀ k, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F n k)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_subst_eq_zero hG (fun q => hγ0 q.2) (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G n k)
  have h := congrArg (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2)) (MulLFrob.lg_mulL Y n j)
  rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply hM hG,
    show (n • Y.lg j) = (n : C) • Y.lg j from (Nat.cast_smul_eq_nsmul C n _).symm,
    MvPowerSeries.subst_smul hG] at h
  show _ = (n : C) • MvPowerSeries.subst γ (un1 (Y.lg j))
  rw [subst_singlePointUncurry hL0, subst_singlePointUncurry hγ0]
  exact h

theorem coeff_l_mulCv_core (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) {U : Fin dd → C}
    (hL : Y.LgLin γ U) (k : Fin dd) :
    V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k))) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hL0 : ∀ k, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_subst_eq_zero hG (fun q => hγ0 q.2) (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l k)
  have hX0 : ∀ (a : C), MvPowerSeries.constantCoeff (a • (MvPowerSeries.X () : PowerSeries C)) = 0 := by
    intro a
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hcl : ∀ j, MvPowerSeries.constantCoeff (alongCv γ (un1 (Y.lg j))) = 0 := fun j =>
    MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0) hγ0 (lg0 Y j)
  have eL := ex_lg_at' Y _ hL0 k
  simp only [lg_mulCv' Y hγ0 V.l] at eL
  have hAL : Agr (V.l ^ 2) (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k))
      (MvPowerSeries.subst (fun j => ((V.l : C) * U j) • (MvPowerSeries.X () : PowerSeries C)) (un1 (Y.ex k))) := by
    rw [← eL]
    refine agr_subst_left (fun j => by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hcl j, mul_zero])
      (fun j => hX0 _) (fun j => ?_) _
    have := FirstVanishing.Agr.smul (hL j) (V.l : C)
    rwa [smul_smul] at this
  have eG := ex_lg_at' Y γ hγ0 k
  have hAG : Agr (V.l ^ 2) (γ k)
      (MvPowerSeries.subst (fun j => U j • (MvPowerSeries.X () : PowerSeries C)) (un1 (Y.ex k))) := by
    rw [← eG]
    exact agr_subst_left hcl (fun j => hX0 _) (fun j => hL j) _
  have hdeg : (Finsupp.single () V.l).degree < V.l ^ 2 := by
    rw [Finsupp.degree_single]
    nlinarith
  have e1 := hAL _ hdeg
  have e2 := hAG _ hdeg
  change PowerSeries.coeff V.l _ = PowerSeries.coeff V.l _ at e1 e2
  rw [e1, FirstVanishing.coeff_subst_scale, ← e2]
  obtain ⟨m, hm⟩ : ∃ m, V.l = m + 1 := ⟨V.l - 1, by omega⟩
  have e3 : (V.l : C) ^ V.l = (V.l : C) * (V.l : C) ^ m := by
    rw [← pow_succ', ← hm]
  rw [e3, mul_assoc]
  exact mm_l_mul ((VF.Ge.pow (ge_natCast V.l) m).mul_int ((hγ k).2 V.l))

end LogarithmSeriesLinearTerm

theorem first_vanishing_core : FirstVanishingCore := by
  intro C _ _ V O _ _ dd Y γ U hγ hL k
  have hB := LogarithmSeriesLinearTerm.coeff_l_mulCv_core Y hγ hL k
  have hA := FirstVanishing.coeff_l_mulCv_frob Y hγ k
  simp only [LogarithmSeriesLinearTerm.coeff1_of_lgLin Y hγ hL] at hA
  have h := MaximalIdealCongruence.mm_sub hB hA
  rwa [sub_sub_cancel] at h

end Formalism.L2.FormalSeriesBounds
