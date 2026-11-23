import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementN
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInVarEqZero
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.E

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq)
open Formalism.L2.Th1.C (IntMv IntPS IsPt IsLogPair)
open CompatibleChartOperations

namespace GeneratorMatrix

def blk (n : Type) (a : Fin 4) : n ↪ Fin 4 × n := ⟨fun i => (a, i), fun _ _ h => (Prod.mk.inj h).2⟩

theorem blk_apply {n : Type} (a b : Fin 4) (μ : n →₀ ℕ) (i : n) :
    Finsupp.embDomain (blk n a) μ (b, i) = if a = b then μ i else 0 := by
  split_ifs with h
  · subst h
    exact Finsupp.embDomain_apply_self (blk n a) μ i
  · refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
    rintro ⟨j, hj⟩
    exact h (Prod.mk.inj hj).1

section Field

variable {K : Type} [Field K] {n : Type}

theorem tensor4_eq_rename (f : MvPowerSeries n K) :
    tensor4 f = ∏ a, MvPowerSeries.rename (blk n a) f := by
  unfold tensor4
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem tensor4_mul (f g : MvPowerSeries n K) : tensor4 (f * g) = tensor4 f * tensor4 g := by
  rw [tensor4_eq_rename, tensor4_eq_rename, tensor4_eq_rename, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => map_mul _ _ _

theorem coeff_tensor4 (f : MvPowerSeries n K) (ν : n →₀ ℕ) :
    MvPowerSeries.coeff (∑ a, Finsupp.embDomain (blk n a) ν) (tensor4 f) =
      MvPowerSeries.coeff ν f ^ 4 := by
  classical
  rw [tensor4_eq_rename, MvPowerSeries.coeff_prod]
  rw [Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm fun a => Finsupp.embDomain (blk n a) ν)]
  · simp
  · intro L hL hne
    by_contra h0
    apply hne
    rw [Finset.mem_finsuppAntidiag] at hL
    have hr : ∀ a, ∃ μ : n →₀ ℕ, L a = Finsupp.embDomain (blk n a) μ := by
      intro a
      by_contra hc
      apply h0
      refine Finset.prod_eq_zero (Finset.mem_univ a) (MvPowerSeries.coeff_rename_eq_zero _ _ ?_)
      rintro ⟨μ, hμ⟩
      exact hc ⟨μ, by rw [Finsupp.embDomain_eq_mapDomain, hμ]⟩
    choose μ hμ using hr
    have hμν : ∀ b, μ b = ν := by
      intro b
      ext i
      have := DFunLike.congr_fun hL.1 (b, i)
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, hμ, blk_apply, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      exact this
    ext1 a
    rw [hμ, hμν]
    rfl
  · intro h
    exact absurd (by simp [Finset.mem_finsuppAntidiag]) h

end Field

section Lin

variable {K : Type} [Field K] {O m : Type} [CommRing O] [Fintype m] {l linv : PowerSeries K}

theorem cc_matCoord (h : IsLogPair l linv) (τ : O →+* K) (γ : Matrix m m O) (w : m) :
    MvPowerSeries.constantCoeff (matCoord l linv τ γ w) = 0 :=
  Formalism.L2.Th1.C.Pts.constantCoeff_flin h _ fun _ => MvPowerSeries.constantCoeff_X _

theorem matCoord_comp (h : IsLogPair l linv) (τ : O →+* K) (γ δ : Matrix m m O) (w : m) :
    MvPowerSeries.subst (matCoord l linv τ δ) (matCoord l linv τ γ w) =
      matCoord l linv τ (γ * δ) w := by
  have hδ0 := cc_matCoord h τ δ
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hδ0
  have hL : ∀ j, PowerSeries.subst (matCoord l linv τ δ j) l =
      ∑ k, MvPowerSeries.C (τ (δ j k)) *
        PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries m K) l := fun j =>
    Formalism.L2.Th1.C.Pts.l_flin h _ fun _ => MvPowerSeries.constantCoeff_X _
  conv_lhs => rw [matCoord, Formalism.L2.Th1.C.flin]
  rw [Formalism.L2.Th1.C.Pts.substMv_subst
    (Formalism.L2.Th1.C.Pts.constantCoeff_sum_l h _ fun _ => MvPowerSeries.constantCoeff_X _) hδ0]
  conv_rhs => rw [matCoord, Formalism.L2.Th1.C.flin]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
  have h1 : ∀ j, MvPowerSeries.substAlgHom hs (MvPowerSeries.C (τ (γ w j)) *
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m K) l) =
      ∑ k, MvPowerSeries.C (τ (γ w j * δ j k)) *
        PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries m K) l := by
    intro j
    rw [map_mul, MvPowerSeries.coe_substAlgHom hs, MvPowerSeries.subst_C,
      Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X j) hδ0,
      MvPowerSeries.subst_X hs, hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, mul_assoc]
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply, map_sum, map_sum, Finset.sum_mul]

theorem matCoord_one [DecidableEq m] (h : IsLogPair l linv) (τ : O →+* K) (w : m) :
    matCoord l linv τ (1 : Matrix m m O) w = MvPowerSeries.X w := by
  rw [matCoord, Formalism.L2.Th1.C.flin, Finset.sum_eq_single w]
  · rw [Matrix.one_apply_eq, map_one, map_one, one_mul]
    exact Formalism.L2.Th1.C.Pts.subst_linv_l h (MvPowerSeries.constantCoeff_X w)
  · intro j _ hj
    rw [Matrix.one_apply_ne hj.symm, map_zero, map_zero, zero_mul]
  · intro hw
    exact absurd (Finset.mem_univ w) hw

end Lin

section Exp

variable {K : Type} [NormedField K] [CharZero K] {n : Type} [Fintype n]

theorem tensor4_exp {ph : PowerSeries K} (hph : PowerSeries.constantCoeff ph = 0) :
    tensor4 (mvExp (phSum ph : MvPowerSeries n K)) =
      mvExp (phSum ph : MvPowerSeries (Fin 4 × n) K) := by
  have h1 : ∀ a : Fin 4, MvPowerSeries.subst
      (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K))
      (mvExp (phSum ph : MvPowerSeries n K)) = mvExp (∑ i, at1 (a, i) ph) := by
    intro a
    have h0 : ∀ i : n, MvPowerSeries.constantCoeff
        (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K) = 0 :=
      fun i => MvPowerSeries.constantCoeff_X _
    have h2 : MvPowerSeries.subst (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K))
        (phSum ph : MvPowerSeries n K) = ∑ i, at1 (a, i) ph := subst_phSum ph h0
    rw [← h2]
    exact Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp (cc_phSum hph) h0
  unfold tensor4
  rw [Finset.prod_congr rfl fun a _ => h1 a]
  have h3 : (phSum ph : MvPowerSeries (Fin 4 × n) K) = ∑ a : Fin 4, ∑ i : n, at1 (a, i) ph := by
    unfold phSum
    exact Fintype.sum_prod_type _
  rw [h3]
  refine (Formalism.L2.Th1.C.mvExp_sum _ _ fun a _ => ?_).symm
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => constantCoeff_inVar_eq_zero _ hph

end Exp

end GeneratorMatrix

open GeneratorMatrix

theorem fourth_power : FourthPower := by
  intro K _ _ n f h ν
  have h1 := h (∑ a, Finsupp.embDomain (blk n a) ν)
  rw [coeff_tensor4, norm_pow] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1

theorem GeneralIntOf_of (hF : FourthPower) (hU : Formalism.L2.Th1.C.UnitaryInv) (hP : ProdInt)
    (hS : SubstExpInt) (hC : CongIffSimeq) : GeneralIntOf := by
  intro K _ _ _ R hR l linv ph hFr O _ _ τ hEnd hBin hF1 hN hA n _ _ Θ γ hγ hK
  obtain ⟨κ, _, r, V, hr, hV, hEq⟩ := hK
  obtain ⟨hlp, hFG, hph⟩ := hFr
  have hγδ : γ * γ.conjTranspose = 1 := mul_eq_one_comm.1 hγ
  have hδ : γ.conjTranspose.conjTranspose * γ.conjTranspose = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hγδ
  have hpt : ∀ w, IsPt R (matCoord l linv τ γ.conjTranspose w) := fun w =>
    Formalism.L2.Th1.C.Pts.isPt_flin hlp hFG (fun _ => hEnd _) fun _ => isPt_X _
  obtain ⟨h1, h2⟩ := hP K κ (Fin 4 × n) ph r V hph hr hV
  obtain ⟨h3, h4, h5⟩ := hS K (Fin 4 × n) (Fin 4 × n) (matCoord l linv τ γ.conjTranspose)
    (fun i => (hpt i).1) (fun i => (integral_iff hR _).2 (hpt i).2) (phSum ph) (thetaProd r V)
    (cc_phSum hph) h2
  have hT : tensor4 Θ =
      mvExp (-(MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose) (phSum ph))) *
        MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose) (thetaProd r V) := by
    rw [← h3, ← h1, ← hEq, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_matCoord hlp τ γ))
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_matCoord hlp τ γ.conjTranspose))]
    have hX : (fun w => MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose)
        (matCoord l linv τ γ w)) = MvPowerSeries.X := by
      funext w
      rw [matCoord_comp hlp, hγδ, matCoord_one hlp]
    rw [hX, MvPowerSeries.subst_self]
    rfl
  have hcong : Formalism.L2.Th1.C.Cong R (phSum ph : MvPowerSeries (Fin 4 × n) K)
      (MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose) (phSum ph)) := by
    rw [subst_phSum ph fun i => (hpt i).1]
    exact Formalism.L2.Th1.C.Calc.cong_symm (hU K R l linv ph ⟨hlp, hFG, hph⟩ O τ hEnd hBin hF1 hN hA
      (Fin 4 × n) γ.conjTranspose hδ (Fin 4 × n) MvPowerSeries.X fun _ => isPt_X _)
  have hsim := ((hC K R hR _ _ _).1 hcong).2
  apply hF
  rw [tensor4_mul, tensor4_exp hph, hT, ← mul_assoc]
  have hadd : mvExp (phSum ph : MvPowerSeries (Fin 4 × n) K) *
      mvExp (-(MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose) (phSum ph))) =
      mvExp ((phSum ph : MvPowerSeries (Fin 4 × n) K) -
        MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose) (phSum ph)) :=
    (Formalism.L2.Th1.C.mvExp_sub (cc_phSum hph) h5).symm
  rw [hadd]
  exact (integral_iff hR _).2 (Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_mul ((integral_iff hR _).1 hsim)
    ((integral_iff hR _).1 h4))

theorem general_integrality : GeneralIntOf :=
  GeneralIntOf_of fourth_power Formalism.L2.Th1.C.unitaryInv product_integral subst_exp_integral
    congruence_iff_simeq

end Formalism.L2.Th1.E
