import Formalism.LocalToGlobal.InertKernelTheory.FirstKernelGeneratorOfOrthogonal
import Formalism.GL3MeanSquares.HookFormulaTorsion.ExpSeries
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne

noncomputable section

namespace Formalism.L2.KerInert.K1

open Formalism.MainNotions.FormalGroupSystem

section Char

variable (p : ℕ) [Fact p.Prime]

theorem charZero_WW : CharZero (WW p) := by
  obtain ⟨q, hq⟩ := CharP.exists (WW p)
  rcases CharP.char_is_prime_or_zero (WW p) q with h | h
  · exfalso
    have h0 : ((q : ℕ) : WW p) = 0 := CharP.cast_eq_zero (WW p) q
    have h1 : ((q : ℕ) : kb p) = 0 := by
      have := congrArg (WittVector.constantCoeff (p := p) (R := kb p)) h0
      rw [map_natCast, map_zero] at this
      exact this
    have h2 : p ∣ q := (CharP.cast_eq_zero_iff (kb p) p q).mp h1
    have h3 : p = q := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) h).mp h2
    have h4 : ((p : ℕ) : WW p) = ((q : ℕ) : WW p) := congrArg (Nat.cast) h3
    exact WittVector.p_nonzero p (kb p) (h4.trans h0)
  · subst h
    exact CharP.charP_to_charZero (WW p)

instance charZero_K0k1 : CharZero (K0 p) :=
  haveI := charZero_WW p
  charZero_of_injective_algebraMap (IsFractionRing.injective (WW p) (K0 p))

end Char

variable {p : ℕ} [Fact p.Prime]

theorem expS_eq {σ : Type} (f : MvPowerSeries σ (K0 p)) (hf : MvPowerSeries.constantCoeff f = 0) :
    expS p f = Formalism.HermitianLattices.ExpSeriesBivariate.expS f := by
  ext n
  rw [Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.coeff_expS f hf n (n.degree + 1) (Nat.lt_succ_self _)]
  show (∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k)) = _
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

theorem expS_add' {σ : Type} (f g : MvPowerSeries σ (K0 p)) (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : expS p (f + g) = expS p f * expS p g := by
  rw [expS_eq f hf, expS_eq g hg, expS_eq (f + g) (by rw [map_add, hf, hg, add_zero])]
  exact Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.expS_add f g hf hg

theorem expS_zero' {σ : Type} : expS p (0 : MvPowerSeries σ (K0 p)) = 1 := by
  rw [expS_eq 0 (map_zero _)]
  exact Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.expS_zero

theorem expS_neg_mul {σ : Type} (f : MvPowerSeries σ (K0 p)) (hf : MvPowerSeries.constantCoeff f = 0) :
    expS p (-f) * expS p f = 1 := by
  rw [← expS_add' (-f) f (by rw [map_neg, hf, neg_zero]) hf, neg_add_cancel, expS_zero']

theorem cc_log : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logF, PowerSeries.coeff_mk]

theorem cc_logX {ι : Type} (i : ι) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι (K0 p)) (logF p)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ cc_log

theorem hasSubst_log {ι : Type} [Finite ι] :
    MvPowerSeries.HasSubst (fun i : ι => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι (K0 p)) (logF p)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero cc_logX

theorem inParam_zero {ι : Type} [Finite ι] : inParam p (0 : MvPowerSeries ι (K0 p)) = 0 := by
  unfold inParam
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_log (p := p))]
  exact map_zero _

theorem simeq_refl' {ι : Type} [Finite ι] (f : MvPowerSeries ι (K0 p)) : Simeq p f f := by
  refine ⟨by rw [sub_self, map_zero], 0, map_zero _, ?_⟩
  rw [sub_self, inParam_zero, expS_zero', map_zero, add_zero]

theorem cc_be {be : MvPowerSeries (Fin 2) (K0 p)} (hB : BeProp p be) : MvPowerSeries.constantCoeff be = 0 := by
  by_contra h
  have := hB.ab 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
  simp at this

theorem constantCoeff_sub2_eq_zero {τ : Type} {be : MvPowerSeries (Fin 2) (K0 p)} (h0 : MvPowerSeries.constantCoeff be = 0)
    (x y : MvPowerSeries τ (K0 p)) (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (sub2 p be x y) = 0 := by
  have ha : ∀ i, MvPowerSeries.constantCoeff ((![x, y] : Fin 2 → MvPowerSeries τ (K0 p)) i) = 0 := by
    intro i; fin_cases i <;> simp [hx, hy]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha h0

theorem cc_sumBe {ι : Type} [Fintype ι] {be : MvPowerSeries (Fin 2) (K0 p)} (h0 : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.constantCoeff (sumBe p be : MvPowerSeries (ι ⊕ ι) (K0 p)) = 0 := by
  unfold sumBe
  rw [map_sum]
  exact Finset.sum_eq_zero fun e _ => constantCoeff_sub2_eq_zero h0 _ _ (by simp) (by simp)

theorem first_kernel_of_sum : FirstKernelGeneratorOfSum := by
  intro p _ ι _ K1 _ _ R1 be Th hB hE hI
  have h0 := cc_sumBe (ι := ι) (cc_be hB)
  refine ⟨sumBe p be, Th * MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (sumBe p be)), ?_, hI, hE, hB,
    simeq_refl' _⟩
  rw [mul_left_comm, ← map_mul, expS_neg_mul _ h0, map_one, mul_one]

end Formalism.L2.KerInert.K1

namespace Formalism.L2.KerInert.K1

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF cob UnrOK IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC)

section Gen

variable {σ τ K : Type} [CommRing K]

theorem subst_single_var {b : σ → MvPowerSeries τ K} (hb : MvPowerSeries.HasSubst b) (i : σ) (f : PowerSeries K) :
    MvPowerSeries.subst b (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K) f) =
      PowerSeries.subst (b i) f := by
  have hX : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ K)) :=
    PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply hX hb, MvPowerSeries.subst_X hb]
  rfl

theorem hasSubst_X_comp [Finite σ] (g : σ → τ) :
    MvPowerSeries.HasSubst (fun s => (MvPowerSeries.X (g s) : MvPowerSeries τ K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => MvPowerSeries.constantCoeff_X _

end Gen

variable {l : ℕ} [Fact l.Prime]

theorem map_logF : PowerSeries.map (k0ToC l) (logF l) = lgF ℂ_[l] l := by
  ext n
  rw [PowerSeries.coeff_map]
  simp only [logF, lgF, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_mul]
  split_ifs <;> simp

theorem inParamK_eq {ι : Type} (f : MvPowerSeries ι ℂ_[l]) :
    @inParamK l _ ι ℂ_[l] _ (wittFractionAlgebraCp l) f = MvPowerSeries.subst (fun i => at1 i (lgF ℂ_[l] l)) f := by
  unfold inParamK
  congr 1
  funext i
  rw [show @algebraMap (K0 l) ℂ_[l] _ _ (wittFractionAlgebraCp l) = k0ToC l from rfl, map_logF]
  rfl

section Main

variable {l : ℕ} [Fact l.Prime]

local notation "lgC" => lgF ℂ_[l] l

theorem mvExp_eq {σ : Type} (f : MvPowerSeries σ ℂ_[l]) : mvExp f = Formalism.HermitianLattices.ExpSeriesBivariate.expS f := rfl

theorem map_expS {σ : Type} (g : MvPowerSeries σ (K0 l)) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.map (k0ToC l) (expS l g) = mvExp (MvPowerSeries.map (k0ToC l) g) := by
  rw [expS_eq g hg, mvExp_eq]
  ext d
  rw [MvPowerSeries.coeff_map, Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.coeff_expS g hg d (d.degree + 1) (Nat.lt_succ_self _),
    Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.coeff_expS _ (by rw [MvPowerSeries.constantCoeff_map, hg, map_zero]) d (d.degree + 1)
      (Nat.lt_succ_self _), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← map_pow, MvPowerSeries.coeff_map]
  congr 1
  simp

theorem cc_inParam {σ : Type} [Finite σ] (g : MvPowerSeries σ (K0 l)) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (inParam l g) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero hasSubst_log cc_logX hg

theorem inParam_expS {σ : Type} [Finite σ] (g : MvPowerSeries σ (K0 l)) (hg : MvPowerSeries.constantCoeff g = 0) :
    inParam l (expS l g) = expS l (inParam l g) := by
  rw [expS_eq g hg, expS_eq _ (cc_inParam g hg)]
  exact Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.subst_expS _ cc_logX g hg

theorem map_inParam {σ : Type} [Finite σ] (g : MvPowerSeries σ (K0 l)) :
    MvPowerSeries.map (k0ToC l) (inParam l g) =
      MvPowerSeries.subst (fun i => at1 i lgC) (MvPowerSeries.map (k0ToC l) g) := by
  unfold inParam
  rw [MvPowerSeries.map_subst hasSubst_log]
  congr 1
  funext i
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)), map_logF,
    MvPowerSeries.map_X]
  rfl

theorem cc_lgC : PowerSeries.constantCoeff lgC = 0 := by
  rw [← map_logF, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_log, map_zero]

theorem constantCoeff_inVar_eq_zero {σ : Type} (i : σ) : MvPowerSeries.constantCoeff (at1 i lgC : MvPowerSeries σ ℂ_[l]) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ cc_lgC

theorem hasSubst_single_var_log {σ : Type} [Finite σ] :
    MvPowerSeries.HasSubst (fun i : σ => (at1 i lgC : MvPowerSeries σ ℂ_[l])) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero constantCoeff_inVar_eq_zero

theorem integral_X {σ : Type} (i : σ) : Integral (MvPowerSeries.X i : MvPowerSeries σ ℂ_[l]) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

abbrev E1 (ι : Type) : Type := ι × Fin 1 × Fin 1

def sideVariable {ι : Type} : Bool × E1 ι → MvPowerSeries (ι ⊕ ι) ℂ_[l] :=
  fun w => if w.1 then MvPowerSeries.X (Sum.inr w.2.1) else MvPowerSeries.X (Sum.inl w.2.1)

theorem cc_renS {ι : Type} (w : Bool × E1 ι) : MvPowerSeries.constantCoeff (sideVariable (l := l) w) = 0 := by
  unfold sideVariable; split_ifs <;> simp

theorem integral_renS {ι : Type} (w : Bool × E1 ι) : Integral (sideVariable (l := l) w) := by
  unfold sideVariable; split_ifs
  · exact integral_X _
  · exact integral_X _

theorem hasSubst_renS {ι : Type} [Finite ι] : MvPowerSeries.HasSubst (sideVariable (l := l) (ι := ι)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero cc_renS

theorem sum_extended_index {ι M : Type} [Fintype ι] [AddCommMonoid M] (g : E1 ι → M) :
    ∑ e : E1 ι, g e = ∑ e : ι, g (e, 0, 0) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_prod_type]
  simp

end Main

section Coord

variable {l : ℕ} [Fact l.Prime]

local notation "lgC" => lgF ℂ_[l] l

theorem lg_flin (hl : 2 ≤ l) {σ m : Type} [Fintype m] (c : m → ℂ_[l]) (v : m → MvPowerSeries σ ℂ_[l])
    (hv : ∀ k, MvPowerSeries.constantCoeff (v k) = 0) :
    PowerSeries.subst (Formalism.L2.Th1.C.flin lgC (expF ℂ_[l] l) c v) lgC =
      ∑ k, MvPowerSeries.C (c k) * PowerSeries.subst (v k) lgC := by
  unfold Formalism.L2.Th1.C.flin
  have hA : MvPowerSeries.constantCoeff (∑ k, MvPowerSeries.C (c k) * PowerSeries.subst (v k) lgC) = 0 := by
    simp only [map_sum, map_mul, MvPowerSeries.constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ cc_lgC, mul_zero]
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' (expSpec ℂ_[l] l hl).1)
    (PowerSeries.HasSubst.of_constantCoeff_zero hA), (expSpec ℂ_[l] l hl).2.1,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hA)]

theorem cc_flin (hl : 2 ≤ l) {σ m : Type} [Fintype m] (c : m → ℂ_[l]) (v : m → MvPowerSeries σ ℂ_[l])
    (hv : ∀ k, MvPowerSeries.constantCoeff (v k) = 0) :
    MvPowerSeries.constantCoeff (Formalism.L2.Th1.C.flin lgC (expF ℂ_[l] l) c v) = 0 := by
  unfold Formalism.L2.Th1.C.flin
  have hA : MvPowerSeries.constantCoeff (∑ k, MvPowerSeries.C (c k) * PowerSeries.subst (v k) lgC) = 0 := by
    simp only [map_sum, map_mul, MvPowerSeries.constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ cc_lgC, mul_zero]
  exact PowerSeries.constantCoeff_subst_eq_zero hA _ (expSpec ℂ_[l] l hl).1

variable {ι n : Type} [Fintype ι] [Fintype n]

def ext1 (f : ι → n → MaximalUnramifiedExtension l) : E1 ι → n → MaximalUnramifiedExtension l := fun e => f e.1

theorem cc_hypCoord (hl : 2 ≤ l) (f f' : ι → n → MaximalUnramifiedExtension l) (i : n) :
    MvPowerSeries.constantCoeff
      (Formalism.L2.Th1.E.hypCoord lgC (expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype (ext1 f) (ext1 f') i) = 0 := by
  unfold Formalism.L2.Th1.E.hypCoord
  exact cc_flin hl _ _ fun k => by cases k <;> simp

theorem cc_hypLin (f f' : ι → n → MaximalUnramifiedExtension l) (i : n) : MvPowerSeries.constantCoeff (hypLin l f f' i) = 0 := by
  unfold hypLin
  simp

theorem coord (hl : 2 ≤ l) (f f' : ι → n → MaximalUnramifiedExtension l) (i : n) :
    MvPowerSeries.subst (fun v => (at1 v lgC : MvPowerSeries (ι ⊕ ι) ℂ_[l])) (hypLin l f f' i) =
      MvPowerSeries.subst sideVariable
        (PowerSeries.subst (Formalism.L2.Th1.E.hypCoord lgC (expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype (ext1 f) (ext1 f') i) lgC) := by
  unfold Formalism.L2.Th1.E.hypCoord
  rw [lg_flin hl _ _ fun k => by cases k <;> simp]
  unfold hypLin
  rw [← MvPowerSeries.coe_substAlgHom hasSubst_single_var_log, ← MvPowerSeries.coe_substAlgHom hasSubst_renS]
  simp only [map_sum, map_add, map_mul]
  simp only [MvPowerSeries.coe_substAlgHom hasSubst_single_var_log, MvPowerSeries.coe_substAlgHom hasSubst_renS,
    MvPowerSeries.subst_C, MvPowerSeries.subst_X hasSubst_single_var_log]
  rw [Fintype.sum_sum_type, sum_extended_index, sum_extended_index, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, ext1]
  rw [subst_single_var hasSubst_renS, subst_single_var hasSubst_renS]
  simp [sideVariable, at1]

theorem hasSubst_hypLin (f f' : ι → n → MaximalUnramifiedExtension l) : MvPowerSeries.HasSubst (hypLin l f f') :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_hypLin f f')

theorem hasSubst_hypCoord (hl : 2 ≤ l) (f f' : ι → n → MaximalUnramifiedExtension l) :
    MvPowerSeries.HasSubst (Formalism.L2.Th1.E.hypCoord lgC (expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype (ext1 f) (ext1 f')) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_hypCoord hl f f')

theorem param_hyp (hl : 2 ≤ l) (f f' : ι → n → MaximalUnramifiedExtension l) (Θ : MvPowerSeries n ℂ_[l]) :
    MvPowerSeries.subst (fun v => (at1 v lgC : MvPowerSeries (ι ⊕ ι) ℂ_[l])) (MvPowerSeries.subst (hypLin l f f') Θ) =
      MvPowerSeries.subst sideVariable (inHyp l (ext1 f) (ext1 f') (MvPowerSeries.subst (fun i => at1 i lgC) Θ)) := by
  have h2 : MvPowerSeries.HasSubst (fun s : n => MvPowerSeries.subst
      (Formalism.L2.Th1.E.hypCoord lgC (expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype (ext1 f) (ext1 f')) (at1 s lgC)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s =>
      MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_hypCoord hl f f') (cc_hypCoord hl f f') (constantCoeff_inVar_eq_zero s)
  unfold inHyp
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_hypLin f f') hasSubst_single_var_log,
    MvPowerSeries.subst_comp_subst_apply hasSubst_single_var_log (hasSubst_hypCoord hl f f'),
    MvPowerSeries.subst_comp_subst_apply h2 hasSubst_renS]
  congr 1
  funext i
  rw [show (at1 i lgC : MvPowerSeries n ℂ_[l]) = PowerSeries.subst (MvPowerSeries.X i) lgC from rfl,
    subst_single_var (hasSubst_hypCoord hl f f') i, coord hl f f' i]

end Coord

section Assembly

variable {l : ℕ} [Fact l.Prime]

local notation "lgC" => lgF ℂ_[l] l

theorem hasSubst_pair_of_constantCoeff_eq_zero {σ R : Type} [CommRing R] [Finite σ] (x y : MvPowerSeries σ R)
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.HasSubst (![x, y] : Fin 2 → MvPowerSeries σ R) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by fin_cases j <;> simp [hx, hy]

theorem M_eq {ι : Type} [Fintype ι] (be : MvPowerSeries (Fin 2) (K0 l)) :
    MvPowerSeries.map (k0ToC l) (inParam l (sumBe l be : MvPowerSeries (ι ⊕ ι) (K0 l))) =
      MvPowerSeries.subst sideVariable (Formalism.L2.Th1.D.sumE (ι := ι) (N0 := 1) (N1 := 1)
        (MvPowerSeries.map (k0ToC l) (inParam l be))) := by
  unfold sumBe Formalism.L2.Th1.D.sumE
  have hsum : inParam l (∑ e : ι, sub2 l be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) =
      ∑ e : ι, inParam l (sub2 l be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) := by
    unfold inParam
    rw [← MvPowerSeries.coe_substAlgHom hasSubst_log, map_sum]
  rw [hsum, map_sum, ← MvPowerSeries.coe_substAlgHom hasSubst_renS, map_sum, sum_extended_index]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hasSubst_renS, map_inParam, map_inParam]
  unfold sub2
  rw [MvPowerSeries.map_subst (hasSubst_pair_of_constantCoeff_eq_zero _ _ (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _)),
    MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by fin_cases j <;> simp) hasSubst_single_var_log,
    MvPowerSeries.subst_comp_subst_apply hasSubst_single_var_log
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => MvPowerSeries.constantCoeff_X _),
    MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => MvPowerSeries.constantCoeff_X _)
        (fun j => MvPowerSeries.constantCoeff_X _) (constantCoeff_inVar_eq_zero j)) hasSubst_renS]
  congr 1
  funext j
  fin_cases j
  · simp only [at1, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, MvPowerSeries.map_X,
      MvPowerSeries.subst_X hasSubst_single_var_log]
    rw [subst_single_var (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => MvPowerSeries.constantCoeff_X _),
      subst_single_var hasSubst_renS]
    simp [sideVariable]
    exact MvPowerSeries.subst_X (hasSubst_single_var_log (l := l)) _
  · simp only [at1, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, MvPowerSeries.map_X,
      MvPowerSeries.subst_X hasSubst_single_var_log]
    rw [subst_single_var (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => MvPowerSeries.constantCoeff_X _),
      subst_single_var hasSubst_renS]
    simp [sideVariable]
    exact MvPowerSeries.subst_X (hasSubst_single_var_log (l := l)) _

theorem simeq_fsum {σ α : Type} (s : Finset α) (u v : α → MvPowerSeries σ ℂ_[l])
    (h : ∀ a ∈ s, Formalism.InvariantFactorPaths.G7.Simeq (u a) (v a)) :
    Formalism.InvariantFactorPaths.G7.Simeq (∑ a ∈ s, u a) (∑ a ∈ s, v a) := by
  classical
  have R := Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[l] σ
  induction s using Finset.induction_on with
  | empty => simpa using R.1 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact R.2.2.2.1 _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem simeq_sumE {ιr : Type} [Fintype ιr] {T Cb : MvPowerSeries (Fin 2) ℂ_[l]} (h : Formalism.InvariantFactorPaths.G7.Simeq T Cb) :
    Formalism.InvariantFactorPaths.G7.Simeq (Formalism.L2.Th1.D.sumE (ι := ιr) (N0 := 1) (N1 := 1) T)
      (Formalism.L2.Th1.D.sumE (ι := ιr) (N0 := 1) (N1 := 1) Cb) := by
  unfold Formalism.L2.Th1.D.sumE
  refine simeq_fsum _ _ _ fun e _ => ?_
  exact (Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[l] (Fin 2)).2.2.2.2 (Bool × E1 ιr) T Cb _
    (fun a => MvPowerSeries.constantCoeff_X _) (fun a => integral_X _) h

theorem hyperbolic_pair_extend {ι n : Type} [DecidableEq ι] [Fintype n] {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} {f f' : ι → n → MaximalUnramifiedExtension l}
    (hP : IsHypPair σ f f') : IsHypPair σ (ext1 f) (ext1 f') := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  refine ⟨fun e i => h1 e.1 i, fun e i => h2 e.1 i, fun e e' => h3 e.1 e'.1, fun e e' => h4 e.1 e'.1,
    fun e e' => ?_⟩
  simp only [ext1]
  rw [h5 e.1 e'.1]
  by_cases h : e.1 = e'.1
  · have he : e = e' := Prod.ext h (Subsingleton.elim _ _)
    simp [h, he]
  · have he : e ≠ e' := fun hh => h (hh ▸ rfl)
    simp [h, he]

theorem hyperbolic_of_orthogonal : HypOfOrth := by
  intro l _ h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hσ F hF hN ι n _ _ _ _ f f' hP be hbe0 hTie Θ hI
  have hl : 2 ≤ l := by omega
  obtain ⟨U0, Φ, hU0, hΦ0, hΦ, hEq⟩ := hypShape l h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hσ F hF hN 1 1 ι n
    (ext1 f) (ext1 f') (hyperbolic_pair_extend hP) _ hI
  rw [inParamK_eq] at hEq
  have hS0 : MvPowerSeries.constantCoeff (sumBe l be : MvPowerSeries (ι ⊕ ι) (K0 l)) = 0 := cc_sumBe hbe0
  have hM0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.map (k0ToC l) (inParam l (sumBe l be : MvPowerSeries (ι ⊕ ι) (K0 l))) : MvPowerSeries (ι ⊕ ι) ℂ_[l]) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, cc_inParam _ hS0, map_zero]
  have hR0 : MvPowerSeries.constantCoeff (MvPowerSeries.subst sideVariable Φ : MvPowerSeries (ι ⊕ ι) ℂ_[l]) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hasSubst_renS cc_renS hΦ0
  have hsim : Formalism.InvariantFactorPaths.G7.Simeq
      (MvPowerSeries.map (k0ToC l) (inParam l (sumBe l be : MvPowerSeries (ι ⊕ ι) (K0 l))) : MvPowerSeries (ι ⊕ ι) ℂ_[l])
      (MvPowerSeries.subst sideVariable Φ) := by
    have R := Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[l] (Bool × E1 ι)
    have R' := Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[l] (ι ⊕ ι)
    have h1 := R.2.2.2.2 (ι ⊕ ι) _ _ sideVariable cc_renS integral_renS (simeq_sumE (ιr := ι) hTie)
    have h2 := R.2.2.2.2 (ι ⊕ ι) _ _ sideVariable cc_renS integral_renS hΦ
    rw [M_eq]
    exact R'.2.2.1 _ _ _ h1 (R'.2.1 _ _ h2)
  rw [inParamK_eq, MvPowerSeries.subst_mul hasSubst_single_var_log, param_hyp hl, hEq, ← map_inParam, inParam_expS _ hS0,
    map_expS _ (cc_inParam _ hS0), MvPowerSeries.subst_mul hasSubst_renS, mvExp_eq, mvExp_eq,
    Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.subst_expS sideVariable cc_renS (-Φ) (by rw [map_neg, hΦ0, neg_zero])]
  have hneg : MvPowerSeries.subst sideVariable (-Φ) = -(MvPowerSeries.subst sideVariable Φ : MvPowerSeries (ι ⊕ ι) ℂ_[l]) := by
    rw [← MvPowerSeries.coe_substAlgHom hasSubst_renS, map_neg]
  rw [hneg]
  have key : Formalism.HermitianLattices.ExpSeriesBivariate.expS (-(MvPowerSeries.subst sideVariable Φ : MvPowerSeries (ι ⊕ ι) ℂ_[l])) *
        MvPowerSeries.subst sideVariable U0 *
        Formalism.HermitianLattices.ExpSeriesBivariate.expS (MvPowerSeries.map (k0ToC l) (inParam l (sumBe l be : MvPowerSeries (ι ⊕ ι) (K0 l)))) =
      MvPowerSeries.subst sideVariable U0 *
        Formalism.HermitianLattices.ExpSeriesBivariate.expS (MvPowerSeries.map (k0ToC l) (inParam l (sumBe l be : MvPowerSeries (ι ⊕ ι) (K0 l))) -
          MvPowerSeries.subst sideVariable Φ) := by
    rw [sub_eq_add_neg, Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.expS_add _ _ hM0 (by rw [map_neg, hR0, neg_zero])]
    ring
  rw [key]
  intro m
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' cc_renS integral_renS hU0) hsim.2 m

end Assembly

end Formalism.L2.KerInert.K1

namespace Formalism.L2.KerInert.K1

open Formalism.MainNotions.FormalGroupSystem

section Calc

variable {p : ℕ} [Fact p.Prime]

theorem simeq_iff_zero {ι : Type} (f g : MvPowerSeries ι (K0 p)) : Simeq p f g ↔ Simeq p (f - g) 0 := by
  simp only [Simeq, sub_zero]

theorem inParam_add {ι : Type} [Finite ι] (f g : MvPowerSeries ι (K0 p)) :
    inParam p (f + g) = inParam p f + inParam p g := by
  unfold inParam
  exact MvPowerSeries.subst_add hasSubst_log f g

theorem inParam_neg {ι : Type} [Finite ι] (f : MvPowerSeries ι (K0 p)) :
    inParam p (-f) = -inParam p f := by
  unfold inParam
  rw [← MvPowerSeries.coe_substAlgHom hasSubst_log, map_neg]

theorem z_add {ι : Type} [Finite ι] {d1 d2 : MvPowerSeries ι (K0 p)} (h1 : Simeq p d1 0) (h2 : Simeq p d2 0) :
    Simeq p (d1 + d2) 0 := by
  simp only [Simeq, sub_zero] at h1 h2 ⊢
  obtain ⟨c1, u1, hu1, e1⟩ := h1
  obtain ⟨c2, u2, hu2, e2⟩ := h2
  have hc1 : MvPowerSeries.constantCoeff d1 = 0 := c1
  have hc2 : MvPowerSeries.constantCoeff d2 = 0 := c2
  refine ⟨by rw [map_add, hc1, hc2, add_zero], u1 + u2 + u1 * u2, by simp [hu1, hu2], ?_⟩
  rw [inParam_add, expS_add' _ _ (cc_inParam d1 hc1) (cc_inParam d2 hc2), e1, e2]
  simp only [map_add, map_mul]
  ring

theorem z_neg {ι : Type} [Finite ι] {d : MvPowerSeries ι (K0 p)} (h : Simeq p d 0) : Simeq p (-d) 0 := by
  simp only [Simeq, sub_zero] at h ⊢
  obtain ⟨c, u, hu, e⟩ := h
  have hc : MvPowerSeries.constantCoeff d = 0 := c
  have hU : IsUnit (1 + u) := MvPowerSeries.isUnit_iff_constantCoeff.2 (by simp [hu])
  obtain ⟨v, hv⟩ := hU.exists_right_inv
  have hcv : MvPowerSeries.constantCoeff v = 1 := by
    have := congrArg MvPowerSeries.constantCoeff hv
    rwa [map_mul, map_one, map_add, map_one, hu, add_zero, one_mul] at this
  refine ⟨by rw [map_neg, hc, neg_zero], v - 1, by rw [map_sub, hcv, map_one, sub_self], ?_⟩
  have hinv := expS_neg_mul (inParam p d) (cc_inParam d hc)
  rw [e] at hinv
  have hx : expS p (-inParam p d) = MvPowerSeries.map (algebraMap (WW p) (K0 p)) v := by
    calc expS p (-inParam p d)
        = expS p (-inParam p d) * (MvPowerSeries.map (algebraMap (WW p) (K0 p)) (1 + u) *
            MvPowerSeries.map (algebraMap (WW p) (K0 p)) v) := by rw [← map_mul, hv, map_one, mul_one]
      _ = (expS p (-inParam p d) * (1 + MvPowerSeries.map (algebraMap (WW p) (K0 p)) u)) *
            MvPowerSeries.map (algebraMap (WW p) (K0 p)) v := by rw [map_add, map_one, mul_assoc]
      _ = MvPowerSeries.map (algebraMap (WW p) (K0 p)) v := by rw [hinv, one_mul]
  rw [inParam_neg, hx, map_sub, map_one, add_sub_cancel]

def sgn {σ τ : Type} (R : Type) [CommRing R] (π : σ → τ) (ε : σ → ℤ) : σ → MvPowerSeries τ R :=
  fun j => MvPowerSeries.C (ε j : R) * MvPowerSeries.X (π j)

theorem cc_sgn {σ τ R : Type} [CommRing R] (π : σ → τ) (ε : σ → ℤ) (j : σ) :
    MvPowerSeries.constantCoeff (sgn R π ε j) = 0 := by
  simp [sgn]

theorem hasSubst_sgn {σ τ R : Type} [CommRing R] [Finite σ] (π : σ → τ) (ε : σ → ℤ) :
    MvPowerSeries.HasSubst (sgn R π ε) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_sgn π ε)

theorem logF_odd (hp : p ≠ 2) :
    PowerSeries.subst (-PowerSeries.X : PowerSeries (K0 p)) (logF p) = -logF p := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  rw [show (-PowerSeries.X : PowerSeries (K0 p)) = (-1 : K0 p) • PowerSeries.X by simp,
    ← PowerSeries.rescale_eq_subst]
  ext n
  rw [PowerSeries.coeff_rescale, map_neg]
  simp only [logF, PowerSeries.coeff_mk, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [h, Odd.neg_one_pow (hodd.pow), neg_one_mul]
  · simp

theorem subst_log_sgn (hp : p ≠ 2) {τ : Type} (k : τ) (e : ℤ) (he : e = 1 ∨ e = -1) :
    PowerSeries.subst (MvPowerSeries.C (e : K0 p) * MvPowerSeries.X k : MvPowerSeries τ (K0 p)) (logF p) =
      MvPowerSeries.C (e : K0 p) * PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries τ (K0 p)) (logF p) := by
  rcases he with rfl | rfl
  · simp
  · have hX : PowerSeries.HasSubst (MvPowerSeries.X k : MvPowerSeries τ (K0 p)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X k)
    have hN : PowerSeries.HasSubst (-PowerSeries.X : PowerSeries (K0 p)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
    have h1 : PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries τ (K0 p)) (-PowerSeries.X : PowerSeries (K0 p)) =
        -MvPowerSeries.X k := by
      rw [← PowerSeries.coe_substAlgHom hX, map_neg, PowerSeries.coe_substAlgHom hX, PowerSeries.subst_X hX]
    have h2 := PowerSeries.subst_comp_subst_apply hN hX (logF p)
    rw [h1, logF_odd hp] at h2
    rw [Int.cast_neg, Int.cast_one, map_neg, map_one, neg_one_mul, neg_one_mul, ← h2,
      ← PowerSeries.coe_substAlgHom hX, map_neg]

theorem inParam_sgn (hp : p ≠ 2) {σ τ : Type} [Finite σ] [Finite τ] (π : σ → τ) (ε : σ → ℤ)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (d : MvPowerSeries σ (K0 p)) :
    inParam p (MvPowerSeries.subst (sgn (K0 p) π ε) d) = MvPowerSeries.subst (sgn (K0 p) π ε) (inParam p d) := by
  unfold inParam
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_sgn π ε) hasSubst_log,
    MvPowerSeries.subst_comp_subst_apply hasSubst_log (hasSubst_sgn π ε)]
  congr 1
  funext j
  rw [subst_single_var (hasSubst_sgn π ε), sgn, MvPowerSeries.subst_mul hasSubst_log, MvPowerSeries.subst_C,
    MvPowerSeries.subst_X hasSubst_log, subst_log_sgn hp _ _ (hε j)]

theorem z_sgn (hp : p ≠ 2) {σ τ : Type} [Finite σ] [Finite τ] (π : σ → τ) (ε : σ → ℤ)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) {d : MvPowerSeries σ (K0 p)} (h : Simeq p d 0) :
    Simeq p (MvPowerSeries.subst (sgn (K0 p) π ε) d) 0 := by
  simp only [Simeq, sub_zero] at h ⊢
  obtain ⟨c, u, hu, e⟩ := h
  have hc : MvPowerSeries.constantCoeff d = 0 := c
  have hs := hasSubst_sgn (R := K0 p) π ε
  have hsW := hasSubst_sgn (R := WW p) π ε
  refine ⟨MvPowerSeries.constantCoeff_subst_eq_zero hs (cc_sgn π ε) hc,
    MvPowerSeries.subst (sgn (WW p) π ε) u,
    MvPowerSeries.constantCoeff_subst_eq_zero hsW (cc_sgn π ε) hu, ?_⟩
  have e2 : expS p (inParam p (MvPowerSeries.subst (sgn (K0 p) π ε) d)) =
      MvPowerSeries.subst (sgn (K0 p) π ε) (expS p (inParam p d)) := by
    rw [inParam_sgn hp π ε hε, expS_eq _ (MvPowerSeries.constantCoeff_subst_eq_zero hs (cc_sgn π ε)
        (cc_inParam d hc)), expS_eq _ (cc_inParam d hc),
      Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.subst_expS _ (cc_sgn π ε) _ (cc_inParam d hc)]
  have hfun : (fun j => MvPowerSeries.map (algebraMap (WW p) (K0 p)) (sgn (WW p) π ε j)) = sgn (K0 p) π ε := by
    funext j
    rw [sgn, sgn, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X, map_intCast]
  have e3 : MvPowerSeries.subst (sgn (K0 p) π ε) (MvPowerSeries.map (algebraMap (WW p) (K0 p)) u) =
      MvPowerSeries.map (algebraMap (WW p) (K0 p)) (MvPowerSeries.subst (sgn (WW p) π ε) u) := by
    rw [MvPowerSeries.map_subst hsW, hfun]
  have e4 : MvPowerSeries.subst (sgn (K0 p) π ε) (1 : MvPowerSeries σ (K0 p)) = 1 := by
    rw [← MvPowerSeries.coe_substAlgHom hs, map_one]
  rw [e2, e, MvPowerSeries.subst_add hs, e3, e4]

end Calc

section Even

variable {p : ℕ} [Fact p.Prime]

theorem formalSum_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ (K0 p)} (ha : MvPowerSeries.HasSubst a)
    (be : MvPowerSeries (Fin 2) (K0 p)) (x y : MvPowerSeries σ (K0 p))
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.subst a (sub2 p be x y) = sub2 p be (MvPowerSeries.subst a x) (MvPowerSeries.subst a y) := by
  unfold sub2
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pair_of_constantCoeff_eq_zero x y hx hy) ha]
  exact congrArg (MvPowerSeries.subst · be) (funext fun j => by fin_cases j <;> rfl)

theorem subst_eq_formalSum {τ : Type} (a : Fin 2 → MvPowerSeries τ (K0 p)) (be : MvPowerSeries (Fin 2) (K0 p)) :
    MvPowerSeries.subst a be = sub2 p be (a 0) (a 1) := by
  unfold sub2
  exact congrArg (MvPowerSeries.subst · be) (funext fun j => by fin_cases j <;> rfl)

theorem formalSum_X_X (be : MvPowerSeries (Fin 2) (K0 p)) : sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 1) = be := by
  rw [← subst_eq_formalSum MvPowerSeries.X, MvPowerSeries.subst_self]
  rfl

theorem formalSum_zero_left {σ : Type} [Finite σ] {be : MvPowerSeries (Fin 2) (K0 p)} (hB : BeProp p be)
    (y : MvPowerSeries σ (K0 p)) (hy : MvPowerSeries.constantCoeff y = 0) : sub2 p be 0 y = 0 := by
  classical
  unfold sub2
  ext n
  rw [MvPowerSeries.coeff_subst (hasSubst_pair_of_constantCoeff_eq_zero 0 y (map_zero _) hy), map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : d 0 = 0
  · have : MvPowerSeries.coeff d be = 0 := by
      by_contra h
      have := (hB.ab d h).1
      omega
    rw [this, zero_smul]
  · have h0 : (d.prod fun s e => ((![0, y] : Fin 2 → MvPowerSeries σ (K0 p)) s) ^ e) = 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hd) (by simp [zero_pow hd])
    rw [h0, map_zero, smul_zero]

theorem formalSum_zero_right {σ : Type} [Finite σ] {be : MvPowerSeries (Fin 2) (K0 p)} (hB : BeProp p be)
    (x : MvPowerSeries σ (K0 p)) (hx : MvPowerSeries.constantCoeff x = 0) : sub2 p be x 0 = 0 := by
  classical
  unfold sub2
  ext n
  rw [MvPowerSeries.coeff_subst (hasSubst_pair_of_constantCoeff_eq_zero x 0 hx (map_zero _)), map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : d 1 = 0
  · have : MvPowerSeries.coeff d be = 0 := by
      by_contra h
      have := (hB.ab d h).2
      omega
    rw [this, zero_smul]
  · have h0 : (d.prod fun s e => ((![x, 0] : Fin 2 → MvPowerSeries σ (K0 p)) s) ^ e) = 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hd) (by simp [zero_pow hd])
    rw [h0, map_zero, smul_zero]

theorem even1 (hp : p ≠ 2) {be : MvPowerSeries (Fin 2) (K0 p)} (hB : BeProp p be) :
    Simeq p (be + sub2 p be (-MvPowerSeries.X 0) (MvPowerSeries.X 1)) 0 := by
  have h := z_neg (z_sgn hp (![0, 0, 1] : Fin 3 → Fin 2) ![1, -1, 1]
    (fun j => by fin_cases j <;> simp) hB.add1)
  have hs := hasSubst_sgn (R := K0 p) (![0, 0, 1] : Fin 3 → Fin 2) ![1, -1, 1]
  rw [MvPowerSeries.subst_sub hs, MvPowerSeries.subst_sub hs,
    formalSum_subst hs _ _ _ (by simp) (by simp), formalSum_subst hs _ _ _ (by simp) (by simp),
    formalSum_subst hs _ _ _ (by simp) (by simp), MvPowerSeries.subst_add hs] at h
  simp only [MvPowerSeries.subst_X hs, sgn, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Int.cast_one, Int.cast_neg, map_one, map_neg, one_mul, neg_mul,
    add_neg_cancel] at h
  rw [formalSum_zero_left hB _ (by simp), formalSum_X_X] at h
  convert h using 1
  ring

theorem even2 (hp : p ≠ 2) {be : MvPowerSeries (Fin 2) (K0 p)} (hB : BeProp p be) :
    Simeq p (be + sub2 p be (MvPowerSeries.X 0) (-MvPowerSeries.X 1)) 0 := by
  have h := z_neg (z_sgn hp (![0, 1, 1] : Fin 3 → Fin 2) ![1, 1, -1]
    (fun j => by fin_cases j <;> simp) hB.add2)
  have hs := hasSubst_sgn (R := K0 p) (![0, 1, 1] : Fin 3 → Fin 2) ![1, 1, -1]
  rw [MvPowerSeries.subst_sub hs, MvPowerSeries.subst_sub hs,
    formalSum_subst hs _ _ _ (by simp) (by simp), formalSum_subst hs _ _ _ (by simp) (by simp),
    formalSum_subst hs _ _ _ (by simp) (by simp), MvPowerSeries.subst_add hs] at h
  simp only [MvPowerSeries.subst_X hs, sgn, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Int.cast_one, Int.cast_neg, map_one, map_neg, one_mul, neg_mul,
    add_neg_cancel] at h
  rw [formalSum_zero_right hB _ (by simp), formalSum_X_X] at h
  convert h using 1
  ring

end Even

section Even2

variable {p : ℕ} [Fact p.Prime]

theorem subst_negX {σ τ : Type} {a : σ → MvPowerSeries τ (K0 p)} (ha : MvPowerSeries.HasSubst a) (j : σ) :
    MvPowerSeries.subst a (-MvPowerSeries.X j : MvPowerSeries σ (K0 p)) = -a j := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_neg, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_X ha]

theorem even3 (hp : p ≠ 2) {be : MvPowerSeries (Fin 2) (K0 p)} (hB : BeProp p be) :
    Simeq p (sub2 p be (-MvPowerSeries.X 0) (-MvPowerSeries.X 1) - be) 0 := by
  have h3 := z_sgn hp (id : Fin 2 → Fin 2) ![-1, 1] (fun j => by fin_cases j <;> simp) (even2 hp hB)
  have hs := hasSubst_sgn (R := K0 p) (id : Fin 2 → Fin 2) ![-1, 1]
  rw [MvPowerSeries.subst_add hs, formalSum_subst hs _ _ _ (by simp) (by simp), subst_negX hs,
    MvPowerSeries.subst_X hs, subst_eq_formalSum] at h3
  simp only [sgn, id, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_one, Int.cast_neg,
    map_one, map_neg, one_mul, neg_mul] at h3
  have h1 := z_neg (even1 hp hB)
  convert z_add h3 h1 using 1
  ring

theorem z_sum {σ α : Type} [Finite σ] (s : Finset α) (u : α → MvPowerSeries σ (K0 p))
    (h : ∀ a ∈ s, Simeq p (u a) 0) : Simeq p (∑ a ∈ s, u a) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using simeq_refl' (p := p) (0 : MvPowerSeries σ (K0 p))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact z_add (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem sum_beta_even : SumBeEven := by
  intro p _ hp ι _ be hB
  rw [simeq_iff_zero]
  have hN : MvPowerSeries.HasSubst (fun i : ι ⊕ ι => (-MvPowerSeries.X i : MvPowerSeries (ι ⊕ ι) (K0 p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp
  have heq : MvPowerSeries.subst (fun i => -MvPowerSeries.X i) (sumBe p be : MvPowerSeries (ι ⊕ ι) (K0 p)) -
      sumBe p be = ∑ e : ι, MvPowerSeries.subst (sgn (K0 p) ![Sum.inl e, Sum.inr e] ![1, 1])
        (sub2 p be (-MvPowerSeries.X 0) (-MvPowerSeries.X 1) - be) := by
    unfold sumBe
    rw [← MvPowerSeries.coe_substAlgHom hN, map_sum, MvPowerSeries.coe_substAlgHom hN, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hσ := hasSubst_sgn (R := K0 p) (![Sum.inl e, Sum.inr e] : Fin 2 → ι ⊕ ι) ![1, 1]
    rw [formalSum_subst hN _ _ _ (by simp) (by simp), MvPowerSeries.subst_X hN, MvPowerSeries.subst_X hN,
      MvPowerSeries.subst_sub hσ, formalSum_subst hσ _ _ _ (by simp) (by simp), subst_negX hσ, subst_negX hσ,
      subst_eq_formalSum]
    simp [sgn]
  rw [heq]
  exact z_sum _ _ fun e _ => z_sgn hp _ _ (fun j => by fin_cases j <;> simp) (even3 hp hB)

end Even2

section Iff

variable {p : ℕ} [Fact p.Prime]

theorem intR_mul {ι K1 : Type} [Field K1] {R1 : Subring K1} {f g : MvPowerSeries ι K1} (hf : IntR R1 f)
    (hg : IntR R1 g) : IntR R1 (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hf _) (hg _)

theorem inParamK_map {ι K1 : Type} [Finite ι] [Field K1] [Algebra (K0 p) K1] (g : MvPowerSeries ι (K0 p)) :
    inParamK p K1 (MvPowerSeries.map (algebraMap (K0 p) K1) g) =
      MvPowerSeries.map (algebraMap (K0 p) K1) (inParam p g) := by
  unfold inParamK inParam
  rw [MvPowerSeries.map_subst hasSubst_log]
  congr 1
  funext i
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)),
    MvPowerSeries.map_X]

theorem inParamK_mul {ι K1 : Type} [Finite ι] [Field K1] [Algebra (K0 p) K1] (f g : MvPowerSeries ι K1) :
    inParamK p K1 (f * g) = inParamK p K1 f * inParamK p K1 g := by
  unfold inParamK
  exact MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_log, map_zero])) f g

theorem first_kernel_general_iff : FirstKernelGeneratorIff := by
  intro p _ hp ι _ K1 _ _ R1 hW be Th
  refine ⟨fun h => ?_, fun h => first_kernel_of_sum p ι K1 R1 be Th h.1 h.2.1 h.2.2⟩
  obtain ⟨Ph, U, hTh, hU, -, hB, hPS⟩ := h
  change Simeq p Ph (sumBe p be) at hPS
  refine ⟨hB, sum_beta_even p hp ι be hB, ?_⟩
  have hS0 : MvPowerSeries.constantCoeff (sumBe p be : MvPowerSeries (ι ⊕ ι) (K0 p)) = 0 := cc_sumBe (cc_be hB)
  have hP0 : MvPowerSeries.constantCoeff Ph = 0 := by
    have := hPS.1
    rwa [map_sub, hS0, sub_zero] at this
  have hz := z_neg ((simeq_iff_zero Ph _).1 hPS)
  obtain ⟨-, v, -, hv⟩ := hz
  rw [sub_zero, neg_sub] at hv
  have hD0 : MvPowerSeries.constantCoeff (sumBe p be - Ph : MvPowerSeries (ι ⊕ ι) (K0 p)) = 0 := by
    rw [map_sub, hS0, hP0, sub_zero]
  have key : Th * MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (sumBe p be)) =
      U * MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (sumBe p be - Ph)) := by
    rw [hTh, sub_eq_add_neg, expS_add' _ _ hS0 (by rw [map_neg, hP0, neg_zero]), map_mul]
    ring
  rw [key, inParamK_mul, inParamK_map, inParam_expS _ hD0, hv]
  refine intR_mul hU fun n => ?_
  rw [MvPowerSeries.coeff_map, ← map_one (MvPowerSeries.map (algebraMap (WW p) (K0 p))), ← map_add,
    MvPowerSeries.coeff_map]
  exact hW _

theorem first_kernel_of_orthogonal : FirstKernelGeneratorOfOrthogonal := by
  intro l _ h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hσ F hF hN ι n _ _ _ _ f f' hP be hB hTie Θ hI
  letI := Formalism.L2.G.Pend.wittFractionAlgebraCp l
  exact first_kernel_of_sum l ι ℂ_[l] (Formalism.L2.G.Pend.OcC l) be _ hB (sum_beta_even l (by omega) ι be hB)
    (hyperbolic_of_orthogonal l h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hσ F hF hN ι n f f' hP be (cc_be hB) hTie Θ hI)

end Iff

end Formalism.L2.KerInert.K1
