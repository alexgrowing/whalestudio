import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis
open scoped ComplexConjugate

variable {D : D7}

theorem hasDerivAt_line_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (E Φ : V → ℂ)
    (hE : Differentiable ℝ E) (hΦ : Differentiable ℝ Φ) (K : ℂ) (z v : V) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * K) * (E (z + t • v) * Φ (z + t • v)))
      (K * (E z * Φ z) + (fderiv ℝ E z v * Φ z + E z * fderiv ℝ Φ z v)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * K)) K 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const K).cexp
    simpa using this
  have hl : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hE' : HasDerivAt (fun t : ℝ => E (z + t • v)) (fderiv ℝ E z v) 0 := by
    have := (hE (z + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rwa [zero_smul, add_zero] at this
  have hΦ' : HasDerivAt (fun t : ℝ => Φ (z + t • v)) (fderiv ℝ Φ z v) 0 := by
    have := (hΦ (z + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rwa [zero_smul, add_zero] at this
  refine (h1.mul (hE'.mul hΦ')).congr_deriv ?_
  simp only [Pi.mul_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero, zero_smul, add_zero, one_mul]

theorem formAt_gram_one {S T : HSp D} (hS1 : S.gram = 1) (hT1 : T.gram = 1) (τ : D.what₂.Tau)
    (x y : Fin T.rank → Fin S.rank → ℂ) :
    ((GlobalTheory.OrientedHeis.formAt S T τ x y : ℝ) : ℂ) = Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * (∑ i, ∑ j, x i j * conj (y i j)) -
      Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * conj (∑ i, ∑ j, x i j * conj (y i j)) := by
  have hS : ∀ a b, tauE D τ ((S.gram⁻¹) a b) = if a = b then 1 else 0 := fun a b => by
    rw [hS1, inv_one, Matrix.one_apply]; split_ifs <;> simp
  have hT : ∀ a b, tauE D τ (T.gram a b) = if a = b then 1 else 0 := fun a b => by
    rw [hT1, Matrix.one_apply]; split_ifs <;> simp
  have hs : ∑ a, ∑ b, ∑ e, ∑ d, tauE D τ (S.gram⁻¹ a b) * conj (y e b) * tauE D τ (T.gram e d) * x d a =
      ∑ i, ∑ j, x i j * conj (y i j) := by
    simp only [hS, hT, ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have h1 : ∀ a : Fin S.rank, (∑ b : Fin S.rank, ∑ e : Fin T.rank,
        if a = b then conj (y e b) * x e a else 0) = ∑ e : Fin T.rank, conj (y e a) * x e a := fun a => by
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    simp only [h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm (conj (y i j)) (x i j)
  unfold GlobalTheory.OrientedHeis.formAt
  rw [hs, GlobalTheory.FockPos.xi_zero_eq_host τ]
  push_cast
  rw [Complex.re_eq_add_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem omO_gram_one {S T : HSp D} (hS1 : S.gram = 1) (hT1 : T.gram = 1) (z v : RW T S) :
    ((GlobalTheory.OrientedHeis.omO S T z v : ℝ) : ℂ) =
      Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * (∑ τ, ∑ i, ∑ j, z τ i j * conj (v τ i j)) -
        Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * conj (∑ τ, ∑ i, ∑ j, z τ i j * conj (v τ i j)) := by
  show ((∑ τ, GlobalTheory.OrientedHeis.formAt S T τ (z τ) (v τ) : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]
  simp only [formAt_gram_one hS1 hT1, map_sum, Finset.mul_sum, Finset.sum_sub_distrib]

theorem reads_isFockVacAt : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Differentiable ℂ G → Reads ψ θ hS hT cc δ r G f → ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f := by
  intro D ψ θ S T a d hS hT cc δ r hset G f hG hR τ
  subst hS hT
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hset.inf
  have hψ := hset.std
  have hth : IsThetaFunO ψ S T f := hR.1
  have hR' := ((reads_iff hset.crv hset.scale G f).1 hR).2
  obtain ⟨hEd, hEc⟩ := GlobalTheory.FockPos.gauss_cr (ι := D.what₂.Tau) (m := T.rank) (n := S.rank) (-Formalism.L2.Pj.xiR D)
  set E : VC D S.rank T.rank → ℂ := fun Z =>
    Complex.exp ((Real.pi * (-Formalism.L2.Pj.xiR D) * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) with hEdef
  let L : VC D S.rank T.rank →L[ℂ] VC D S.rank T.rank := LinearMap.toContinuousLinearMap
    { toFun := fun Z τ i j => δ * embT D τ r * Z τ i j
      map_add' := fun Y Z => by funext τ i j; simp only [Pi.add_apply]; ring
      map_smul' := fun c Z => by funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  set Φ : VC D S.rank T.rank → ℂ := fun Z => G (fun τ i j => δ * embT D τ r * Z τ i j) with hΦdef
  have hΦd : Differentiable ℂ Φ := hG.comp L.differentiable
  have hΦc : ∀ z v : VC D S.rank T.rank, fderiv ℝ Φ z (Complex.I • v) = Complex.I * fderiv ℝ Φ z v := fun z v => by
    rw [((hΦd z).hasFDerivAt.restrictScalars ℝ).fderiv]
    exact (fderiv ℂ Φ z).map_smul Complex.I v
  have hreal : ∀ w : WO S T, w.map (finPart D) = 0 → ∀ x : RW T S, (w + iotaW σ T S x).map (finPart D) = 0 := by
    intro w hw x
    have h2 := h.real_iota T S x
    ext i j
    have a1 := congrFun (congrFun hw i) j
    have a2 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at a1 a2 ⊢
    rw [Matrix.add_apply, (finPart D).map_add, a1, a2, add_zero]
  have hval : ∀ w : WO S T, w.map (finPart D) = 0 → f w = E (piW θ T S w) * Φ (piW θ T S w) := by
    intro w hw
    rw [hR' w hw]
    have hz : GlobalTheory.FockPos.zCo θ 1 1 w = piW θ T S w := by
      funext τ
      have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
        Matrix.map_one _ (map_zero _) (map_one _)
      simp only [GlobalTheory.FockPos.zCo, e, inv_one, Matrix.one_mul, Matrix.mul_one]
      rfl
    rw [GlobalTheory.FockPos.gaussO, hz]
    show Complex.exp _ * G _ = Complex.exp _ * G _
    congr 2
    push_cast
    ring
  have hline : ∀ (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) (x : RW T S),
      (∀ t : ℝ, lineAt θ τ u t = iotaW σ T S (t • x)) → ∀ w : WO S T, w.map (finPart D) = 0 →
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f w =
        (-(Real.pi * Complex.I) * ((GlobalTheory.OrientedHeis.omO S T (piW θ T S w) x : ℝ) : ℂ)) *
            (E (piW θ T S w) * Φ (piW θ T S w)) +
          (fderiv ℝ E (piW θ T S w) x * Φ (piW θ T S w) + E (piW θ T S w) * fderiv ℝ Φ (piW θ T S w) x) := by
    intro u x hx w hw
    have hfun : (fun t : ℝ => heisO ψ S T (lineAt θ τ u t) f w) = fun t : ℝ =>
        Complex.exp ((t : ℂ) * (-(Real.pi * Complex.I) * ((GlobalTheory.OrientedHeis.omO S T (piW θ T S w) x : ℝ) : ℂ))) *
          (E (piW θ T S w + t • x) * Φ (piW θ T S w + t • x)) := by
      funext t
      rw [hx t, heisO_iota h hψ, hval _ (hreal w hw _), AddMonoidHom.map_add, h.pi_iota T S, LinearMap.map_smul]
      congr 2
      rw [smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [Formalism.IndefR.Datum.dRho, hfun]
    exact (hasDerivAt_line_mul E Φ hEd (hΦd.restrictScalars ℝ) _ _ _).deriv
  let X : Matrix (Fin T.rank) (Fin S.rank) ℂ → RW T S := fun u τ' i j => if τ' = τ then u i j else 0
  have hX : ∀ u (t : ℝ), lineAt θ τ u t = iotaW σ T S (t • X u) := fun u t => by
    rw [GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ u t]
    congr 2
    funext τ' i j
    by_cases e : τ' = τ
    · subst e
      simp [X, Pi.single, Function.update]
    · simp [X, e, Pi.single, Function.update]
  have hXI : ∀ u, X (Complex.I • u) = Complex.I • X u := fun u => by
    funext τ' i j
    by_cases e : τ' = τ <;> simp [X, e]
  have hJ : ∀ u : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      cplxO (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) u = Complex.I • u :=
    fun u => by simp only [cplxO, Matrix.one_mul, Matrix.mul_one]
  intro u
  have hθa : IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ (cplxO 1 1) u f) := by
    have hc := (GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hset.inf S T f hth).2
    exact (GlobalTheory.FinWeilO.thetaSub ψ S T).add_mem (hc τ u)
      ((GlobalTheory.FinWeilO.thetaSub ψ S T).smul_mem Complex.I (hc τ _))
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hθa fun w hw => ?_
  have hw' : w.map (finPart D) = 0 := hw
  show Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f w +
    Complex.I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO 1 1 u) f w = 0
  rw [hJ, hline u (X u) (hX u) w hw', hline _ (X (Complex.I • u)) (hX _) w hw', hXI]
  have hp' : ∑ τ', ∑ i, ∑ j, piW θ T S w τ' i j * conj ((Complex.I • X u) τ' i j) =
      -Complex.I * ∑ τ', ∑ i, ∑ j, piW θ T S w τ' i j * conj (X u τ' i j) := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [omO_gram_one hset.gS hset.gT, omO_gram_one hset.gS hset.gT, hp', hΦc]
  simp only [map_mul, map_neg, Complex.conj_I, neg_neg]
  have key := hEc (piW θ T S w) (X u)
  rw [Complex.ofReal_neg] at key
  set P := ∑ τ', ∑ i, ∑ j, piW θ T S w τ' i j * conj (X u τ' i j) with hP
  linear_combination (Φ (piW θ T S w)) * key +
    (E (piW θ T S w) * Φ (piW θ T S w) * (Real.pi : ℂ) * (Formalism.L2.Pj.xiR D : ℂ) *
        (Complex.I ^ 2 * (P + conj P) - 2 * P) + E (piW θ T S w) * fderiv ℝ Φ (piW θ T S w) (X u)) * Complex.I_sq

end GlobalTheory.NormExact
