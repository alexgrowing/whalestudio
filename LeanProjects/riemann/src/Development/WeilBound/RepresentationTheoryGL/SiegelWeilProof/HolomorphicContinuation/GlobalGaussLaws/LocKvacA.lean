import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoI

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

def ptX {m : ℕ} (u : Matrix (Fin m) (Fin n) ℂ) : Fin m × Fin n × Bool → ℂ := fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1

theorem evX_eq_eval {m : ℕ} (Q : PX m n) (u : Matrix (Fin m) (Fin n) ℂ) : evX Q u = eval (ptX u) Q := rfl

theorem ptX_add_smul {m : ℕ} (u w : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    ptX (u + (t : ℂ) • w) = ptX u + (t : ℂ) • ptX w := by
  funext k
  simp only [ptX, Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [Complex.conj_ofReal]

theorem gAway_add_dirAt (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (X : Matrix (Fin V.rank) (Fin n) ℂ) (t : ℝ) :
    gAway V l s τ (z + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X) = gAway V l s τ z := by
  have hz : ∀ τ', τ' ≠ τ → (z + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X) τ' = z τ' := by
    intro τ' h
    rw [Pi.add_apply, Pi.smul_apply, dirAt_ne h, smul_zero, add_zero]
  delta gAway
  beta_reduce
  congr 2
  refine Finset.sum_congr rfl fun τ' hτ' => ?_
  rw [hz τ' (by simpa using hτ')]

theorem gaussian_vacuum_add_line {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) (x : Mx D V.rank n)
    (X : Matrix (Fin V.rank) (Fin n) ℂ) (t : ℝ) :
    psi0 θ V n l s τ (x + lineAt θ τ X t) = psi0 θ V n l s τ x := by
  obtain ⟨-, hfinL, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ X
  have h1 : (fun τ' => compAt θ τ' (x + lineAt θ τ X t)) =
      (fun τ' => compAt θ τ' x) + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X := by
    funext τ'
    have hadd : compAt θ τ' (x + lineAt θ τ X t) = compAt θ τ' x + compAt θ τ' (lineAt θ τ X t) := by
      ext i j
      show (θ τ') (infPart D ((x + lineAt θ τ X t) i j)) =
        (θ τ') (infPart D (x i j)) + (θ τ') (infPart D (lineAt θ τ X t i j))
      rw [show (x + lineAt θ τ X t) i j = x i j + lineAt θ τ X t i j from rfl, map_add, map_add]
    rw [hadd, hcomp t τ', Pi.add_apply, Pi.smul_apply]
    by_cases h : τ' = τ
    · rw [if_pos h, h, dirAt_self]
    · rw [if_neg h, dirAt_ne h, smul_zero]
  have h2 : (fun i j => finPart D ((x + lineAt θ τ X t) i j)) = (fun i j => finPart D (x i j)) := by
    funext i j
    have h0 : finPart D (lineAt θ τ X t i j) = 0 := congrFun (congrFun (hfinL t) i) j
    rw [show (x + lineAt θ τ X t) i j = x i j + lineAt θ τ X t i j from rfl, map_add, h0, add_zero]
  show gAway V l s τ (fun τ' => compAt θ τ' (x + lineAt θ τ X t)) *
      g0 D V.rank n (fun i j => finPart D ((x + lineAt θ τ X t) i j)) =
    gAway V l s τ (fun τ' => compAt θ τ' x) * g0 D V.rank n (fun i j => finPart D (x i j))
  rw [h1, h2, gAway_add_dirAt]

private theorem hasDerivAt_mvPolynomial_eval_line_zero {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℂ) (a v : σ → ℂ) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (a + (t : ℂ) • v) p)
      (∑ k, v k * MvPolynomial.eval a (MvPolynomial.pderiv k p)) 0 := by
  induction p using MvPolynomial.induction_on
  next r =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  next p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  next p i hp =>
    have hX : HasDerivAt (fun t : ℝ => (a + (t : ℂ) • v) i) (v i) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
      have h2 := (h1.mul_const (v i)).const_add (a i)
      simpa using h2
    have h := hp.mul hX
    simp only [map_mul, MvPolynomial.eval_X]
    refine h.congr_deriv ?_
    have hk : ∀ k, MvPolynomial.eval a (MvPolynomial.pderiv k (p * MvPolynomial.X i)) =
        MvPolynomial.eval a (MvPolynomial.pderiv k p) * a i +
          (if i = k then MvPolynomial.eval a p else 0) := by
      intro k
      rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
        MvPolynomial.eval_X, Pi.single_apply]
      split_ifs with h
      · simp only [map_one, mul_one]
        ring
      · simp only [map_zero, mul_zero, zero_add, add_zero]
        ring
    have hs1 : ∑ k, v k * (MvPolynomial.eval a (MvPolynomial.pderiv k p) * a i) =
        (∑ k, v k * MvPolynomial.eval a (MvPolynomial.pderiv k p)) * a i := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hs2 : ∑ k, v k * (if i = k then MvPolynomial.eval a p else 0) = MvPolynomial.eval a p * v i := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
        ring
      · intro b _ hb
        rw [if_neg (Ne.symm hb), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    simp only [hk, mul_add, Finset.sum_add_distrib, hs1, hs2, Complex.ofReal_zero, zero_smul, add_zero]

private theorem hasDerivAt_norm_sq_add_smul_zero (u w : ℂ) :
    HasDerivAt (fun t : ℝ => ‖u + (t : ℂ) * w‖ ^ 2) (2 * (star u * w).re) 0 := by
  have h : (fun t : ℝ => ‖u + (t : ℂ) * w‖ ^ 2) =
      fun t : ℝ => (u.re + t * w.re) * (u.re + t * w.re) + (u.im + t * w.im) * (u.im + t * w.im) := by
    funext t
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  rw [h]
  have h1 : HasDerivAt (fun t : ℝ => u.re + t * w.re) w.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.re).const_add u.re
  have h2 : HasDerivAt (fun t : ℝ => u.im + t * w.im) w.im 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.im).const_add u.im
  refine ((h1.mul h1).add (h2.mul h2)).congr_deriv ?_
  show _ = 2 * ((starRingEnd ℂ) u * w).re
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem hasDerivAt_gs_line_zero {m : ℕ} (c : ℝ) (U W : Matrix (Fin m) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => gs c (U + (t : ℂ) • W))
      (gs c U * (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ))) 0 := by
  have hr : HasDerivAt (fun t : ℝ => c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2)
      (c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re) 0 := by
    refine HasDerivAt.const_mul c ?_
    first
      | exact HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun i _ => hasDerivAt_norm_sq_add_smul_zero (U a i) (W a i)
      | exact HasDerivAt.sum fun a _ => HasDerivAt.sum fun i _ => hasDerivAt_norm_sq_add_smul_zero (U a i) (W a i)
  have hn : HasDerivAt (fun t : ℝ => -((c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2 : ℝ) : ℂ))
      (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ)) 0 := hr.ofReal_comp.neg
  have hc := hn.cexp
  have e0 : (fun t : ℝ => gs c (U + (t : ℂ) • W)) =
      fun t : ℝ => Complex.exp (-((c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2 : ℝ) : ℂ)) := by
    funext t
    rfl
  rw [e0]
  refine hc.congr_deriv ?_
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  rfl

theorem annS_tens {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (X : Matrix (Fin V.rank) (Fin n) ℂ) (x : Mx D V.rank n) :
    annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) x =
      (∑ k, ptX (fr⁻¹ * X) k * eval (ptX (fr⁻¹ * compAt θ τ x)) (pderiv k Q)) *
        gs (cLoc l τ) (fr⁻¹ * compAt θ τ x) * psi0 θ V n l s τ x := by
  obtain ⟨-, -, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ X
  set c := cLoc l τ with hc
  set z := compAt θ τ x with hz
  set U : Matrix (Fin V.rank) (Fin n) ℂ := fr⁻¹ * z with hU
  set W : Matrix (Fin V.rank) (Fin n) ℂ := fr⁻¹ * X with hW
  set Ψx := psi0 θ V n l s τ x with hΨ
  have hadd : ∀ y : Mx D V.rank n, compAt θ τ (x + y) = z + compAt θ τ y := by
    intro y
    ext i j
    show (θ τ) (infPart D ((x + y) i j)) = (θ τ) (infPart D (x i j)) + (θ τ) (infPart D (y i j))
    rw [show (x + y) i j = x i j + y i j from rfl, map_add, map_add]
  have hcz : ∀ t : ℝ, compAt θ τ (x + lineAt θ τ X t) = z + (t : ℂ) • X := by
    intro t
    rw [hadd, hcomp t τ, if_pos rfl]
  have hφ : ∀ t : ℝ, tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t) =
      eval (ptX U + (t : ℂ) • ptX W) Q * gs c (U + (t : ℂ) • W) * Ψx := by
    intro t
    have e1 : fr⁻¹ * compAt θ τ (x + lineAt θ τ X t) = U + (t : ℂ) • W := by
      rw [hcz t, Matrix.mul_add, Matrix.mul_smul]
    show fP c Q (fr⁻¹ * compAt θ τ (x + lineAt θ τ X t)) * psi0 θ V n l s τ (x + lineAt θ τ X t) = _
    rw [e1, gaussian_vacuum_add_line hθ V l s τ x X t]
    show evX Q (U + (t : ℂ) • W) * gs c (U + (t : ℂ) • W) * Ψx = _
    rw [evX_eq_eval, ptX_add_smul]
  have hderiv : HasDerivAt (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t))
      ((∑ k, ptX W k * eval (ptX U) (pderiv k Q)) * gs c U * Ψx +
        eval (ptX U) Q * (gs c U * (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ))) * Ψx) 0 := by
    have hP := hasDerivAt_mvPolynomial_eval_line_zero Q (ptX U) (ptX W)
    have hG := hasDerivAt_gs_line_zero c U W
    rw [show (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t)) =
        fun t : ℝ => eval (ptX U + (t : ℂ) • ptX W) Q * gs c (U + (t : ℂ) • W) * Ψx from funext hφ]
    refine ((hP.mul hG).mul_const Ψx).congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_smul, add_zero]
    ring
  have hφx : tens θ τ fr (fP c Q) (psi0 θ V n l s τ) x = eval (ptX U) Q * gs c U * Ψx := by
    have h0 := hφ 0
    simp only [map_zero, add_zero, Complex.ofReal_zero, zero_smul] at h0
    exact h0
  have hdet : IsUnit fr.det := hfr.1
  have hdetH : IsUnit frᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star
  have hGs : gramAt D V τ * s τ = (fr⁻¹)ᴴ * fr⁻¹ := by
    have h := hfr.2.2
    calc gramAt D V τ * s τ = (frᴴ)⁻¹ * (frᴴ * (gramAt D V τ * s τ) * fr) * fr⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
            ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mul]
      _ = (fr⁻¹)ᴴ * fr⁻¹ := by
          rw [h, Matrix.mul_one, Matrix.conjTranspose_nonsing_inv]
  have e1' : ∑ a, ∑ i, 2 * (star (U a i) * W a i).re = 2 * (Uᴴ * W).trace.re := by
    show _ = 2 * (∑ i, (Uᴴ * W) i i).re
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_comm
  have e2' : Uᴴ * W = zᴴ * (gramAt D V τ * s τ) * X := by
    rw [hGs]
    simp only [hU, hW, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e3' : (zᴴ * (gramAt D V τ * s τ) * X).trace.re = (Xᴴ * (gramAt D V τ * s τ) * z).trace.re := by
    have h : Xᴴ * (gramAt D V τ * s τ) * z = (zᴴ * (gramAt D V τ * s τ) * X)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        (hM τ).eq, Matrix.mul_assoc]
    rw [h, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
  have hc' : c = 2 * Real.pi * |l τ| := rfl
  have hlin : GlobalTheory.StdUnn.linF V l s τ X z = ((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ) := by
    show ((4 * Real.pi * |l τ| * (Xᴴ * (gramAt D V τ * s τ) * z).trace.re : ℝ) : ℂ) = _
    congr 1
    rw [e1', e2', e3', hc']
    ring
  show deriv (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t)) 0 +
      GlobalTheory.StdUnn.linF V l s τ X z * tens θ τ fr (fP c Q) (psi0 θ V n l s τ) x = _
  rw [hderiv.deriv, hφx, hlin]
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
