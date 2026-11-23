import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenC
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMultiplierTemperate

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Sw.Glob.UnipH

variable {D : D7}

def ur {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  M.submatrix (fun i => finSumFinEquiv (Sum.inl i)) (fun j => finSumFinEquiv (Sum.inr j))

theorem unipotent_part_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : ur (blk4 a b c d) = b := by
  ext i j
  simp only [ur, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]

theorem compAt_ur (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (ur M) = ur (compAt θ τ M) := rfl

theorem fin_ur {n : ℕ} (M : Mx D (n + n) (n + n)) : (ur M).map (finPart D) = ur (M.map (finPart D)) := rfl

theorem one_eq_block_matrix {R : Type} [CommRing R] {n : ℕ} : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = blk4 1 0 0 1 :=
  GlobalTheory.StdUnn.Frame.block_matrix_one.symm

theorem mat_iota_nU {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {n : ℕ} {ι : GR n →* G D n}
    (hι : IsPlaceEmb θ τ ι) (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ) (hyb : mR y = nU b) :
    mat (ι y) = blk4 1 (ur (mat (ι y))) 0 1 ∧ compAt θ τ (ur (mat (ι y))) = b ∧
      (∀ τ', τ' ≠ τ → compAt θ τ' (ur (mat (ι y))) = 0) ∧ (ur (mat (ι y))).map (finPart D) = 0 := by
  obtain ⟨h1, h2, h3⟩ := hι.2 y
  have e1 : compAt θ τ (ur (mat (ι y))) = b := by
    rw [compAt_ur, h1, hyb]
    exact unipotent_part_block_matrix 1 b 0 1
  have e2 : ∀ τ', τ' ≠ τ → compAt θ τ' (ur (mat (ι y))) = 0 := by
    intro τ' h
    rw [compAt_ur, h2 τ' h, one_eq_block_matrix, unipotent_part_block_matrix]
  have e3 : (ur (mat (ι y))).map (finPart D) = 0 := by
    rw [fin_ur, h3, one_eq_block_matrix, unipotent_part_block_matrix]
  refine ⟨?_, e1, e2, e3⟩
  apply GlobalTheory.StabAtPlace.mx_ext hθ
  · rw [h3, OG.finite_part_block_matrix, e3, Matrix.map_zero _ (map_zero (finPart D)), Matrix.map_one _ (map_zero (finPart D)) (map_one (finPart D)),
      one_eq_block_matrix]
  · intro τ'
    rw [OG.component_block_matrix, OG.compAt_zero', OG.compAt_one']
    by_cases h : τ' = τ
    · subst h
      rw [h1, hyb, e1]
      rfl
    · rw [h2 τ' h, e2 τ' h, one_eq_block_matrix]

theorem theta_half (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) :
    θ ρ (algebraMap D.host.F (Ainf D.host.F) (1 / 2) ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 / 2 := by
  have h2 : θ ρ (algebraMap D.host.F (Ainf D.host.F) 2 ⊗ₜ[D.host.F] (1 : D.host.E)) = 2 := by
    have : (algebraMap D.host.F (Ainf D.host.F) 2 ⊗ₜ[D.host.F] (1 : D.host.E)) = 2 := by
      rw [map_ofNat]
      rfl
    rw [this, map_ofNat]
  have hm : θ ρ (algebraMap D.host.F (Ainf D.host.F) (1 / 2) ⊗ₜ[D.host.F] (1 : D.host.E)) *
      θ ρ (algebraMap D.host.F (Ainf D.host.F) 2 ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, mul_one]
    norm_num
    rw [← Algebra.TensorProduct.one_def, map_one]
  rw [h2] at hm
  field_simp
  linear_combination hm

theorem gramX_eq {m n : ℕ} (ε : Fin m → Bool) (u : Matrix (Fin m) (Fin n) ℂ) :
    gramX ε u = uᴴ * Matrix.diagonal (sgn ε) * u := by
  ext i j
  simp only [gramX, evX, Qp, Qb, map_sub, map_sum, map_mul, MvPolynomial.eval_X, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.conjTranspose_apply, if_true, Bool.false_eq_true, if_false]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun k _ hk => by rw [if_neg hk, mul_zero]) (by simp), if_pos rfl]
  unfold sgn
  cases ε a <;> simp <;> ring

theorem psi_unip {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) {V : HSp D} {n : ℕ} (τ : D.what₂.Tau) (ε : Fin V.rank → Bool)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hfr : IsUnit fr.det)
    (hG : frᴴ * gramAt D V τ * fr = Matrix.diagonal (sgn ε)) (B : Mx D n n) (b : Matrix (Fin n) (Fin n) ℂ)
    (hb : bᴴ = b) (h1 : compAt θ τ B = b) (h2 : ∀ τ', τ' ≠ τ → compAt θ τ' B = 0) (h3 : B.map (finPart D) = 0)
    (x : Mx D V.rank n) :
    ψ (halfTr (Matrix.trace (HMul.hMul B (GlobalTheory.StdUnn.inner V x x) : Mx D n n))) =
      Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε (fr⁻¹ * compAt θ τ x)).trace) := by
  set z : AE D := Matrix.trace (HMul.hMul B (GlobalTheory.StdUnn.inner V x x) : Mx D n n) with hz
  have hcomp : ∀ τ', θ τ' (infPart D z) = Matrix.trace (compAt θ τ' B * ((compAt θ τ' x)ᴴ * (gramAt D V τ' * compAt θ τ' x))) := by
    intro τ'
    have e : θ τ' (infPart D z) = ((θ τ').comp (infPart D)) z := rfl
    rw [e, hz, AddMonoidHom.map_trace]
    show Matrix.trace (compAt θ τ' (HMul.hMul B (GlobalTheory.StdUnn.inner V x x) : Mx D n n)) = _
    rw [GlobalTheory.CompanionTheory.WSum.compAt_mul', GlobalTheory.StdUnn.inner, GlobalTheory.CompanionTheory.WSum.compAt_mul', GlobalTheory.CompanionTheory.WSum.compAt_adj hθ, GlobalTheory.CompanionTheory.WSum.compAt_mul', gA,
      GlobalTheory.CompanionTheory.WSum.compAt_rat hθ]
    rfl
  have hzf : finPart D z = 0 := by
    rw [hz, AddMonoidHom.map_trace, Matrix.map_mul, h3, Matrix.zero_mul, Matrix.trace_zero]
  have hT := GlobalTheory.PhaseReal.trace_real hzf
  have hh : halfTr z = pairA D.host.F (algebraMap D.host.F (Ainf D.host.F) (1 / 2) *
      fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) z)) 0 := by
    unfold halfTr trA
    rw [hT]
    refine Prod.ext ?_ ?_
    · show (algebraMap D.host.F (AF D.host.F) (1 / 2)).1 * _ = _
      rfl
    · show (algebraMap D.host.F (AF D.host.F) (1 / 2)).2 * 0 = 0
      exact mul_zero _
  rw [hh, show ψ (pairA D.host.F _ 0) = psiInf D.host.F ψ _ from rfl, hl]
  have hterm : ∀ τ', θ τ' ((algebraMap D.host.F (Ainf D.host.F) (1 / 2) *
      fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) z)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      (((θ τ' (infPart D z)).re : ℝ) : ℂ) := by
    intro τ'
    rw [show ((algebraMap D.host.F (Ainf D.host.F) (1 / 2) * fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) z)) ⊗ₜ[D.host.F]
        (1 : D.host.E)) = (algebraMap D.host.F (Ainf D.host.F) (1 / 2) ⊗ₜ[D.host.F] (1 : D.host.E)) *
        (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) ⊗ₜ[D.host.F] (1 : D.host.E)) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one], map_mul, theta_half θ hθ, GlobalTheory.PhaseReal.theta_trace θ hθ]
    push_cast
    ring
  simp only [hterm]
  rw [Finset.sum_eq_single τ]
  · have hc : compAt θ τ x = fr * (fr⁻¹ * compAt θ τ x) := (Matrix.mul_nonsing_inv_cancel_left _ _ hfr).symm
    have hq : compAt θ τ B * ((compAt θ τ x)ᴴ * (gramAt D V τ * compAt θ τ x)) =
        b * gramX ε (fr⁻¹ * compAt θ τ x) := by
      rw [h1, gramX_eq]
      conv_lhs => rw [hc]
      rw [Matrix.conjTranspose_mul, ← hG]
      simp only [Matrix.mul_assoc]
    rw [hcomp τ, hq]
    set T : ℂ := (b * gramX ε (fr⁻¹ * compAt θ τ x)).trace with hTdef
    have hr : ((T.re : ℝ) : ℂ) = T := OpGenAH.trace_real ε b hb _
    rw [hr]
    congr 1
    unfold tLoc
    push_cast
    ring
  · intro τ' _ hne
    rw [hcomp τ', h2 τ' hne, Matrix.zero_mul, Matrix.trace_zero]
    simp
  · intro h
    exact absurd (Finset.mem_univ τ) h

end PositivityTheory.Rg.Sw.Glob.UnipH

namespace PositivityTheory.Rg.Sw.Glob

theorem unipTau : UnipTau := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y b hb hyb Φ x
  obtain ⟨hm, h1, h2, h3⟩ := UnipH.mat_iota_nU hC.hθ hC.hι y b hyb
  rw [hC.hω.unip (ι y) _ hm Φ x]
  congr 1
  exact UnipH.psi_unip hC.hθ hC.hl τ ε fr hC.hfr.1 hC.hfr.2.1 _ b hb h1 h2 h3 x

end PositivityTheory.Rg.Sw.Glob
