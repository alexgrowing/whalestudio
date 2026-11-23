import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormRationality
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockPolyInj

open GlobalTheory.FockVecInj GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7}

theorem pureTensorO_injective_of_on (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sV BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (s BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (pV pW : D.what₂.Tau → ℕ)
    (hBV : ∀ τ, IsONBasis (gramAt D V τ) (sV τ) (BV τ) (pV τ))
    (hBW : ∀ τ, IsONBasis (gramAt D W τ) (s τ) (BW τ) (pW τ)) (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f)
    (hvac : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sV τ) (s τ)) f) (hf0 : f ≠ 0) :
    Function.Injective (pureTensorO ψ θ V W sV s BV BW f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  choose ε hε hG hs using hBV
  choose ε' hε' hG' hs' using hBW
  have sq : ∀ τ a, (ε τ a : ℂ) * ε τ a = 1 := fun τ a => by
    rcases hε τ a with h | h <;> simp [h.1]
  have sq' : ∀ τ a, (ε' τ a : ℂ) * ε' τ a = 1 := fun τ a => by
    rcases hε' τ a with h | h <;> simp [h.1]
  have hdet : ∀ τ, IsUnit (BV τ).det := fun τ => by
    have e : (diagonal (fun a => (ε τ a : ℂ)) * ((BV τ)ᴴ * gramAt D V τ)) * BV τ = 1 := by
      rw [Matrix.mul_assoc, hG, Matrix.diagonal_mul_diagonal]
      simp only [sq, Matrix.diagonal_one]
    exact Matrix.isUnit_det_of_left_inverse e
  have hE : ∀ τ z g, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g = hD (iotaW σ W V) (piW θ W V) (omO V W)
      (Pi.single τ z : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) g := fun τ z g => by
    rw [← pi_lineAt hθ]
    exact dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  let M : Submodule ℂ (WO V W → ℂ) :=
    { carrier := {g | Sm (iotaW σ W V) g}
      add_mem' := fun ha hb w => (ha w).add (hb w)
      zero_mem' := fun w => contDiff_const
      smul_mem' := fun c g hg w => contDiff_const.mul (hg w) }
  have hform := fun g hg u w => hD_eq_fderiv (iotaW σ W V) (piW θ W V) (omO V W) g hg u w
  obtain ⟨Dop, hD1, -⟩ := exists_heisenberg_operators _ _ (iotaW σ W V) (piW θ W V) (omO V W) (h.pi_iota W V) hform M
    (fun _ hg => hg) fun u g hg => (hD_formula_smooth _ _ _ _ _ (h.pi_iota W V) g hg u).2
  have sk : ∀ u v, omO V W v u = -omO V W u v := fun u v => by
    have h1 := omO_self h (S := V) (T := W) (u + v)
    simp only [LinearMap.map_add, LinearMap.add_apply, omO_self h] at h1
    linarith
  have hcomm : ∀ u v g, Dop u (Dop v g) = Dop v (Dop u g) + (-(2 * Real.pi * I) * (omO V W u v : ℝ)) • g :=
    fun u v g => by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, hD1, hD1, hD1, hD1]
    exact eq_add_of_sub_eq' (heisenberg_derivative_commutator _ _ _ _ _ (h.pi_iota W V) hform sk g g.2 u v)
  let η : FVar D W.rank V.rank → ℝ := fun k => ε' k.1 k.2.1 * ε k.1 k.2.2
  have hη : ∀ k, η k = 1 ∨ η k = -1 := fun k => by
    rcases hε k.1 k.2.2 with h | h <;> rcases hε' k.1 k.2.1 with h' | h' <;> simp [η, h.1, h'.1]
  let u : ℂ → FVar D W.rank V.rank → RW W V := fun c k =>
    (Pi.single k.1 (c • unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ)
  have hom : ∀ c c' k l, omO V W (u c k) (u c' l) =
      if k = l then 2 * (tauE D k.1 D.host.xi0 * (c * conj c' * η k)).re else 0 := by
    rintro c c' ⟨τ, i, j⟩ ⟨τ', k, l⟩
    refine (omO_single V W τ τ' _ _).trans ?_
    by_cases hτ : τ = τ'
    · subst hτ
      rw [if_pos rfl, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.trace_smul, Matrix.trace_smul, trace_unitMap (sq τ) (hG τ) (hG' τ)]
      by_cases hk : i = k ∧ j = l
      · rw [if_pos hk, if_pos (by rw [hk.1, hk.2])]
        simp only [η, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
        rfl
      · rw [if_neg hk, if_neg (by simpa using hk)]
        simp
    · rw [if_neg hτ, if_neg fun hh => hτ (congrArg Prod.fst hh)]
  have hJ : ∀ k : FVar D W.rank V.rank, cplxO (sV k.1) (s k.1) (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) =
      (I * η k) • unitMap (BV k.1) (BW k.1) k.2.1 k.2.2 := fun k => by
    rw [cplxO_unitMap (hdet _) (hs _) (hs' _)]
    simp only [η, Complex.ofReal_mul]
  have h1 : ∀ k : FVar D W.rank V.rank, u 1 k = (Pi.single k.1 (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) :
      D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) := fun k => congrArg (Pi.single k.1) (one_smul _ _)
  have hξ : ∀ τ, tauE D τ D.host.xi0 ≠ 0 := fun τ => (_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hre := fun τ => GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero (D := D) τ
  have him : ∀ τ, (tauE D τ D.host.xi0).im ≠ 0 := fun τ hh => hξ τ (Complex.ext (hre τ) hh)
  have hsc : ∀ τ, (fockScale D τ : ℂ) ≠ 0 := fun τ => by
    have := norm_pos_iff.2 (hξ τ)
    have h2 : 0 < fockScale D τ := by unfold fockScale; positivity
    exact Complex.ofReal_ne_zero.2 h2.ne'
  refine injective_of_canonicalCommutation M _ (fun k => (fockScale D k.1 : ℂ)⁻¹ • (Dop (u 1 k) - I • Dop (u (I * η k) k)))
    (fun k => Dop (u 1 k) + I • Dop (u (I * η k) k))
    (fun k => (fockScale D k.1 : ℂ)⁻¹ * (-8 * Real.pi * (tauE D k.1 D.host.xi0).im)) (fun k g => ?_) (fun k l g => ?_)
    (fun k l g => ?_) (fun k => ?_) ⟨f, theta_sm h hf⟩ (fun k => ?_) (fun hh => hf0 (congrArg Subtype.val hh))
  · simp only [aPlusAll, aPlus, crea, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
      hD1, hE, hJ]
    rw [h1]
  · rw [(ccr_of_comm Dop _ hcomm _ _ _ _ _ _ g).1]
    refine add_eq_left.2 (smul_eq_zero.2 (Or.inl ?_))
    simp only [hom]
    split_ifs with hh
    · subst hh
      rcases hη k with e | e <;> simp [e, hre]
    · simp
  · rw [(ccr_of_comm Dop _ hcomm _ _ _ _ 0 _ g).2]
    refine congrArg (fun c : ℂ => _ + c • g) ?_
    by_cases hh : k = l
    · subst hh
      simp only [hom, if_true]
      refine congrArg _ ?_
      rcases hη k with e | e <;> simp [e, hre] <;> ring_nf <;> simp only [I_sq] <;> ring1
    · simp [hom, hh]
  · exact mul_ne_zero (inv_ne_zero (hsc _)) (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) (Complex.ofReal_ne_zero.2 (him _)))
  · apply Subtype.ext
    have := hvac k.1 (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2)
    simp only [annih, hE, hJ] at this
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, hD1]
    rw [h1]
    exact this

theorem isONBasis_one {V : HSp D} (hV : V.gram = 1) (τ : D.what₂.Tau) :
    IsONBasis (gramAt D V τ) 1 1 V.rank := by
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.isLt⟩, ?_, ?_⟩ <;>
    simp [hg, Matrix.diagonal_one]

theorem fvec_injective : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → f ≠ 0 → Function.Injective (C.fvec B f) := by
  intro D S T C B hB f hf hvac hf0
  have hT := ((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.1
  exact pureTensorO_injective_of_on C.ψ C.θ S T C.std C.inf (fun _ => 1) (fun _ => 1) (C.sB B) B
    (fun _ => S.rank) (fun _ => C.X.p0) (isONBasis_one C.m.gS) (fun τ => (hT τ).2) f hf hvac hf0

end GlobalTheory.FockPolyInj

end
