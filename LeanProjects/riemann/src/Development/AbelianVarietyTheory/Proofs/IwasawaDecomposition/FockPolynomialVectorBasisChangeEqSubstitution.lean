import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.CompactHowe Matrix Complex
open scoped TensorProduct Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockBaseChange

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockIndep

theorem cplxO_one {m n : ℕ} (z : Matrix (Fin m) (Fin n) ℂ) : cplxO 1 1 z = I • z := by
  rw [cplxO, Matrix.one_mul, Matrix.mul_one]

theorem unitMap_mul {m n : ℕ} (B g : Matrix (Fin n) (Fin n) ℂ) (B' h : Matrix (Fin m) (Fin m) ℂ) (i : Fin m)
    (j : Fin n) : unitMap (B * g) (B' * h) i j = ∑ k, ∑ l, (h k i * g⁻¹ j l) • unitMap B B' k l := by
  have e : h * Matrix.single i j (1 : ℂ) * g⁻¹ = ∑ k, ∑ l, (h k i * g⁻¹ j l) • Matrix.single k l (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (h * Matrix.single i j (1 : ℂ) * g⁻¹)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j (fun b _ hb => by rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul])
      (by simp), Matrix.mul_single_apply_same, mul_one]
  unfold unitMap
  rw [Matrix.mul_inv_rev]
  calc B' * h * Matrix.single i j (1 : ℂ) * (g⁻¹ * B⁻¹) = B' * (h * Matrix.single i j (1 : ℂ) * g⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by simp only [e, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem omDir_I (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ' : D.what₂.Tau)
    (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omDir S T τ (cplxO 1 1 z) τ' (cplxO 1 1 z') = omDir S T τ z τ' z' ∧
    omDir S T τ z τ' (cplxO 1 1 z') = -omDir S T τ (cplxO 1 1 z) τ' z' := by
  unfold omDir
  split_ifs with h
  · simp only [cplxO_one, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      RCLike.star_def, conj_I]
    constructor
    · congr 3
      rw [← mul_assoc]; simp
    · simp only [neg_mul, mul_neg, Complex.neg_re]
  · simp

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
include hψ hθ

theorem dRho_dir_add (τ : D.what₂.Tau) (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dRho (heisO ψ S T) θ τ (z + z') f = dRho (heisO ψ S T) θ τ z f + dRho (heisO ψ S T) θ τ z' f := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ z g, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ z 1)) g := fun z g =>
    dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  have hs := theta_sm h hf
  have e : piW θ T S (lineAt θ τ (z + z') 1) = piW θ T S (lineAt θ τ z 1) + piW θ T S (lineAt θ τ z' 1) := by
    rw [piW_lineAt hθ, piW_lineAt hθ, piW_lineAt hθ, Pi.single_add]
    rfl
  funext w
  rw [Pi.add_apply, hE, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
    LinearMap.map_add, ContinuousLinearMap.map_add]
  push_cast
  ring

theorem dRho_dir_smul (τ : D.what₂.Tau) (t : ℝ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dRho (heisO ψ S T) θ τ ((t : ℂ) • z) f = (t : ℂ) • dRho (heisO ψ S T) θ τ z f := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ z g, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ z 1)) g := fun z g =>
    dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  have hs := theta_sm h hf
  have e : piW θ T S (lineAt θ τ ((t : ℂ) • z) 1) = t • piW θ T S (lineAt θ τ z 1) := by
    rw [piW_lineAt hθ, piW_lineAt hθ, Pi.single_smul]
    rfl
  funext w
  rw [Pi.smul_apply, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
    LinearMap.map_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem aPlus_dir_add (τ : D.what₂.Tau) (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO 1 1) (z + z') f =
      aPlus (heisO ψ S T) θ τ (cplxO 1 1) z f + aPlus (heisO ψ S T) θ τ (cplxO 1 1) z' f := by
  simp only [aPlus_eq, cplxO_one, smul_add, fun z z' => dRho_dir_add hψ hθ τ z z' hf]
  module

theorem aPlus_dir_smul (τ : D.what₂.Tau) (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO 1 1) (c • z) f = c • aPlus (heisO ψ S T) θ τ (cplxO 1 1) z f := by
  have e1 : c • z = (c.re : ℂ) • z + (c.im : ℂ) • (I • z) := by
    rw [smul_smul, ← add_smul, re_add_im]
  have e2 : I • c • z = ((-c.im : ℝ) : ℂ) • z + (c.re : ℂ) • (I • z) := by
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    apply Complex.ext <;> simp
  simp only [aPlus_eq, cplxO_one]
  rw [e2, e1, dRho_dir_add hψ hθ τ _ _ hf, dRho_dir_add hψ hθ τ _ _ hf, dRho_dir_smul hψ hθ τ _ _ hf,
    dRho_dir_smul hψ hθ τ _ _ hf, dRho_dir_smul hψ hθ τ _ _ hf, dRho_dir_smul hψ hθ τ _ _ hf]
  generalize ((fockScale D τ : ℂ)⁻¹) = a
  match_scalars
  · linear_combination a * re_add_im c
  · linear_combination (-I) * a * re_add_im c + a * (c.im : ℂ) * I_mul_I

theorem aPlus_dir_sum {ι : Type} (τ : D.what₂.Tau) (s : Finset ι) (z : ι → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO 1 1) (∑ i ∈ s, z i) f = ∑ i ∈ s, aPlus (heisO ψ S T) θ τ (cplxO 1 1) (z i) f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := aPlus_dir_smul hψ hθ τ 0 0 hf
    rwa [zero_smul, zero_smul] at this
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, aPlus_dir_add hψ hθ τ _ _ hf, ih]

theorem aPlus_comm_one (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ' : D.what₂.Tau)
    (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO 1 1) z (aPlus (heisO ψ S T) θ τ' (cplxO 1 1) z' f) =
    aPlus (heisO ψ S T) θ τ' (cplxO 1 1) z' (aPlus (heisO ψ S T) θ τ (cplxO 1 1) z f) := by
  have ht := fun τ z => theta_dRho hθ hψ τ z hf
  have hc := fun τ z τ' z' => dRho_comm hψ hθ τ z τ' z' hf
  obtain ⟨h1, h2⟩ := omDir_I τ z τ' z'
  rw [aPlus_eq τ' _ z' f, aPlus_eq τ _ z f, aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)), aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    aPlus_smul hψ hθ _ _ _ _ (ht _ _), aPlus_smul hψ hθ _ _ _ _ (ht _ _)]
  simp only [aPlus_eq]
  rw [hc τ z τ' z', hc τ z τ' (cplxO 1 1 z'), hc τ (cplxO 1 1 z) τ' z', hc τ (cplxO 1 1 z) τ' (cplxO 1 1 z')]
  rw [h1, h2]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [I_pow_three]; ring1)

theorem pureTensorO_X_mul (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) (v : FVar D T.rank S.rank) :
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (MvPolynomial.X v * Q) =
      aPlus (heisO ψ S T) θ v.1 (cplxO 1 1) (unitMap (BS v.1) (BT v.1) v.2.1 v.2.2)
        (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f Q) := by
  unfold pureTensorO
  exact pure_X_mul (A := aPlusAll (heisO ψ S T) θ (fun _ => cplxO 1 1) BS BT) (P := IsThetaFunO ψ S T)
    (fun _ _ => theta_add) (fun a _ => theta_smul a)
    (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) (fun i j _ h => aPlus_comm_one hψ hθ i.1 _ j.1 _ h)
    (fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h') (fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h) hf Q v

omit hψ hθ in

theorem pureTensorO_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BS g : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT h : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun τ => BS τ * g τ) (fun τ => BT τ * h τ) f P = pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (substF h (fun τ => ((g τ)⁻¹)ᵀ) P) := by
  intro D ψ θ S T hψ hθ BS g BT h f hf P
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [← mul_one (MvPolynomial.C a), MvPolynomial.C_mul', map_smul, map_smul, map_smul, map_one (substF _ _)]
    unfold pureTensorO
    rw [pure_one, pure_one]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    have hm : IsThetaFunO ψ S T
        (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (substF h (fun τ => ((g τ)⁻¹)ᵀ) p)) :=
      pure_mem (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
        (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) hf _
    rw [mul_comm, pureTensorO_X_mul hψ hθ _ _ hf, hp, map_mul, substF_X, unitMap_mul, aPlus_dir_sum hψ hθ _ _ _ hm,
      Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [aPlus_dir_sum hψ hθ _ _ _ hm, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [aPlus_dir_smul hψ hθ _ _ _ hm, mul_assoc, MvPolynomial.C_mul', map_smul, pureTensorO_X_mul hψ hθ _ _ hf]
    rfl

end GlobalTheory.FockBaseChange
