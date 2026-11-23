import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.DerFock

open Complex GlobalTheory.FockIndep GlobalTheory.OrientedHeis
open scoped Real

section Mat

variable {m n : ℕ}

theorem Jm_mul_Jm (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> simp

theorem Jm_herm (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp

open scoped ComplexOrder in

theorem isCartanInv_of_isFrameOf {G s fr : Mn n} {ε : Fin n → Bool} (h : IsFrameOf G s ε fr) : IsCartanInv G s := by
  obtain ⟨hu', rfl, rfl⟩ := h
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 hu'
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : fr⁻¹ * fr = 1 := Matrix.nonsing_inv_mul _ hu
  have hG : frᴴ * Formalism.REAL.Jm ε * fr * (fr⁻¹ * Formalism.REAL.Jm ε * fr) = frᴴ * fr := by
    calc _ = frᴴ * (Formalism.REAL.Jm ε * (fr * fr⁻¹) * Formalism.REAL.Jm ε) * fr := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, Jm_mul_Jm, Matrix.mul_one]
  have hs : fr⁻¹ * Formalism.REAL.Jm ε * fr * (fr⁻¹ * Formalism.REAL.Jm ε * fr) = 1 := by
    calc _ = fr⁻¹ * (Formalism.REAL.Jm ε * (fr * fr⁻¹) * Formalism.REAL.Jm ε) * fr := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, Jm_mul_Jm, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (frᴴ * Formalism.REAL.Jm ε * fr)ᴴ = frᴴ * Formalism.REAL.Jm ε * fr := by
      simp [Matrix.conjTranspose_mul, Jm_herm, Matrix.mul_assoc]
    have h3 := congrArg Matrix.conjTranspose hG
    rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul frᴴ fr, Matrix.conjTranspose_conjTranspose] at h3
    rw [h3, ← hG, Matrix.mul_assoc _ (fr⁻¹ * Formalism.REAL.Jm ε * fr), hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 hu')

theorem cplxO_unitMap {G s fr : Mn n} {ε : Fin n → Bool} (h : IsFrameOf G s ε fr) {H t gr : Mn m} {δ : Fin m → Bool}
    (h' : IsFrameOf H t δ gr) (a : Fin m) (b : Fin n) :
    cplxO s t (unitMap fr⁻¹ gr⁻¹ a b) = ((if (δ a == ε b) then 1 else -1 : ℂ) * I) • unitMap fr⁻¹ gr⁻¹ a b := by
  obtain ⟨hu, -, rfl⟩ := h
  obtain ⟨hu', -, rfl⟩ := h'
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : gr * gr⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu')
  have e : Formalism.REAL.Jm δ * single a b (1 : ℂ) * Formalism.REAL.Jm ε =
      (if (δ a == ε b) then 1 else -1 : ℂ) • single a b (1 : ℂ) := by
    ext p q
    rw [Formalism.REAL.Jm, Formalism.REAL.Jm, mul_diagonal, diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases h : a = p ∧ b = q
    · obtain ⟨rfl, rfl⟩ := h
      cases δ a <;> cases ε b <;> simp
    · simp [h]
  unfold cplxO unitMap
  rw [Matrix.nonsing_inv_nonsing_inv _ hd, mul_comm _ I, ← smul_smul]
  congr 1
  calc _ = gr⁻¹ * (Formalism.REAL.Jm δ * (gr * gr⁻¹) * single a b (1 : ℂ) * (fr * fr⁻¹) * Formalism.REAL.Jm ε) * fr := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one, e, Matrix.mul_smul, Matrix.smul_mul]

theorem eq_sum_unitMap {fr : Mn n} {gr : Mn m} (hu : IsUnit fr) (hu' : IsUnit gr) (z : Matrix (Fin m) (Fin n) ℂ) :
    z = ∑ k : Fin m × Fin n, (gr * z * fr⁻¹) k.1 k.2 • unitMap fr⁻¹ gr⁻¹ k.1 k.2 := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h1 : fr⁻¹ * fr = 1 := Matrix.nonsing_inv_mul _ hd
  have h2 : gr⁻¹ * gr = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu')
  have e : gr * z * fr⁻¹ = ∑ k : Fin m × Fin n, (gr * z * fr⁻¹) k.1 k.2 • single k.1 k.2 (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (gr * z * fr⁻¹)]
    rw [Fintype.sum_prod_type]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  unfold unitMap
  rw [Matrix.nonsing_inv_nonsing_inv _ hd]
  calc z = (gr⁻¹ * gr) * z * (fr⁻¹ * fr) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    _ = gr⁻¹ * (gr * z * fr⁻¹) * fr := by simp only [Matrix.mul_assoc]
    _ = _ := by
        conv_lhs => rw [e]
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end Mat

section Generic

variable {ι X : Type} [Fintype ι] {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem pure_deriv {B : (X → ℂ) → (X → ℂ)} {c : ι → ℂ}
    (hadd : ∀ f f', P f → P f' → P (f + f')) (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    (Badd : ∀ f f', P f → P f' → B (f + f') = B f + B f')
    (Bsm : ∀ (a : ℂ) f, P f → B (a • f) = a • B f)
    (hBA : ∀ j f, P f → B (A j f) = A j (B f) + c j • f)
    {f : X → ℂ} (hf : P f) (hv : B f = 0) (Q : MvPolynomial ι ℂ) :
    B (pureTensorL A f Q) = pureTensorL A f (∑ i, c i • MvPolynomial.pderiv i Q) := by
  classical
  have hC : ∀ a, pureTensorL A f (MvPolynomial.C a) = a • f := fun a => by
    rw [← mul_one (MvPolynomial.C a), MvPolynomial.C_mul', map_smul, pure_one]
  have hm := pure_mem hadd hsm hA hf
  have hX := pure_X_mul hadd hsm hA hc Aadd Asm hf
  induction Q using MvPolynomial.induction_on with
  | C a => simp [hC, Bsm _ _ hf, hv]
  | add p q hp hq =>
    rw [map_add, Badd _ _ (hm _) (hm _), hp, hq, ← map_add, ← Finset.sum_add_distrib]
    simp only [map_add, smul_add]
  | mul_X p j hp =>
    rw [mul_comm, hX, hBA _ _ (hm _), hp, ← hX, ← map_smul, ← map_add]
    congr 1
    simp only [MvPolynomial.pderiv_mul, smul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_smul_comm]
    rw [add_comm]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hi), zero_mul, smul_zero]
    · simp

end Generic

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem fockScale_ne_zero (τ : D.what₂.Tau) : (fockScale D τ : ℂ) ≠ 0 := by
  have h1 := xi_zero_im_pos D τ
  have h2 : 0 < ‖tauE D τ D.host.xi0‖ := norm_pos_iff.2 fun h => by rw [h] at h1; simp at h1
  have h3 : 0 < fockScale D τ := by unfold fockScale; positivity
  exact_mod_cast h3.ne'

variable {τ : D.what₂.Tau} {sS : Mn S.rank} {sT : Mn T.rank}
  (hS : IsCartanInv (gramAt D S τ) sS) (hT : IsCartanInv (gramAt D T τ) sT) (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ)
include hS hT

theorem omDir_cplx :
    omDir S T τ (cplxO sS sT z) τ (cplxO sS sT z') = omDir S T τ z τ z' ∧
    omDir S T τ z τ (cplxO sS sT z') = -omDir S T τ (cplxO sS sT z) τ z' := by
  unfold omDir
  simp only [if_true]
  refine ⟨by rw [GlobalTheory.RealSymplForm.tr_J_J hS hT], ?_⟩
  rw [← GlobalTheory.RealSymplForm.tr_J_J hS hT z, GlobalTheory.RealSymplForm.cplxO_cplxO hS.1 hT.1]
  simp
  ring

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
include hψ hθ

theorem aPlus_comm {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO sS sT) z (aPlus (heisO ψ S T) θ τ (cplxO sS sT) z' f) =
    aPlus (heisO ψ S T) θ τ (cplxO sS sT) z' (aPlus (heisO ψ S T) θ τ (cplxO sS sT) z f) := by
  have ht := fun z => theta_dRho hθ hψ τ z hf
  have hc := fun z z' => dRho_comm hψ hθ τ z τ z' hf
  obtain ⟨h1, h2⟩ := omDir_cplx hS hT z z'
  rw [aPlus_eq τ _ z' f, aPlus_eq τ _ z f, aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _) (theta_smul _ (ht _))),
    aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _) (theta_smul _ (ht _))),
    aPlus_add hψ hθ _ _ _ (ht _) (theta_smul _ (ht _)), aPlus_add hψ hθ _ _ _ (ht _) (theta_smul _ (ht _)),
    aPlus_smul hψ hθ _ _ _ _ (ht _), aPlus_smul hψ hθ _ _ _ _ (ht _)]
  simp only [aPlus_eq]
  rw [hc z z', hc z (cplxO sS sT z'), hc (cplxO sS sT z) z', hc (cplxO sS sT z) (cplxO sS sT z')]
  rw [h1, h2]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [I_pow_three]; ring1)

theorem annih_aPlus {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ S T) θ τ (cplxO sS sT) z (aPlus (heisO ψ S T) θ τ (cplxO sS sT) z' f) =
    aPlus (heisO ψ S T) θ τ (cplxO sS sT) z' (annih (heisO ψ S T) θ τ (cplxO sS sT) z f) +
      ((fockScale D τ : ℂ)⁻¹ * (-(4 * π * I) * ((omDir S T τ z τ z' : ℝ) +
        I * (omDir S T τ (cplxO sS sT z) τ z' : ℝ)))) • f := by
  have ht := fun z => theta_dRho hθ hψ τ z hf
  have hc := fun z z' => dRho_comm hψ hθ τ z τ z' hf
  obtain ⟨h1, h2⟩ := omDir_cplx hS hT z z'
  rw [aPlus_eq τ _ z' f, annih_smul hψ hθ _ _ _ _ (theta_add (ht _) (theta_smul _ (ht _))),
    annih_add hψ hθ _ _ _ (ht _) (theta_smul _ (ht _)), annih_smul hψ hθ _ _ _ _ (ht _)]
  conv_rhs => rw [annih, aPlus_add hψ hθ _ _ _ (ht _) (theta_smul _ (ht _)), aPlus_smul hψ hθ _ _ _ _ (ht _)]
  simp only [aPlus_eq, annih]
  rw [hc z z', hc z (cplxO sS sT z'), hc (cplxO sS sT z) z', hc (cplxO sS sT z) (cplxO sS sT z')]
  rw [h1, h2]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [I_pow_three]; ring1)

omit hS hT hψ hθ

theorem exists_dRho_ptAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, ∃ L : Module.End ℂ (LPol T.rank S.rank), ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → ∀ P, dRho (heisO ψ S T) θ τ z (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P) = ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f (L P) := by
  intro D ψ θ S T τ hψ hθ sS frS εS sT frT εT hfS hfT z
  have hS := isCartanInv_of_isFrameOf hfS
  have hT := isCartanInv_of_isFrameOf hfT
  let u : Fin T.rank × Fin S.rank → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun k => unitMap frS⁻¹ frT⁻¹ k.1 k.2
  let A : Fin T.rank × Fin S.rank → (WO S T → ℂ) → (WO S T → ℂ) := fun k =>
    aPlus (heisO ψ S T) θ τ (cplxO sS sT) (u k)
  let α : Fin T.rank × Fin S.rank → ℂ := fun k =>
    if (εT k.1 == εS k.2) then (frT * z * frS⁻¹) k.1 k.2 else starRingEnd ℂ ((frT * z * frS⁻¹) k.1 k.2)
  let c : Fin T.rank × Fin S.rank → ℂ := fun k => (fockScale D τ : ℂ)⁻¹ * (-(4 * π * I) *
    ((omDir S T τ z τ (u k) : ℝ) + I * (omDir S T τ (cplxO sS sT z) τ (u k) : ℝ)))
  refine ⟨(1 / 2 : ℂ) • ((∑ k, c k • (MvPolynomial.pderiv k).toLinearMap) +
    (fockScale D τ : ℂ) • ∑ k, α k • LinearMap.mulLeft ℂ (MvPolynomial.X k)), fun f hf hv P => ?_⟩
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) := fun a _ => theta_smul a
  have hA : ∀ k g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A k g) := fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i j g, IsThetaFunO ψ S T g → A i (A j g) = A j (A i g) :=
    fun _ _ _ h => aPlus_comm hS hT _ _ hψ hθ h
  have Aadd : ∀ i g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → A i (g + g') = A i g + A i g' :=
    fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ S T g → A i (a • g) = a • A i g :=
    fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  have hm := pure_mem hadd hsm hA hf P
  have h1 := pure_deriv (B := annih (heisO ψ S T) θ τ (cplxO sS sT) z) (c := c) hadd hsm hA hc Aadd Asm
    (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
    (fun _ _ h => annih_aPlus hS hT _ _ hψ hθ h) hf (hv z) P
  have h2 : aPlus (heisO ψ S T) θ τ (cplxO sS sT) z (pureTensorL A f P) =
      pureTensorL A f (∑ k, α k • (MvPolynomial.X k * P)) := by
    conv_lhs => rw [eq_sum_unitMap hfS.1 hfT.1 z]
    rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ sS sT hm, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ sS sT hm _ _ (cplxO_unitMap hfS hfT k.1 k.2), map_smul,
      pure_X_mul hadd hsm hA hc Aadd Asm hf]
  have h3 : ∀ g, dRho (heisO ψ S T) θ τ z g = (1 / 2 : ℂ) • (annih (heisO ψ S T) θ τ (cplxO sS sT) z g +
      (fockScale D τ : ℂ) • aPlus (heisO ψ S T) θ τ (cplxO sS sT) z g) := fun g => by
    rw [aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero τ), one_smul, annih, crea]
    module
  change dRho (heisO ψ S T) θ τ z (pureTensorL A f P) = pureTensorL A f _
  rw [h3, h1, h2, ← map_smul, ← map_add, ← map_smul]
  congr 1
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.mulLeft_apply]
  rfl

end GlobalTheory.ArchRec.DerFock
