import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorSchroedingerImageAtLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaHalfSpaceDatumTranslateDisjointSupportStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerImagesOrthogonalDisjointSplitSupportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace

noncomputable section

namespace GlobalTheory.BadPlace

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem actO_one_inv_half {D : D7} {S T : HSp D} {e f : AE D} (hef : e * f = e) {γ : GA D T}
    (hγ : GlobalTheory.RawLift.TrivAt T f γ) {y : WO S T} (hy : IsHalf e y) : actO S T 1 γ⁻¹ y = y := by
  have h1 : f • Formalism.L2.Theta.mt T γ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    ext a b
    have := hγ a b
    rw [Matrix.sub_apply, mul_sub] at this
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    exact sub_eq_zero.1 this
  have h2 : Formalism.L2.Theta.mt T γ * Formalism.L2.Theta.mt T γ⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h3 : f • Formalism.L2.Theta.mt T γ⁻¹ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    calc f • Formalism.L2.Theta.mt T γ⁻¹ = (f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) * Formalism.L2.Theta.mt T γ⁻¹ := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (f • Formalism.L2.Theta.mt T γ) * Formalism.L2.Theta.mt T γ⁻¹ := by rw [h1]
      _ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by rw [Matrix.smul_mul, h2]
  have h4 : e • Formalism.L2.Theta.mt T γ⁻¹ = e • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    rw [← hef, ← smul_smul, h3, smul_smul]
  have hy' : e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = y := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hy a b
  have hone : Formalism.L2.Theta.mt S (1 : GA D S)⁻¹ = 1 := by
    simp only [inv_one, Formalism.L2.Theta.mt, map_one, Units.val_one]
  unfold actO
  rw [hone, Matrix.mul_one]
  calc HMul.hMul (Formalism.L2.Theta.mt T γ⁻¹) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      = HMul.hMul (Formalism.L2.Theta.mt T γ⁻¹) (e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by rw [hy']
    _ = HMul.hMul (e • Formalism.L2.Theta.mt T γ⁻¹) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = HMul.hMul (e • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
        rw [h4]
    _ = y := by rw [Matrix.smul_mul, Matrix.one_mul, hy']

theorem pureTensorL_one {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : pureTensorL A f 1 = f := by
  have e : (1 : MvPolynomial ι ℂ) = MvPolynomial.basisMonomials ι ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]; rfl
  rw [e]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]
  simp [opPow]

set_option maxHeartbeats 2000000 in

theorem coef_bad_vanish : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hC P hP e f hPI γ _ hTr k hk hlev
  obtain ⟨ea, Tm, c, hIS, hSe, hee, hf, hψ, hSV, hSW, hv0, hvl, hTm, hSB2, hSB1, hvP, hωk⟩ :=
    GlobalTheory.T.thetaLiftVector_schroedingerImage_at_levelPrime D G Pl0 T A Ks R F hL hF i t P hP e f hPI k hk
  have hdisj := GlobalTheory.T.thetaHalfSpaceDatum_translate_disjoint_support D G Pl0 T A Ks R F hL hF i t ea hIS P hP e f hPI k hk hlev
  have hW := (hF i t).datum
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [RealDat.ptP, pureTensorO, pureTensorL_one] at this
  have hef : e * f = e := by
    rw [hf, mul_add, hSe.1, hSe.2.1, add_zero]
  have e1 := GlobalTheory.WeilPairing.thetaInner_weilRep D R.ψ _ _ _ _ (R.ωP i t) μ 𝓕 hW hC (1, γ⁻¹)
    (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) (hW.om_pres (1, γ * k) _ hth) hth
  rw [← e1, ← Module.End.mul_apply, ← map_mul]
  have e2 : ((1 : GA D (Vc D i)), γ⁻¹) * (1, γ * k) = (1, k) := by
    ext
    · exact mul_one 1
    · exact (inv_mul_cancel_left γ k)
  rw [e2, hωk, thetaInner_smul_left]
  have hz := GlobalTheory.T.schrodingerImages_orthogonal_disjoint_splitSupport D R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) _ ea e (R.vacP i) Tm μ 𝓕 hψ hSV hSW hIS hSe hee hv0 hvl
    hTm hC _ _ hSB1 hSB2 (fun x x' hxx' h1 h2 => hdisj x x' (by rw [hf]; exact hxx') h1 h2) (R.ωP i t (1, γ⁻¹))
    (fun g hg => hW.om_pres _ _ hg) (fun y hy g hg => by
      rw [hW.om_heis _ _ _ _ hg, actO_one_inv_half hef hTr hy])
  rw [← hvP] at hz
  rw [hz, mul_zero]

end GlobalTheory.BadPlace

end
