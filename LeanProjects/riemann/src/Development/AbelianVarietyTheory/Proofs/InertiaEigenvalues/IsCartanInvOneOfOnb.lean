import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift.VecNonzero

theorem thetaInner_self_ne_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : thetaIP μ 𝓕 f f ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨-, c, hc⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hKc f hf.cont h0
    (by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul]))
  have h1 := hc μ 𝓕 hμ.1 hμ.2.1 hμ.2.2
  have e1 : thetaIP μ 𝓕 f f = ((∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    unfold thetaIP
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  intro h
  rw [e1, Complex.ofReal_eq_zero] at h
  simp only [norm_mul, mul_pow] at h1
  rw [integral_const_mul, h, mul_zero] at h1
  exact zero_ne_one h1

end GlobalTheory.RawLift.VecNonzero

namespace GlobalTheory.RawLift

open GlobalTheory.RawLift.VecNonzero

open scoped ComplexOrder in

theorem isCartanInv_one_of_onb {k : ℕ} {Gm B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis Gm 1 B k) : IsCartanInv Gm 1 := by
  obtain ⟨ε, hε, hG, -⟩ := h
  have e1 : ∀ a, (ε a : ℂ) = 1 := fun a => by
    rcases hε a with h | h
    · simp [h.1]
    · exact absurd a.2 (not_lt.2 h.2)
  have hB : Bᴴ * Gm * B = 1 := by
    rw [hG]
    simp only [e1, Matrix.diagonal_one]
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have h1 := Matrix.mul_nonsing_inv B hu
  have h2 : Gm = (B⁻¹)ᴴ * B⁻¹ := by
    have h3 : (B⁻¹)ᴴ * (Bᴴ * Gm * B) * B⁻¹ = (B⁻¹)ᴴ * B⁻¹ := by rw [hB, Matrix.mul_one]
    have h4 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    rw [← h3]
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
  refine ⟨Matrix.mul_one _, by simp, ?_⟩
  rw [Matrix.mul_one, h2]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (by
      rw [Matrix.det_nonsing_inv]; exact hu.ringInverse)))

theorem vecNe : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, VecNe R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ
  have hW := hL.thP.ωP i t
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hv0 : R.vP i t ≠ 0 := GlobalTheory.AdTh.VecNe.thPVec_ne_zero
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hL.thP.vP i t)
  refine ⟨thetaInner_self_ne_zero hW.std hth hv0 hμ, ?_⟩
  obtain ⟨-, -, v, w, hv1, -, hio⟩ := hL.thP.ioP i t
  have hvac := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hL.thP.vP i t) hth
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hW.std hL.models.inf (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1)
    (fun τ => isCartanInv_one_of_onb (hL.models.BV i τ)) (GlobalTheory.AdTh.VecFock.isCartanInv_cart _) (hL.models.BV i)
    (fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hL.models.order i τ)) (D.sp.V_sig _) (D.sp.W_sig _) _ hth hvac hv0
  refine ⟨fun ρ => v ρ, w, hv1, ?_⟩
  have hj : jointVec R i t (fun ρ => v ρ) w = R.ptP i t (RealDat.Delta i) := by
    unfold jointVec
    rw [hio]
  rw [hj]
  refine thetaInner_self_ne_zero hW.std (hL.thP.pt_theta i t _) (fun h => ?_) hμ
  refine GlobalTheory.AdTh.IoExtPf.Delta_ne i (hinj ?_)
  exact h.trans (map_zero (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) (R.vP i t))).symm

end GlobalTheory.RawLift

end
