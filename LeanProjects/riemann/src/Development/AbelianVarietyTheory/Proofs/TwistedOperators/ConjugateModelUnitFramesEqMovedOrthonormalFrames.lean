import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdSpan.ConjHol
variable {D : D7} {S T : HSp D}

theorem gram_conj_emb (C : Ctx S T) (hH : ∀ τ, (gramAt D T τ)ᴴ = gramAt D T τ) (ρ : D.what₂.Tau)
    (M : Matrix (Fin T.rank) (Fin T.rank) ℂ) :
    FD.gram (C.m.e ρ).1 C.X.Gm (M.map (starRingEnd ℂ)) = Mᴴ * gramAt D T ρ * M := by
  ext a b
  have hh : ∀ i k, conj (gramAt D T ρ k i) = gramAt D T ρ i k := fun i k => by
    have := congrFun (congrFun (hH ρ) i) k
    rwa [Matrix.conjTranspose_apply] at this
  simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.map_apply, C.m.e_emb, C.m.gT, Matrix.transpose_apply,
    NumberField.ComplexEmbedding.conjugate_coe_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [gramAt, Matrix.map_apply] at hh ⊢
  simp only [Complex.conj_conj, hh, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]

end GlobalTheory.AdSpan.ConjHol

namespace GlobalTheory.AdSpan.ConjHol

theorem unitFr_conj_moved : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → (∀ a, GlobalTheory.HolRead.IsUnitFr C.X (C.xB (C.mvB a B))) ∧ (∀ y, GlobalTheory.HolRead.IsUnitFr C.X y → ∃ a ∈ GinfC T, C.xB (C.mvB a B) = y) ∧ (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, C.xB (C.mvB a B) = C.xB (C.mvB a' B) → a = a') := by
  intro D S T C B hB
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  have hT := GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C
  have hH : ∀ τ, (gramAt D T τ)ᴴ = gramAt D T τ := fun τ => (R.1 τ).1
  refine ⟨fun a => ?_, fun y hy => ?_, fun a ha a' ha' h => ?_⟩
  · exact (hT.2 _ ((hT.2 B hB).2.2.2.2.2 a).1).1
  · let Y : C.Bas := fun ρ => (FD.mat y (C.m.e ρ)).map (starRingEnd ℂ)
    have hY : ∀ ρ, (Y ρ)ᴴ * gramAt D T ρ * Y ρ = sgnM C.X := by
      intro ρ
      rw [← gram_conj_emb C hH ρ]
      have e : (Y ρ).map (starRingEnd ℂ) = FD.mat y (C.m.e ρ) := by
        ext i j; simp [Y]
      rw [e]
      exact hy (C.m.e ρ)
    have hu : ∀ ρ, Y ρ * (B ρ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := by
      intro ρ
      have hd := isUnit_det_B C hB ρ
      have hd' : IsUnit (B ρ)ᴴ.det := by rw [det_conjTranspose]; exact hd.star
      show (Y ρ * (B ρ)⁻¹)ᴴ * gramAt D T ρ * (Y ρ * (B ρ)⁻¹) = gramAt D T ρ
      have e1 : (Y ρ * (B ρ)⁻¹)ᴴ * gramAt D T ρ * (Y ρ * (B ρ)⁻¹) =
          ((B ρ)⁻¹)ᴴ * ((Y ρ)ᴴ * gramAt D T ρ * Y ρ) * (B ρ)⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [e1, hY, ← hB ρ, conjTranspose_nonsing_inv]
      simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hd', Matrix.one_mul]
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
    obtain ⟨a, ha, hau⟩ := R.2.1 (fun ρ => Y ρ * (B ρ)⁻¹) hu
    refine ⟨a, ha, ?_⟩
    have hm : ∀ ρ, C.mvB a B ρ = Y ρ := by
      intro ρ
      simp only [Ctx.mvB]
      rw [show compAt C.θ ρ (mt T a) = Y ρ * (B ρ)⁻¹ from hau ρ, Matrix.mul_assoc,
        nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.mul_one]
    funext σ i j
    obtain ⟨ρ, rfl⟩ := C.m.e.surjective σ
    simp only [Ctx.xB, Equiv.symm_apply_apply, hm, Y, Matrix.map_apply, Complex.conj_conj, FD.mat, Matrix.of_apply]
  · have hm : ∀ ρ, C.mvB a B ρ = C.mvB a' B ρ := by
      intro ρ
      ext i j
      have := congrFun (congrFun (congrFun h (C.m.e ρ)) i) j
      simp only [Ctx.xB, Equiv.symm_apply_apply] at this
      simpa using congrArg (starRingEnd ℂ) this
    refine R.2.2.1 a ha a' ha' fun ρ => ?_
    have e := congrArg (· * (B ρ)⁻¹) (hm ρ)
    simp only [Ctx.mvB, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_det_B C hB ρ), Matrix.mul_one] at e
    exact e

end GlobalTheory.AdSpan.ConjHol
