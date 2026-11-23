import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.ProjInf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem crd_eq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : GL (Fin d.n) (AE F E)) (η : E)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star)
    (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1)
    (w : InfinitePlace F) (X : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    Gen.crd (θ w) (fr w) (g w) (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) = R.loc w (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) := by
  set c : ℂ := ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcdef
  have hm : Nonempty (Fin d.m) := ⟨⟨0, d.ok.hm⟩⟩
  have hc : c ≠ 0 := by
    intro h0
    have h1 := frc w
    rw [← hcdef, h0, zero_smul] at h1
    have h2 : ((fr w)⁻¹).1 * (fr w).1 = 1 := Units.inv_mul (fr w)
    rw [h1, Matrix.mul_zero] at h2
    exact zero_ne_one h2
  have hfr : ((fr w)⁻¹).1 = c⁻¹ • (((R.fr w)⁻¹).1).map star := by
    refine Units.inv_eq_of_mul_eq_one_left ?_
    rw [frc w, ← hcdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, ← map_star_mul,
      Units.inv_mul]
    exact Matrix.map_one _ (star_zero _) (star_one _)
  have hN : ((d.cw w u.1)ᵀ).map star * ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star = 1 := by
    rw [← map_star_mul, ← Matrix.transpose_mul]
    have : d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1 * d.cw w u.1 = 1 := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
      rw [← Matrix.map_mul (f := piInf (d.B.emb w)), Units.inv_mul]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, Matrix.transpose_one]
    exact Matrix.map_one _ (star_zero _) (star_one _)
  have hg : (g w).1 = c • ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star := by
    calc (g w).1 = (g w).1 * (((d.cw w u.1)ᵀ).map star * ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star) := by
          rw [hN, Matrix.mul_one]
      _ = c • ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star := by
          rw [← Matrix.mul_assoc, gc w, ← hcdef, Matrix.smul_mul, Matrix.one_mul]
  have hX : Matrix.of (fun a j => θ w (HeckeCharacterZeroLocus.SiegelWeilU.projInf X j a)) = (d.cw w (toMx X)).map star := by
    ext a j
    simp only [Matrix.of_apply, HeckeCharacterZeroLocus.SiegelWeilU.projInf, th, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, toMx]
  have hZ : d.cw w (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) =
      d.cw w (toMx X) * (d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
    rw [Matrix.map_mul (f := piInf (d.B.emb w)), Matrix.transpose_map]
  unfold Gen.crd _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [hfr, hX, hg, hZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc, one_smul,
    map_star_mul, map_star_mul, Matrix.mul_assoc]
end PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB
end
end
