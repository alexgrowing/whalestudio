import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxOfIsONFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiHalfSymplecticOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CplxOfFrame

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.FockVac

theorem hasDerivAt_translate {n g : ℕ} (c : Fin g → ℝ) (H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ)
    (hH : ∀ z w, H z w = ∑ j, (c j : ℂ) * z j * conj (w j)) (F : (Fin n → Fin g → ℂ) → ℂ) (hF : Differentiable ℂ F)
    (Z A : Fin n → Fin g → ℂ) :
    HasDerivAt (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A)))
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b)) *
        (-(Real.pi * ∑ b, H (A b) (Z b)) * F Z + fderiv ℂ F Z A)) 0 := by
  have hc : ∀ z w, conj (H z w) = H w z := fun z w => by
    simp only [hH, map_sum, map_mul, conj_ofReal, conj_conj]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e : (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A))) =
      fun t : ℝ => (fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) + (-(Real.pi * ∑ b, H (A b) (Z b)) * u +
        -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) t := by
    funext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    have h1 : ∀ b, I * ((H (Z b) (((t : ℂ) • A) b)).im : ℂ) = t * (H (Z b) (A b) - H (A b) (Z b)) / 2 := fun b => by
      have h2 : H (Z b) (((t : ℂ) • A) b) = t * H (Z b) (A b) := by
        simp only [hH, Pi.smul_apply, smul_eq_mul, map_mul, conj_ofReal, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [h2, ← hc (Z b) (A b), Complex.sub_conj, Complex.im_ofReal_mul]
      push_cast
      ring
    have h3 : ∀ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b) =
        H (Z b) (Z b) + t * H (Z b) (A b) + t * H (A b) (Z b) + t ^ 2 * H (A b) (A b) := fun b => by
      simp only [hH, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_add, conj_ofReal, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [Complex.ofReal_sum, mul_assoc, Finset.mul_sum]
    simp only [h1, h3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  rw [e]
  refine HasDerivAt.comp_ofReal (e := fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) +
    (-(Real.pi * ∑ b, H (A b) (Z b)) * u + -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) ?_
  rw [Complex.ofReal_zero]
  have h1 : HasDerivAt (fun u : ℂ => Z + u • A) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const A).const_add Z
  have h2 : HasDerivAt (fun u : ℂ => F (Z + u • A)) (fderiv ℂ F Z A) 0 := by
    have := (hF (Z + (0 : ℂ) • A)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
    rwa [zero_smul, add_zero] at this
  have h3 := ((((hasDerivAt_id (0 : ℂ)).const_mul (-(Real.pi * ∑ b, H (A b) (Z b)))).fun_add
    ((hasDerivAt_pow 2 (0 : ℂ)).const_mul (-(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b))))).const_add
      (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b))).cexp.fun_mul h2
  refine h3.congr_deriv ?_
  simp only [id, zero_smul, add_zero, mul_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Nat.add_one_sub_one, pow_one]
  ring

theorem isFockVacAt_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (s τ)) f := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv f φ hf hR τ z
  obtain ⟨hd, -, hH⟩ := hx_of_isONFr _ r g V.rank X bas idx hs hev x hx0
  obtain ⟨-, hadd, hline, -⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x
  have hJ := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv).2.2 τ z
  have hF := GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hR.1 hd
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real (WeilVacMove.isTheta_add (WeilVacMove.isTheta_dRho hψ hθ τ z hf)
    (WeilVacMove.isTheta_smul I (WeilVacMove.isTheta_dRho hψ hθ τ _ hf))) fun w hw => ?_
  have hw' : w.map (finPart D) = 0 := hw
  have key : ∀ u, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ u f w =
      cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ u 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ u 1))) := fun u => by
    rw [← (hasDerivAt_translate _ _ hH _ hF _ _).deriv]
    unfold Formalism.IndefR.Datum.dRho
    congr 1
    funext t
    have h0 : (w + lineAt θ τ u t).map (finPart D) = 0 := by
      rw [Matrix.map_add _ (finPart D).map_add, hw', (WeilVacMove.isLineAt_lineAt hθ τ u).2.1 t, add_zero]
    rw [heisO, GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x hx0 w _ hw', hR.2 _ h0, hadd, hline]
  have hI : ∀ a b : Fin g → ℂ, hx X bas idx x (I • a) b = I * hx X bas idx x a b := fun a b => by
    simp only [hH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [annih, Pi.add_apply, Pi.smul_apply, key, key, hJ, map_smul]
  simp only [Pi.smul_apply, hI, ← Finset.mul_sum, smul_eq_mul]
  linear_combination (cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ z 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ z 1)))) * I_mul_I

end GlobalTheory.AdTh.FockVac
