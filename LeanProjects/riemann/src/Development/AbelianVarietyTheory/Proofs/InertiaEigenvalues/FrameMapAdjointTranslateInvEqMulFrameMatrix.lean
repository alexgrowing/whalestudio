import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.TranslateAdj

theorem frameAdjoint_translate_mul_frameConj_algebra {R S : Type} [CommRing R] [CommRing S] (σ : R →+* R) (f : R →+* S) {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (G K K' : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin m) (Fin m) R)
    (x : Matrix (Fin n) (Fin m) R) (βV : GL (Fin m) S) (βW : GL (Fin n) S)
    (hkey : (K'.map σ)ᵀ * G = G * K) (hP : P = 1) :
    (βV⁻¹).val * ((A * ((K' * x * P).map σ)ᵀ * G).map f) * βW.val =
      ((βV⁻¹).val * ((A * (x.map σ)ᵀ * G).map f) * βW.val) * ((βW⁻¹).val * K.map f * βW.val) := by
  subst hP
  have hβ : βW.val * (βW⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : A * ((K' * x * (1 : Matrix (Fin m) (Fin m) R)).map σ)ᵀ * G = A * (x.map σ)ᵀ * G * K := by
    rw [Matrix.mul_one, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc A, Matrix.mul_assoc, hkey]
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βW.val, hβ, Matrix.one_mul]

theorem frMapAdj_actO_inv : ∀ (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (x : WO V W), frMapAdj V W βV βW (actO V W 1 k⁻¹ x) = (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) := by
  intro D V W βV βW k x
  have hU : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt W k⁻¹) * W.gram.map (incA D) * Formalism.L2.Theta.mt W k⁻¹ =
      W.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig W.gram from k⁻¹).2
  have hi : Formalism.L2.Theta.mt W k⁻¹ * Formalism.L2.Theta.mt W k = 1 := by
    show Formalism.L2.Theta.mt W (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  have hkey : ((Formalism.L2.Theta.mt W k⁻¹).map (cA D)).transpose * W.gram.map (incA D) =
      W.gram.map (incA D) * Formalism.L2.Theta.mt W k := by
    calc _ = Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt W k⁻¹) * W.gram.map (incA D) *
          (Formalism.L2.Theta.mt W k⁻¹ * Formalism.L2.Theta.mt W k) := by rw [hi, Matrix.mul_one]; rfl
      _ = _ := by rw [← Matrix.mul_assoc, hU]
  have hmt1 : Formalism.L2.Theta.mt V (1 : GA D V)⁻¹ = 1 := by rw [inv_one]; rfl
  exact frameAdjoint_translate_mul_frameConj_algebra (cA D) (toEAf D) ((V.gram⁻¹).map (incA D)) (W.gram.map (incA D)) (Formalism.L2.Theta.mt W k)
    (Formalism.L2.Theta.mt W k⁻¹) (Formalism.L2.Theta.mt V (1 : GA D V)⁻¹) x βV βW hkey hmt1

end GlobalTheory.TranslateAdj
