import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LoweredSignatureVanishing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignCompatibleNumberingOfWittTowerLower
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerSplit

theorem signCard_of_isEnum {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) (b : Bool) :
    GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard S b = (Finset.univ.filter fun a => ε a = b).card := by
  obtain ⟨hl, q, hq, rfl⟩ := h
  have hinj : Function.Injective q := fun a c hac => hl.injective (by rw [hq, hq, hac])
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard
  rw [Finset.filter_image, Finset.card_image_of_injective]
  intro a c hac
  exact hinj (Prod.ext_iff.1 hac).1

theorem hasSignature_of_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    Formalism.UG.HasSignature (gramAt D V τ) (GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (S τ) true)
      (GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (S τ) false) := by
  rw [signCard_of_isEnum (M.enum τ), signCard_of_isEnum (M.enum τ)]
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  refine GlobalTheory.AutInhab.hasSignature_of_frame (P := (M.fr τ)⁻¹) ?_ ?_
  · exact IsUnit.of_mul_eq_one _ (Matrix.nonsing_inv_mul _ hd)
  · rw [← M.fr_gram τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one,
      Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem exists_isoSplit : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (_M : DSModel V S) (r : ℕ)
    (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∃ (V' : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B ∧
      GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S r V' := by
  intro D V S M r C hC
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj V C
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp V.frame.equivFun.toLinearMap hC.2.1
  have hiso : ∀ a b, V.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hC.2.2]; rfl
  obtain ⟨V', ι, h1, h2, h3⟩ := GlobalTheory.WittLow.exists_lower Examples₂.star_isIntegral V e he hiso
  have hlow : IsWittLower V V' r := by
    refine ⟨h1, ι, h2, _, ⟨hC.2.1, hC.2.2⟩, ?_⟩
    refine Matrix.ext fun a b => ?_
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h3 _ _
  refine ⟨V', frameMat V V' ι, ⟨hC, ?_, ?_, by omega⟩, fun τ => ?_⟩
  · refine Matrix.ext fun a b => ?_
    unfold adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h2 _ _
  · refine Matrix.ext fun a b => ?_
    unfold adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul, ← V.herm.eq, h3]
    simp
  · obtain ⟨s, hs⟩ := GlobalTheory.WittLow.exists_sig V' (tauE D τ)
    have hs' : Formalism.UG.HasSignature (gramAt D V' τ) s.1 s.2 := hs
    obtain ⟨e1, e2⟩ := Formalism.UG.P.signature_unique _ _ _ _ _ _ (GlobalTheory.WittSign.hasSignature_of_isWittLower hlow τ hs')
      (hasSignature_of_model M τ)
    exact ⟨s.1, s.2, e1, e2, hs'⟩

end GlobalTheory.TowerSplit

end
