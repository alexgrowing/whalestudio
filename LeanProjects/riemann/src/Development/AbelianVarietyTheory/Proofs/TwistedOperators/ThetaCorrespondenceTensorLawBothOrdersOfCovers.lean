import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelJointHarmonicsFormNormalisationUniqueneStatement

noncomputable section

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

namespace GlobalTheory.ArchRec.TensLawOf

section

variable {p q r s : ℕ}

theorem cJoint_swap {σ : Type} (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))
    (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ)
    (Φ : MvPolynomial σ ℂ) (h : CJoint a₁ a₂ Λ₁ Λ₂ Φ) : CJoint a₂ a₁ Λ₂ Λ₁ Φ := by
  obtain ⟨⟨d, h0, h1, h2⟩, h3, h4⟩ := h
  exact ⟨⟨d, h0, h2, h1⟩, h4, h3⟩

theorem tIntw_swap {W : Type} [AddCommGroup W] [Module ℂ W] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ W)
    (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ W) (M₁ : GKMod p q) (M₂ : GKMod r s) (f : W →ₗ[ℂ] M₁.V ⊗[ℂ] M₂.V)
    (h : TIntw a₁ a₂ M₁ M₂ f) :
    TIntw a₂ a₁ M₂ M₁ ((TensorProduct.comm ℂ M₁.V M₂.V).toLinearMap ∘ₗ f) := by
  constructor
  · intro Y
    rw [LinearMap.comp_assoc, h.2 Y, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    congr 1
    ext x y
    simp
  · intro Y
    rw [LinearMap.comp_assoc, h.1 Y, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    congr 1
    ext x y
    simp

theorem comm_comp_inj {W A B : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] {f g : W →ₗ[ℂ] A ⊗[ℂ] B}
    (h : (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f = (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ g) : f = g := by
  refine LinearMap.ext fun x => ?_
  exact (TensorProduct.comm ℂ A B).injective (LinearMap.congr_fun h x)

theorem range_swap {W A B C : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] (f : W →ₗ[ℂ] A ⊗[ℂ] B) (j : C →ₗ[ℂ] B)
    (h : LinearMap.range ((TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f) =
      LinearMap.range (TensorProduct.map j (LinearMap.id : A →ₗ[ℂ] A))) :
    LinearMap.range f = LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) j) := by
  have e : (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) j =
      TensorProduct.map j (LinearMap.id : A →ₗ[ℂ] A) ∘ₗ (TensorProduct.comm ℂ A C).toLinearMap := by
    ext x y
    simp
  apply Submodule.map_injective_of_injective (f := (TensorProduct.comm ℂ A B).toLinearMap)
    (TensorProduct.comm ℂ A B).injective
  rw [← LinearMap.range_comp, ← LinearMap.range_comp, h, e,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

end

theorem tensLaw_of : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), ARi X lam lam' → ARiiiUp X lam lam' → ARiiiDown X lam lam' → ARiiiLine X lam lam' → TensLaw (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) (X.ds r s lam') (blattner lam) (blattner lam') ∧ TensLaw (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam') (X.ds p q lam) (blattner lam') (blattner lam) := by
  intro X p q r s lam lam' h1 hU hD hL
  obtain ⟨hiff, hnorm, huniq⟩ := GlobalTheory.T.fockModel_jointHarmonics_form_normalisation_uniqueness X p q r s (blattner lam) (blattner lam')
  obtain ⟨Φ₀, hΦ₀⟩ := h1.1
  have hex : CJoint (fockAct1 p q r s) (fockAct2 p q r s) (blattner lam) (blattner lam') Φ₀ :=
    (hiff Φ₀).2 ⟨hΦ₀.1, hΦ₀.2.1, hΦ₀.2.2.1⟩
  refine ⟨⟨⟨Φ₀, hex⟩, huniq, ?_, hL⟩, ⟨⟨Φ₀, cJoint_swap _ _ _ _ _ hex⟩,
    fun Φ Φ' h h' => huniq Φ Φ' (cJoint_swap _ _ _ _ _ h) (cJoint_swap _ _ _ _ _ h'), ?_, ?_⟩⟩
  · intro MM f hf hf0
    obtain ⟨⟨N, -, e, he⟩, hΦ⟩ := hU MM f hf hf0
    refine ⟨⟨N, e, he⟩, fun Φ hJ => ?_⟩
    obtain ⟨c, -, hc⟩ := hnorm Φ hJ
    obtain ⟨g1, g2⟩ := hΦ _ hc
    refine ⟨fun h0 => g1 (by rw [map_smul, h0, smul_zero]), fun f' hf' h => g2 f' hf' ?_⟩
    rw [map_smul, map_smul, h]
  · intro MM f hf hf0
    have hf1 := tIntw_swap _ _ _ _ f hf
    obtain ⟨⟨N, -, e, he, hr⟩, hΦ⟩ := hD MM _ hf1
      (fun h => hf0 (comm_comp_inj (by rw [h, LinearMap.comp_zero])))
    refine ⟨⟨N, e, he, range_swap f _ hr⟩, fun Φ hJ => ?_⟩
    obtain ⟨c, -, hc⟩ := hnorm Φ (cJoint_swap _ _ _ _ _ hJ)
    obtain ⟨g1, g2⟩ := hΦ _ hc
    refine ⟨fun h0 => g1 (by rw [map_smul, LinearMap.comp_apply, h0, map_zero, smul_zero]), fun f' hf' h =>
      comm_comp_inj (g2 _ (tIntw_swap _ _ _ _ f' hf') ?_)⟩
    rw [map_smul, map_smul, LinearMap.comp_apply, LinearMap.comp_apply, h]
  · obtain ⟨f₀, hf₀, hne, hall⟩ := hL
    refine ⟨_, tIntw_swap _ _ _ _ f₀ hf₀,
      fun h => hne (comm_comp_inj (by rw [h, LinearMap.comp_zero])), fun f hf => ?_⟩
    obtain ⟨c, hc⟩ := hall _ (tIntw_swap _ _ _ _ f hf)
    refine ⟨c, comm_comp_inj ?_⟩
    rw [hc]
    refine LinearMap.ext fun x => ?_
    simp

end GlobalTheory.ArchRec.TensLawOf

end
