import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeFlagUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMonoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeIsotropicFlagStabiliStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.ConstTrans
open GlobalTheory.StdPar GlobalTheory.Cusp

theorem unip_eq_unipFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S = GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) := fun F E _ _ _ _ _ σ h n J hJ r X Y hW S m hm hm' => le_antisymm (GlobalTheory.T.standardParabolicUnipotent_le_flagUnipotentRadical F E σ h n J hJ r X Y hW S m hm hm') (GlobalTheory.T.flagUnipotentRadical_le_standardParabolicUnipotent F E σ h n J hJ r X Y hW S m hm hm')
theorem unip_mono : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)), T ⊆ S → GlobalTheory.StdPar.unip σ J X T ≤ GlobalTheory.StdPar.unip σ J X S := GlobalTheory.T.standardParabolicUnipotent_mono
theorem unip_le_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)) (m : Fin r), T ⊆ S → m ∈ T → (∀ k ∈ T, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.parFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (T.filter fun k => k.val < i.val).card) := GlobalTheory.T.standardParabolicUnipotent_le_isotropicFlagStabiliser

theorem isConstAlong_zero_of_subset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ φ : GAd σ J → ℂ, Continuous φ → (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) → ∀ S T : Finset (Fin r), T ⊆ S →
        GlobalTheory.StdPar.IsConstAlong σ J X T φ 0 → GlobalTheory.StdPar.IsConstAlong σ J X S φ 0 := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW φ hφc hφ S T hTS hT
  by_cases hT0 : T = ∅
  · subst hT0
    have e := isConstAlong_empty hT
    rw [← e]
    exact isConstAlong_const σ J X S 0
  obtain ⟨mT, hmT, hmT'⟩ : ∃ m ∈ T, ∀ k ∈ T, k ≤ m := ⟨T.max' (Finset.nonempty_iff_ne_empty.2 hT0),
    T.max'_mem _, fun k hk => T.le_max' k hk⟩
  obtain ⟨mS, hmS, hmS'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' ⟨mT, hTS hmT⟩, S.max'_mem _, fun k hk => S.le_max' k hk⟩
  have hσ := sigma_sigma h
  have eS := unip_eq_unipFlag F E σ h n J hJ r X Y hW S mS hmS hmS'
  have eT := unip_eq_unipFlag F E σ h n J hJ r X Y hW T mT hmT hmT'
  have hCS : IsIsoCols σ J (initCols X mS) := isIsoCols_of_isWittFrame hW hσ hJ mS.2
  have hCT : IsIsoCols σ J (initCols X mT) := isIsoCols_of_isWittFrame hW hσ hJ mT.2
  haveI : LocallyCompactSpace (unip σ J X S) := (isClosed_unip S h hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (unip σ J X T) := (isClosed_unip T h hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hcS : Cocompact (ratPts σ J) (unip σ J X S) := eS ▸ cocompact_unipFlag hJ hσ hCS _
  have hcT : Cocompact (ratPts σ J) (unip σ J X T) := eT ▸ cocompact_unipFlag hJ hσ hCT _
  have hφ' : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) φ := hφ
  have hnorm : ∀ p ∈ unip σ J X S, ∀ u ∈ unip σ J X T, p * u * p⁻¹ ∈ unip σ J X T := fun p hp u hu => by
    rw [eT] at hu ⊢
    exact conj_mem_unipFlag hJ hσ hCT _ (unip_le_parFlag F E σ h n J hJ r X Y hW S T mT hTS hmT hmT' hp) hu
  have h0 : (0 : GAd σ J → ℂ) = constTermOn (ratPts σ J) (unip σ J X T) φ :=
    (isConstTermOn_iff hcT fun γ hγ => hφ γ hγ.1).1 hT
  refine (isConstTermOn_iff hcS fun γ hγ => hφ γ hγ.1).2 (funext fun x => ?_)
  rw [Stages.constTermOn_stages (GAd σ J) (ratPts σ J) (unip σ J X S) (unip σ J X T)
    (unip_mono F E σ h n J hJ r X Y hW S T hTS) hnorm hcS hcT φ hφ' hφc x, ← h0]
  simp [constTermOn]

end GlobalTheory.ConstTrans
