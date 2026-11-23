import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyHeightOnePrimesOfFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreBaseFlatNoetherianIntClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatAlgHomEtaleHeightOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureZmodTorsorGenericFibreDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleOfGaloisDescentHartogsStatement
open IsLocalRing Polynomial
open scoped TensorProduct

theorem GlobalTheory.GoodEtale.closure_finiteEtale : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    ∀ (q : ℕ), 0 < q → IsUnit (q : A) →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
      GlobalTheory.KeyOriginNoeth.Good A (Localization.AtPrime QA) DA ρ →
      GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A (Localization.AtPrime QA) DA := by
  intro A _ _ _ _ _ _ EA _ _ _ _ _ QA _ hQA ρ hρ hker q hq hqu DA _ _ actA htor hgood
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨hflat, hnoeth, ht, hic⟩ := GlobalTheory.T.genericFibreBase_flat_noetherian_intClosed A EA QA hQA ρ hρ hker
  haveI := hflat
  haveI := hnoeth
  have hHR := GlobalTheory.T.hasHartogsPropertyHeightOnePrimes_of_flat A (Localization.AtPrime QA)
  obtain ⟨act', T, hT, ⟨a, ha, n, x, y, hxy⟩, htf, hHC, hint, hnt⟩ :=
    GlobalTheory.T.integralClosure_zmodTorsor_genericFibre_data A (Localization.AtPrime QA) hHR hic q DA actA htor
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A (Localization.AtPrime QA) DA
  obtain ⟨hEt, s, hs⟩ := hgood
  obtain ⟨O, _, _, hO, hσ⟩ := GlobalTheory.T.exists_faithfullyFlat_algHom_etale_height_one A (Localization.AtPrime QA) (GlobalTheory.KeyOriginNoeth.closure A _ DA)
    ρ hρ _ hker ht hint (fun P _ h => hEt P h) ⟨s, hs⟩
  obtain ⟨hfin, het⟩ := GlobalTheory.T.finiteEtale_of_galois_descent_hartogs A (Localization.AtPrime QA) (GlobalTheory.KeyOriginNoeth.closure A _ DA) O
    (Multiplicative (ZMod q)) act' T hT a ha n x y hxy htf hHC (fun P _ h => hEt P h) hσ
  exact ⟨hfin, het, hnt⟩
