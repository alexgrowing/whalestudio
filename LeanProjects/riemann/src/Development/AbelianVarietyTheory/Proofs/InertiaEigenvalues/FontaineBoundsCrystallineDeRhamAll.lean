import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankPeriodFunctorCoeffBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExtEmbeddingSplittingStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.FontaineAll

noncomputable def extRep {G : Type} [Group G] {LL : Type} [Field LL] (LL' : Type) [Field LL']
    [Algebra LL LL'] {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V) :
    Representation LL' G (LL' ⊗[LL] V) where
  toFun g := (ρ g).baseChange LL'
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one LL V
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem fontCore_of_tied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : LocTied l P AI) (K : FinExt l) : Formalism.MainNotions.LocalSituation.fontCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A
  haveI : FiniteDimensional ℚ_[l] LL := hO.2.1
  obtain ⟨LL', ⟨f⟩, -, -⟩ := GlobalTheory.T.exists_finExt_embedding_splitting' l K LL
  letI : Algebra LL ↥LL'.1 := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL ↥LL'.1 :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : FiniteDimensional LL ↥LL'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] LL ↥LL'.1
  obtain ⟨hV, -, ⟨hc, hcf⟩, ⟨hd, hdf⟩, -⟩ :=
    GlobalTheory.T.finrank_periodFunctor_coeff_baseChange (P.PD K) LL ↥LL'.1 A.V (↥LL'.1 ⊗[LL] A.V) A.ρ (extRep ↥LL'.1 A.ρ)
      (TensorProduct.mk LL ↥LL'.1 A.V 1) (TensorProduct.isBaseChange LL A.V ↥LL'.1)
      (fun g x => by simp [extRep])
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.fontaineLe_of_tied l P AI hT K LL'
  obtain ⟨h3, h4⟩ := GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI hT K LL' _ (extRep ↥LL'.1 A.ρ)
  refine ⟨⟨hcf.1 (h2 _ _), ?_⟩, ⟨hdf.1 h3, ?_⟩, fun hcr => ?_⟩
  · rw [← hc, ← hV]; exact h1 _ _
  · rw [← hd, ← hV]; exact h4
  · have h5 : IsCrys (P.PD K) (extRep ↥LL'.1 A.ρ) := by
      unfold IsCrys at hcr ⊢
      rw [hc, hV]; exact hcr
    have h6 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL' _ _ h5).1
    unfold IsDR at h6 ⊢
    rw [← hd, ← hV]; exact h6

theorem fontaine_bounds : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm7 D :=
  fun D l _ K => fontCore_of_tied l (D.loc l) (D.locA l) (D.locT l) K

end GlobalTheory.Per.FontaineAll
