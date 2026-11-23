import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectExistsCharZeroLiftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelFieldClass

theorem dense_generic {A V : Type} [CommRing A] [CommRing V] [IsDomain V] (β : A →+* V)
    (hβ : Function.Injective β) : Dense {x : Sp V | (spMap β x).asIdeal = ⊥} := by
  let ξ : Sp V := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)
  have hξ : ξ ∈ {x : Sp V | (spMap β x).asIdeal = ⊥} := by
    show (PrimeSpectrum.comap (CommRingCat.ofHom β).hom ⟨⊥, Ideal.isPrime_bot⟩).asIdeal = ⊥
    simp only [PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom]
    exact (RingHom.injective_iff_ker_eq_bot β).1 hβ
  have hd : Dense ({ξ} : Set (Sp V)) := by
    rw [dense_iff_closure_eq]
    show closure ({(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)} : Set (PrimeSpectrum V)) = Set.univ
    rw [PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  exact hd.mono (Set.singleton_subset_iff.2 hξ)

theorem classifies_algClosed : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp K ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ _ β c hc
  obtain ⟨V, _, _, βV, π, cV, hinj, hcomp, hpr, hpb⟩ := GlobalTheory.T.principal_siegel_object_exists_charZero_lift g n hg hn hodd K β c hc
  obtain ⟨f, hf, hfpb⟩ := F.rep (Sp V) (spMap βV) cV inferInstance (dense_generic βV hinj) hpr
  refine ⟨spMap π ≫ f, ?_, GlobalTheory.SiegelPullComp.pb_comp hfpb hpb⟩
  rw [Category.assoc, hf, ← hcomp]
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.SiegelFieldClass
