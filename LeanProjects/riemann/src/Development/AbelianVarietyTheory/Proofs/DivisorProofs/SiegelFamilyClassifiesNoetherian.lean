import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesNoetherianLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelClassifiedAtPrimeSpreadsBasicOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelNoeth

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id_eq (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap]
  exact Spec.map_id _

theorem classify_noetherian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ β c hc
  refine GlobalTheory.T.siegelFamily_classified_of_local g n hg hn hodd F (Sp R) (spMap β) c hc ?_
  intro x
  let 𝔭 : Ideal R := x.asIdeal
  haveI : 𝔭.IsPrime := x.isPrime
  have loc : ∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)),
      SiegPB c' c (spMap (algebraMap R (Localization.AtPrime 𝔭))) →
      ∃ f : Sp (Localization.AtPrime 𝔭) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) ∧
        SiegPB c' F.univ f := by
    intro c' hc'
    have hP := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) (Sp R) (Sp (Localization.AtPrime 𝔭)) (spMap β)
      (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)) (spMap (algebraMap R (Localization.AtPrime 𝔭))) rfl
      (by rw [spMap_id_eq, Category.comp_id]; exact (spMap_comp_eq _ _).symm)).2.1 c c' hc' hc
    exact GlobalTheory.T.siegelFamily_classifies_noetherian_local g n hg hn hodd F (Localization.AtPrime 𝔭) ((algebraMap R (Localization.AtPrime 𝔭)).comp β) c' hP
  obtain ⟨r, hr, H⟩ := GlobalTheory.T.siegelClassified_at_prime_spreads_basicOpen g n hg hn hodd F R β c 𝔭 hc loc
  let j : Sp (Localization.Away r) ⟶ Sp R := spMap (algebraMap R (Localization.Away r))
  have e : spMap ((algebraMap R (Localization.Away r)).comp β) = j ≫ spMap β := spMap_comp_eq _ _
  rw [e] at H
  obtain ⟨cV, hcV⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) (Sp R) (Sp (Localization.Away r)) (spMap β) (j ≫ spMap β) j rfl
      (by rw [spMap_id_eq, Category.comp_id])).1 c
  obtain ⟨f, hf, hfu⟩ := H cV hcV
  refine ⟨Sp (Localization.Away r), j, cV, IsOpenImmersion.of_isLocalization r, ?_, hcV, f, hf, hfu⟩
  have hu : Set.range j = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
  rw [hu]
  exact hr

end GlobalTheory.SiegelNoeth
