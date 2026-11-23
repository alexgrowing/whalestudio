import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelDescendsFiniteTypeSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifyingMapUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFamAll

theorem exists_classify_affine {g n : ℕ} (hg : 1 ≤ g) (hn : 3 ≤ n) (hodd : Odd n) (F : SFam g n (zetaAway n))
    (R : Type) [CommRing R] (t : Sp R ⟶ Sp (cycAway n)) (d : SiegPre g n (zetaAway n) t) (hd : d.Principal) :
    ∃ f : Sp R ⟶ F.X, f ≫ F.s = t ∧ SiegPB d F.univ f := by
  obtain ⟨β, rfl⟩ := GlobalTheory.SiegelRingChange.exists_spMap t
  obtain ⟨R₀, β₀, c₀, hft, hβ, hp₀, hpb⟩ := GlobalTheory.T.principalSiegel_descends_finiteType_subring g n hn hodd R β d hd
  haveI : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  obtain ⟨f₀, hf₀, hpb₀⟩ := GlobalTheory.T.siegelFamily_classifies_noetherian g n hg hn hodd F R₀ β₀ c₀ hp₀
  refine ⟨spMap R₀.subtype ≫ f₀, ?_, GlobalTheory.TChart.AbLevel.siegPB_trans hpb hpb₀⟩
  rw [Category.assoc, hf₀, ← GlobalTheory.SiegelRingChange.spMap_comp', hβ]

theorem existsUnique_classify : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal →
      ∃! f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F S s' c hc
  obtain ⟨f, hf, hpf⟩ := GlobalTheory.T.siegelFamily_classified_of_local g n hg hn hodd F S s' c hc (fun x => by
    let 𝒰 := S.affineOpenCover
    let j : Sp (𝒰.X (𝒰.idx x)) ⟶ S := 𝒰.f (𝒰.idx x)
    have hid : j ≫ s' = (j ≫ s') ≫ spMap (RingHom.id (cycAway n)) := by simp [spMap]
    have key := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) S (Sp (𝒰.X (𝒰.idx x))) s' (j ≫ s') j rfl hid
    obtain ⟨cV, hcV⟩ := key.1 c
    have hpV : cV.Principal := key.2.1 c cV hcV hc
    obtain ⟨fV, hfV, hpbV⟩ := exists_classify_affine hg hn hodd F (𝒰.X (𝒰.idx x)) (j ≫ s') cV hpV
    exact ⟨Sp (𝒰.X (𝒰.idx x)), j, cV, inferInstance, 𝒰.covers x, hcV, fV, hfV, hpbV⟩)
  exact ⟨f, ⟨hf, hpf⟩, fun f' hf' => GlobalTheory.T.siegelFamily_classifyingMap_unique g n hg hn hodd F S s' c f' f hf'.1 hf hf'.2 hpf⟩

end GlobalTheory.SiegFamAll
