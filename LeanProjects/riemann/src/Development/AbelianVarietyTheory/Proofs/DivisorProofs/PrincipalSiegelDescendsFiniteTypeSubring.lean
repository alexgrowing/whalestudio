import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Data
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeomPtSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticOfSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrincipalOfSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFG

theorem siegPre_descends_fg : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (c₀ : SiegPre g n (zetaAway n) (spMap β₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ c₀.Principal ∧ SiegPB c c₀ (spMap R₀.subtype) := by
  intro g n hn hodd R _ β c hc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨R₀, β₀, A₀, _, P₀, lv₀, hft, hβ, hsym, hadd, hamp, hpb⟩ := GlobalTheory.SiegFGData.data g n hn hodd R β c hc
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have hpb' := hpb
  obtain ⟨φ, φ₂, hφ, s₁, s₂, iso, hl⟩ := hpb
  have hpr : IsPrincipal A₀ P₀ :=
    GlobalTheory.PrincSubring.isPrincipal_of_subring g R R₀ c.A c.P A₀ P₀ φ φ₂ hsym hamp hφ ⟨s₁, s₂⟩ iso ((principal_iff c).1 hc)
  let u : (cycAway n)ˣ := Units.ofPowEqOne (zetaAway n) n (zetaAway_pow_self hn0) hn0
  have hζ : u ^ n = 1 := Units.ext (by simp [u])
  have hunit : IsUnit (n : R₀) := by simpa using (isUnit_natCast hn0).map β₀
  have hlevR : IsLevel c.A (lvOf c) := isLevel_lvOf (ζ := u) c
  have hlev₀ : IsLevel A₀ lv₀ :=
    GlobalTheory.LevelDescent.isLevel_of_subring g n R R₀ c.A A₀ φ (lvOf c) lv₀ (by omega) hunit hsym.1 hφ hl hadd hlevR
  have hsympR : IsSymplectic u (spMap β) c.A c.P (lvOf c) :=
    isSymplectic_of_translFixed (ζ := u) hn0 hζ (isUnit_natCast hn0) c (translFixed_of_ample c hc.1)
  have hsymp₀ : IsSymplectic u (spMap β₀) A₀ P₀ lv₀ :=
    GlobalTheory.SympDescent.isSymplectic_of_subring g n (cycAway n) R u R₀ (spMap β₀) c.A c.P (lvOf c) A₀ P₀ lv₀ (by omega) hζ hunit hsym hpr hlev₀
      c.isLB hpb' (by rw [← GlobalTheory.SiegelTypings.spMap_comp, hβ]; exact hsympR)
  let c₀ : SiegPre g n (zetaAway n) (spMap β₀) := ofTriple (ζ := u) hn0 hζ A₀ P₀ lv₀ hsym hlev₀ hsymp₀
  refine ⟨R₀, β₀, c₀, hft, hβ, (principal_iff c₀).2 hpr, (siegPB_iff c c₀ _).2 ?_⟩
  rw [show lvOf c₀ = lv₀ from lvOf_ofTriple (ζ := u) hn0 hζ A₀ P₀ lv₀ hsym hlev₀ hsymp₀]
  exact hpb'

end GlobalTheory.SiegFG
