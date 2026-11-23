import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilySimilitudeGroupActionFreeTransitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelLowerLevelDescendsGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDescentEtaleCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

theorem nonempty_sQuot : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N →
    j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Nonempty (SQuot F n (zetaAway n) j) := by
  intro h n N F j hn hN hdvd hj hfin het
  have hn0 : n ≠ 0 := by omega
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hN)
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hover, hlow, hfree, htrans⟩ := GlobalTheory.T.siegelFamily_similitudeGroup_action_free_transitive h n N F j hn hN hdvd hj
  have hjf : j.Finite := (IsFinite.SpecMap_iff _).1 hfin
  have hq : IsQProjOver (F.s ≫ spMap j) :=
    (GlobalTheory.isQProjOver_baseChange_and_finite_restrict _ _ j F.X (F.s ≫ spMap j)).2 F.s hjf F.qproj
  obtain ⟨Y, π, sY, hπ, hG, hsep, hft, -⟩ :=
    GlobalTheory.T.exists_galoisCover_quotient_freeFiniteAction (cycAway n) F.X (F.s ≫ spMap j) Ga ρ hq h1 hmul hover hfree
  have hqY : IsQProjOver sY := GlobalTheory.T.isQProjOver_target_galoisCover_noetherian (cycAway n) F.X Y π sY Ga ρ hG hsep hft (by rw [hπ]; exact hq)
  have hsm : SmoothOfRelativeDimension (h * (h + 1) / 2) (π ≫ sY) := by
    rw [hπ]
    haveI := F.smooth
    haveI : SmoothOfRelativeDimension 0 (spMap j) := inferInstance
    have := smoothOfRelativeDimension_comp (h * (h + 1) / 2) 0 F.s (spMap j)
    rwa [Nat.add_zero] at this
  have hsY : SmoothOfRelativeDimension (h * (h + 1) / 2) sY :=
    GlobalTheory.T.smoothOfRelativeDimension_descent_etaleCover (cycAway n) F.X Y π sY _ hG.etale hG.onto hft hsm
  obtain ⟨c, hc, hlowc⟩ := GlobalTheory.T.principal_siegel_lower_level_descends_galois h n N (cycAway n) (cycAway N) (cycBase hn0) (zetaAway N) j F.X Y F.s π sY F.univ
    Ga ρ ν hN0 (isUnit_natCast hN0) hdvd (by rw [cycBase_ζ]; exact hj) hπ hG (by rw [hπ]; exact hq) hft F.princ hν1
    hνmul hlow
  refine ⟨⟨Y, sY, hsY, hqY, c, hc, π, hπ, hG.fin, hG.etale, hG.onto, hlowc, ?_⟩⟩
  intro R _ _ y y' s' c' h₀ h₁ h₂
  obtain ⟨a, rfl⟩ := htrans R y y' s' c' h₀ h₁ h₂
  rw [Category.assoc, hG.inv]

example : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N → j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Nonempty (SQuot F n (zetaAway n) j) := nonempty_sQuot

end GlobalTheory.SiegLev

end
