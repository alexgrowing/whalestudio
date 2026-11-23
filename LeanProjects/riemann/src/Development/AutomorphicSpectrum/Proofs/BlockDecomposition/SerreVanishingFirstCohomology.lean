import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

theorem serre_vanishing_coh_one : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {F : X.Modules}, IsCoherent F → ∃ n₂ : ℤ, ∀ n, n₂ ≤ n → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) 1) := by
  intro A _ _ X _ _ H hH F hF
  letI : Algebra A ↑(X.presheaf.obj (Opposite.op ⊤)) :=
    ((X ↘ Spec (.of A)).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).toAlgebra
  obtain ⟨hq, hfin⟩ := hF
  haveI : GlobalTheory.QCoh.IsFiniteQC F := GlobalTheory.QCoh.IsFiniteQC.mk hq hfin
  haveI : IsProper ((X ↘ Spec (.of A)) : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A) := ‹IsProper (X ↘ Spec (.of A))›
  have hev := GlobalTheory.IsAmpleLB.eventually_subsingleton_coh_twistZ (R := A)
    (f := ((X ↘ Spec (.of A)) : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A)) (fun _ => rfl) F hH
  obtain ⟨n₂, hn⟩ := Filter.eventually_atTop.1 hev
  exact ⟨n₂, fun n hn' => hn n hn' 1 Nat.one_pos⟩

end GlobalTheory.CompanionTheory.GE.Step
