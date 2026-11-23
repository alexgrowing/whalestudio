import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpairGeo

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Twpair

theorem tw_pair : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, ζ n ^ p ^ n = 1) → X.PairingRegular B ζ → ∀ n, ∃ s ∈ prodSpan ((X.Γ n).btOrder ⊤), ∀ a b, s (lev p n a, lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p hpp C _ _ _ v O _ _ _ hv _ _ S _ G _ _ _ y La _ _ _ X B ζ hζ hreg n
  have : ValuationRing O := ValuationRing.of_integers v hv
  have := finite_levGrp (La := La) hpp.out.ne_zero n
  obtain ⟨β, hβ⟩ := exists_bichar p n B (ζ n) (hζ n)
  obtain ⟨s, hs⟩ := hreg n
  refine ⟨_, bichar_mem_prodSpan (henselian hv) (fun P => ?_) (X.Γ n) β s fun a b => ?_, fun a b => ?_⟩
  · exact (prime_eq_bot_or_maximal hv P.asIdeal).imp id fun h => PrimeSpectrum.ext h
  · obtain ⟨a, rfl⟩ := lev_surjective p n a
    obtain ⟨b, rfl⟩ := lev_surjective p n b
    rw [hβ]
    exact hs a b
  · exact congrArg Units.val (hβ a b)

end PositivityTheory.HtPt.Twpair
