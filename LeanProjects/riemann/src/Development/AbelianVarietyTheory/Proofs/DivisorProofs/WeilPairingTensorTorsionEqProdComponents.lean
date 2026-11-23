import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPairingEqProdFactorPairingsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem weilQk_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ), 0 < k → ∀ (p' q' : QkPt D'.toPre F k) (ps qs : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs → ∀ z : Fin r → Fin r → Fˣ, (∀ i j, WeilQkIs D.toPre F k (ps i) (qs j) (z i j : F)) → WeilQkIs D'.toPre F k p' q' ((∏ i, ∏ j, z i j ^ (W + W.transpose) i j : Fˣ) : F) := by
  intro R _ _ _ _ D D' r W T F _ _ _ N N' ν ν' k hk p' q' ps qs hp hq z hz
  have gt : BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  have wp : BrWpSt := GlobalTheory.WeilValues.weil_eq_values gt (GlobalTheory.Ex.brFam GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1)
  have hk1 : 1 ≤ k := hk
  have hW := wp R D.toPre D.psi_even D.tau_bimult F N ν k hk1
  have hW' := wp R D'.toPre D'.psi_even D'.tau_bimult F N' ν' k hk1
  have hF := GlobalTheory.T.tensorData_values_facts R ‹_› D D' W T F N N' ν ν'
  obtain ⟨a', as, ha', has, hra⟩ := hp
  obtain ⟨b', bs, hb', hbs, hrb⟩ := hq
  have hv := GlobalTheory.T.tensorTorsionPairing_eq_prod_factor_pairings F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hF k hk1 a' b' as bs hra hrb
  refine (hW' p' q' a' b' _ ha' hb').2 ?_
  rw [hv]
  have hz' : ∀ i j, z i j = N.wp (as i) (bs j) := fun i j =>
    Units.ext ((hW (ps i) (qs j) (as i) (bs j) _ (has i) (hbs j)).1 (hz i j))
  simp only [hz']

end GlobalTheory.Mum.TensTor
