import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDatumStandardLatticeTensorUnimodulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultiplicityAndRankTensorDataLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplecticBasesLevelPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDvdOfRingOfIntegersToIntMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTorsionIsometryOntoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.tens_pelOK : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → Nontrivial D.toPre.X → 1 ≤ r → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∃ Dm : Datum H, PelOK Dm D'.toPre o := by
  have hA := GlobalTheory.T.finrank_dvd_of_ringOfIntegers_to_int_matrix
  have hB := GlobalTheory.T.tensorDegenerationData_torsion_isometry_onto
  intro R _ _ _ hR E _ _ _ H D D' r W hpos hdet T ρ hadj hw0 hX hr _ o hact hpsi
  obtain ⟨s, hs⟩ := hA E ρ
  obtain ⟨Dm, e, hp, hq, he, hEF⟩ := GlobalTheory.T.exists_unitary_datum_standardLattice_tensor_unimodular E H W hpos hdet ρ hadj hw0
    (D.toPre.P.g + Module.finrank ℤ D.toPre.X) s hs
  obtain ⟨hrk, hlie⟩ := GlobalTheory.T.lieMultiplicity_and_rank_tensorData_lattice R hR E H D D' W hpos hdet T ρ o hact s hs
  have hs0 : s ≠ 0 := by rintro rfl; omega
  have hX0 : 0 < Module.finrank ℤ D.toPre.X := Module.finrank_pos
  refine ⟨Dm, hp.trans hq.symm, ?_, hpsi, fun F _ _ _ => ⟨fun τ => ⟨s * D.toPre.P.g, hlie F τ, ?_⟩, fun ζ hζ hζ' => ?_⟩⟩
  · rw [hp]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hs0 (by omega))
  · rw [hrk, hp]; ring
  · obtain ⟨ev, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_compatible_symplectic_bases_levelPoints R hR D F ζ hζ hζ' _ rfl
    exact hB R hR E H D D' W hpos hdet T ρ hadj hw0 o hact hpsi Dm _ e rfl he hEF F ζ hζ hζ' ev h1 h2 h3 h4 h5
