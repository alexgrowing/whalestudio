import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ClosedSubgroupsStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

theorem groups_invL {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hH : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hH]

theorem groups_invR {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    g * (Hpk k r * gᴴ * Hpk k r) = 1 :=
  mul_eq_one_comm.mp (groups_invL hg)

theorem groups_sset_closed (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hK : IsCompact (UWset k r z)) :
    IsClosed (Sset k r z) := by
  have hN : IsClosed (Nset k r) := (Formalism.FourierDecayAlt.P.B2x2.closedN k r).closed
  have : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.mp hK
  have hc : Continuous fun p : UWset k r z × Mat k r =>
      Hpk k r * ((p.1 : Mat k r))ᴴ * Hpk k r * p.2 := by
    refine Continuous.matrix_mul ?_ continuous_snd
    refine Continuous.matrix_mul ?_ continuous_const
    refine Continuous.matrix_mul continuous_const ?_
    exact (continuous_subtype_val.comp continuous_fst).matrix_conjTranspose
  have e : Sset k r z = Prod.snd '' {p : UWset k r z × Mat k r |
      Hpk k r * ((p.1 : Mat k r))ᴴ * Hpk k r * p.2 ∈ Nset k r} := by
    ext s
    constructor
    · rintro ⟨h, hh, m, hm, rfl⟩
      refine ⟨(⟨h, hh⟩, h * m), ?_, rfl⟩
      show Hpk k r * hᴴ * Hpk k r * (h * m) ∈ Nset k r
      rw [← Matrix.mul_assoc, groups_invL hh.1, Matrix.one_mul]
      exact hm
    · rintro ⟨⟨⟨h, hh⟩, s'⟩, hp, rfl⟩
      refine ⟨h, hh, _, hp, ?_⟩
      show s' = h * (Hpk k r * hᴴ * Hpk k r * s')
      rw [← Matrix.mul_assoc, groups_invR hh.1, Matrix.one_mul]
  rw [e]
  exact isClosedMap_snd_of_compactSpace _ (hN.preimage hc)

theorem closedSubgroups : ClosedSubgroupsStatement := by
  intro k r z
  refine ⟨Formalism.FourierDecayAlt.P.B2x2.closedG k r, Formalism.FourierDecayAlt.P.B2x2.closedN k r, fun hz hT => ⟨Formalism.FourierDecayAlt.P.B2x3.closedW k r z, ?_⟩⟩
  obtain ⟨h1, hmul, hinv⟩ := Formalism.QuantumDeterminants.sGroup k r z hz
  refine ⟨h1, hmul, hinv, ?_, groups_sset_closed k r z (Formalism.FourierDecayAlt.P.B2x3.compactW k r z hz hT)⟩
  rintro s ⟨h, hh, m, hm, rfl⟩
  rw [Matrix.det_mul]
  exact ((Formalism.FourierDecayAlt.P.B2x3.closedW k r z).unit h hh).mul ((Formalism.FourierDecayAlt.P.B2x2.closedN k r).unit m hm)

end ReciprocityTheory.ChartRestriction.DS.Lap
