import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FrameCompare
open GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections (PowSec)

variable {S : Scheme.{0}} (G : Over S)

variable [GrpObj G] [IsCommMonObj G] (L : RigLB G) (N : ℕ)

omit [GrpObj G] [IsCommMonObj G] in

theorem relAmple_iff {O : Type} [CommRing O] (b : S ⟶ Sp O) {A : LB S} (hA : A.IsLB) :
    (Out.RelAmple (Over.mk b) A →
      ∀ z : S, ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ z ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s)) ∧
    (IsProper b → (∀ z : S, ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ z ∈ Out.nonzeroLocus s ∧
      IsAffineOpen (Out.nonzeroLocus s)) → Out.RelAmple (Over.mk b) A) := by
  constructor
  · intro h z
    obtain ⟨n, hn, s, hs⟩ := (isAmpleLB_of_relAmple_of_isAffine (Over.mk b) hA h).exists_affine z
    obtain ⟨s', e, -⟩ := exists_sec_oneTerm A (K' := Fin 1) (e' := (n : ℤ)) rfl s
    exact ⟨n, s', hn, by rw [← e] at hs; exact hs⟩
  · intro hb h
    have : IsProper (Over.mk b).hom := hb
    have hc : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace b
    have ha : IsAmpleLB A := ⟨hA, hc, fun z => by
      obtain ⟨n, s, hn, hs⟩ := h z
      obtain ⟨s', e, -⟩ := exists_sec_oneTerm A (K' := PUnit) (e' := (n : ℤ)) rfl s
      exact ⟨n, hn, s', by rw [← e] at hs; exact hs⟩⟩
    refine relAmple_of_isAmpleLB (Over.mk b) hA fun U hU => ?_
    have : CompactSpace (b ⁻¹ᵁ U).toScheme :=
      isCompact_iff_compactSpace.1 (QuasiCompact.isCompact_preimage (f := b) _ U.isOpen hU.isCompact)
    exact ha.pull_of_isOpenImmersion (b ⁻¹ᵁ U).ι

end GlobalTheory.FrameCompare
end
