import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatValEqValAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEmbeddingsCard
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MSmoothAndSemiPosIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfInducedOfInduced

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.NefModel

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem charZero_residueField (M : TrueGeo.Model Y) (y : Y.X) : CharZero (M.X.residueField (M.j y)) := by
  let f : F →+* Y.X.residueField y :=
    (Y.X.Γevaluation y).hom.comp (Y.str.appTop.hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom)
  have : CharZero (Y.X.residueField y) := charZero_of_injective_ringHom f.injective
  exact (M.j.residueFieldMap y).hom.charZero

theorem exists_isClosed (M : TrueGeo.Model Y) {z : M.X} (hz : ArInt.IsAlgPt z) :
    ∃ x : Y.X, IsClosed ({x} : Set Y.X) ∧ M.j x = z := by
  have := hz.1
  let o : Sp F := IsLocalRing.closedPoint F
  have : CharZero ((Sp F).residueField o) := (RingHom.charZero_iff (RingHom.injective
    (Scheme.Spec.residueFieldIso (.of F) o).inv.hom)).1
      ((RingHom.charZero_iff (algebraMap F _).injective).1 inferInstance)
  obtain ⟨x, hx, -⟩ := Scheme.exists_preimage_of_isPullback M.pb z o
    (PrimeSpectrum.ext ((Mean4O.asIdeal_eq_bot M.p z).trans
      (Mean4O.asIdeal_eq_bot (spMap (algebraMap (𝓞 F) F)) o).symm))
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  have : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip this
  refine ⟨x, isClosed_of_closure_subset fun y hy => ?_, hx⟩
  have := charZero_residueField M y
  obtain ⟨b, hb, hne⟩ := Mean4O.exists_specializes_ne M.ar (M.j y)
  have hs : z ⤳ M.j y := hx ▸ (specializes_iff_mem_closure.2 hy).map M.j.continuous
  exact M.j.isEmbedding.injective
    (hx.trans (((Mean4O.dim_closure_le_one_iff z).1 hz.2.le _ _ hs hb).resolve_right hne)).symm

theorem card_pos (M : TrueGeo.Model Y) {x : Y.X} (hx : IsClosed ({x} : Set Y.X)) :
    0 < Nat.card (M.X.residueField (M.j x) →+* ℂ) := by
  obtain ⟨_, _⟩ := ExtConj.pts Y x hx
  rw [ResidueCard.main F Y M x hx]
  exact mul_pos Module.finrank_pos Nat.card_pos

end GlobalTheory.TrueGeo.NefModel
