import Mathlib
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.PsJetEqToJetOfNonempty
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.UnifAnyResidue

theorem exists_local_extension {V W k : Type} [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W]
    [Algebra V W] [Module.Finite V W] [IsLocalHom (algebraMap V W)] [Field k] [IsAlgClosed k] (r : V →+* k)
    [IsLocalHom r] : ∃ r' : W →+* k, r'.comp (algebraMap V W) = r ∧ IsLocalHom r' := by
  let : Algebra (ResidueField V) k := (ResidueField.lift r).toAlgebra
  have : Module.Finite (ResidueField V) (ResidueField W) := inferInstance
  let e : ResidueField W →ₐ[ResidueField V] k := IsAlgClosed.lift
  refine ⟨e.toRingHom.comp (residue W), RingHom.ext fun v => ?_, inferInstance⟩
  exact (e.commutes (residue V v)).trans (ResidueField.lift_residue_apply r v)

theorem exists_ext_pelUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (T : CDVR) (t : SAB H (Sp T.V)), GlobalTheory.LN.PolAt t (jK T.V) → ∀ (k : Type) [Field k] [IsAlgClosed k] (r : T.V →+* k), IsLocalHom r → ∃ (T' : CDVR) (φ : T.V →+* T'.V) (r' : T'.V →+* k) (t' : SAB H (Sp T'.V)), r'.comp φ = r ∧ IsLocalHom r' ∧ Nonempty (SABMap t' t (spMap φ)) ∧ Nonempty (PELUnif (maximalIdeal T'.V) t') := by
  intro E _ _ _ H T t hp k _ _ r hr
  let F := AlgebraicClosure (FractionRing T.V)
  have hF : Function.Injective (algebraMap T.V F) := by
    rw [IsScalarTower.algebraMap_eq T.V (FractionRing T.V) F]
    exact (algebraMap (FractionRing T.V) F).injective.comp (IsFractionRing.injective T.V _)
  have : FaithfulSMul T.V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hF
  have : Algebra.IsAlgebraic T.V F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing T.V)).2 inferInstance
  obtain ⟨W, hd, hc, hf, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split T.V F t.G t.semi
  have hi : Function.Injective (algebraMap T.V W) := fun _ _ h => hF (congrArg (fun z : W => (z : F)) h)
  have hz : CharZero W := charZero_of_injective_ringHom hi
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T.V W) := inferInstance
  obtain ⟨r', h₁, h₂⟩ := exists_local_extension (W := W) r
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull CubePf.cubePull (spMap (algebraMap T.V W)) t
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  let g : FractionRing T.V →+* FractionRing W := IsFractionRing.lift j
  have hp' := GlobalTheory.DatUniq.polAt_pull m hp (jK W) (spMap g)
    ((GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W ⟨hd, hc, hz⟩ _ hp' hs
  exact ⟨{ V := W }, algebraMap T.V W, r', _, h₁, h₂, ⟨m⟩, ⟨P⟩⟩

end GlobalTheory.UnifAnyResidue
