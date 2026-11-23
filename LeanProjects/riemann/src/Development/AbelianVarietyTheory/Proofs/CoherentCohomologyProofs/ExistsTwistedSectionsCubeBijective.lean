import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TwistedSectionsLocaliseToChartsStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

section

variable {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {H : LB Y}
  {ι : Type} {s : ι → LB.Sec H} {M : LB Y}
  (hx : ∀ V : Y.Opens, OperatorsCommute (ι := ι) (A := fun t => SecOnR f (tw M H t) V)
    fun i t => SecOnR.mulSec f M t (s i) V)

noncomputable def twistedSumRestrict {V W : Y.Opens} (h : W ≤ V) :
    GrSum (hx V) →ₗ[MvPolynomial ι R] GrSum (hx W) :=
  GrSum.map (hx V) (hx W) (fun t => SecOnR.restrict f (tw M H t) h)
    fun i _ a => (SecOn.mulSec_restrict (s i) h a).symm

theorem twistedSumRestrict_of {V W : Y.Opens} (h : W ≤ V) (t : ℤ) (a : SecOnR f (tw M H t) V) :
    twistedSumRestrict hx h (GrSum.of (hx V) t a) =
      GrSum.of (hx W) t (SecOnR.restrict f (tw M H t) h a) :=
  GrSum.map_of (hx V) (hx W) (fun t => SecOnR.restrict f (tw M H t) h)
    (fun i _ a => (SecOn.mulSec_restrict (s i) h a).symm) t a

theorem twistedSumRestrict_comp {U V W : Y.Opens} (h : V ≤ U) (h' : W ≤ V) (y : GrSum (hx U)) :
    twistedSumRestrict hx h' (twistedSumRestrict hx h y) =
      twistedSumRestrict hx (h'.trans h) y := by
  have e : ((twistedSumRestrict hx h' ∘ₗ twistedSumRestrict hx h).restrictScalars R) =
      (twistedSumRestrict hx (h'.trans h)).restrictScalars R :=
    GrSum.lhom_ext _ fun n a => by
      simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, twistedSumRestrict_of,
        SecOnR.restrict_restrict]
  exact congr($e y)

end

theorem exists_grCube_twistedSections_hom_secCube_bijective :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (t : ℤ), ∃ φ : grCube (Fin (m + 1)) (GrSum.grading (hx ⊤)) t ⟶ secCube f (tw M H t) (fun i => nonzeroLocus (s i)), ∀ I, Function.Bijective (φ.app I).hom := by
  intro R _ Y f H m s M hH hM hva hx
  have hloc := GlobalTheory.T.twistedSections_localise_to_charts R Y f H m s M hH hM hva hx
  refine GlobalTheory.exists_grCube_hom_bijective (Fin (m + 1)) R (GrSum (hx ⊤)) (GrSum.grading (hx ⊤))
    (fun t => secCube f (tw M H t) fun i => nonzeroLocus (s i))
    (fun i t => secCubeMul f M _ t (s i)) (fun I => hx (⨅ i ∈ I, nonzeroLocus (s i)))
    (fun I => twistedSumRestrict hx (le_top : (⨅ i ∈ I, nonzeroLocus (s i)) ≤ ⊤))
    (fun I => GrSum.isGradedMap_map _ _ _ _) (fun I J h n y a e => ?_)
    (fun I i hi t => SecOnR.mulSec_bijective f t (s i) (biInf_le (fun i => nonzeroLocus (s i)) hi))
    (fun I n y hy e => ?_) (fun I t a => ?_)
  · have h' := iInf_le_iInf_of_subset (fun i => nonzeroLocus (s i)) h
    exact (twistedSumRestrict_comp hx le_top h' y).symm.trans
      ((congrArg (twistedSumRestrict hx h') e).trans (twistedSumRestrict_of hx h' n a))
  · obtain ⟨a, rfl⟩ := hy
    refine (hloc I).1 n a (GrSum.of_injective (hx _) n ?_)
    exact ((twistedSumRestrict_of hx le_top n a).symm.trans e).trans (map_zero _).symm
  · obtain ⟨k, t', b, hb⟩ := (hloc I).2 t a
    exact ⟨k, GrSum.of (hx ⊤) t' b, (twistedSumRestrict_of hx le_top t' b).trans hb⟩

end GlobalTheory
