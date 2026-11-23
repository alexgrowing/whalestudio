import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem relAmple_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.RelAmple (G i) (M i)) → Out.RelAmple A L := by
  intro S I U A _ G _ ψ hU hψ L M hL hM hiso hA _ hamp
  have : IsProper A.hom := hA.proper
  refine GlobalTheory.AmpleLocal.relAmple_of_locally S A L hL inferInstance inferInstance fun s => ?_
  obtain ⟨i, hi⟩ := exists_mem hU s
  obtain ⟨V, hV, hs, hle⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := U i) (x := s) hi
  have hle' : V ≤ U i := hle
  refine ⟨V, hs, ?_⟩
  have h := (hψ i).1
  have hf : S.homOfLE hle' ≫ (U i).ι = V.ι := S.homOfLE_ι hle'
  have sq : (A.hom ⁻¹ᵁ V).ι ≫ A.hom = ((A.hom ∣_ V) ≫ S.homOfLE hle') ≫ (U i).ι := by
    rw [Category.assoc, hf, morphismRestrict_ι]
  let φ : (A.hom ⁻¹ᵁ V).toScheme ⟶ (G i).left := h.lift _ _ sq
  have hφ : φ ≫ ψ i = (A.hom ⁻¹ᵁ V).ι := h.lift_fst _ _ _
  have H : IsPullback φ (A.hom ∣_ V) (G i).hom (S.homOfLE hle') := by
    refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [hφ, hf]
    exact (isPullback_morphismRestrict A.hom V).flip
  obtain ⟨w, hw⟩ : LBIso (L.pull (A.hom ⁻¹ᵁ V).ι) ((M i).pull φ) :=
    LBIso.chartPull (chartPullSame L (fun _ : PUnit => (A.hom ⁻¹ᵁ V).ι) (fun _ => ψ i) (fun _ => 1) φ fun _ => hφ.symm)
      (chartPullPull (M i) φ φ rfl) (hiso i).symm
  refine relAmple_pull (A' := Over.mk (A.hom ∣_ V)) H (hM i) (pull_isLB hL _) ((isGen_iff w).1 hw) ((U i).ι ⁻¹ᵁ V)
    (hV.preimage_of_isOpenImmersion _ (by simpa using hle')) (fun y => ?_) (hamp i)
  show (U i).ι (S.homOfLE hle' y) ∈ V
  rw [← Scheme.Hom.comp_apply, hf]
  exact y.2

end GlobalTheory.CoverGlue
