import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotFrobGUnitRat
open CategoryTheory GlobalTheory.AV GlobalTheory.AV.AbVar

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry Limits MonObj GlobalTheory.Published.AbVarRed GlobalTheory.SS.FrobModel
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AV.FrobEx

theorem frobOver_ptOver (K : Type) [Field K] [Fintype K] :
    frobOver (ptOver K (AlgebraicClosure K)) =
      specAut (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  apply Over.OverMorphism.ext
  change absFrob (ptOver K (AlgebraicClosure K)) = Spec.map (CommRingCat.ofHom
    ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
      AlgebraicClosure K →+* AlgebraicClosure K))
  haveI : IsAffine (ptOver K (AlgebraicClosure K)).left := inferInstanceAs (IsAffine (Spec _))
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).inv]
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext c
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  have e : ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) :
      AlgebraicClosure K →+* AlgebraicClosure K) c) = c ^ Fintype.card K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic_apply K (AlgebraicClosure K) c
  exact ((congrArg (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv.hom e).trans (map_pow _ c _)).symm

theorem isFrob_frobOver (K : Type) [Field K] [Fintype K] (A : AbVar K) :
    letI : IsMonHom (frobOver A.X) := (frobG_frobOver A.X).1
    IsFrob (A := A) (Hom.mk (frobOver A.X)) := by
  letI : IsMonHom (frobOver A.X) := (frobG_frobOver A.X).1
  intro x
  rw [mk_hom, ← frobOver_comm, frobOver_ptOver]
  rfl

end GlobalTheory.AV.FrobEx
