import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapLocallyQuasiFinite
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapFlatSemiabelian
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tors

section Identity
variable {R : Type} [CommRing R]

def toIdMk (Y : Over (Spec (CommRingCat.of R))) : Y ⟶ Over.mk (Y.hom ≫ 𝟙 _) :=
  Over.homMk (𝟙 _) (by simp)

def ofIdMk (Y : Over (Spec (CommRingCat.of R))) : Over.mk (Y.hom ≫ 𝟙 _) ⟶ Y :=
  Over.homMk (𝟙 _) (by simp)

theorem ofIdMk_toIdMk (Y : Over (Spec (CommRingCat.of R))) : ofIdMk Y ≫ toIdMk Y = 𝟙 _ := by
  ext
  simp [ofIdMk, toIdMk]

end Identity

theorem exists_qfGroup_kernel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsSemiAbelian B → ∀ (N : ℕ), 1 ≤ N → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] [IsCommMonObj A] (j : A ⟶ B) [IsMonHom j], IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B] → (∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g) → ∃ (C : Type) (_ : CommGroup C) (Γ : QFGroup R C) (φ : Γ.G ≅ A), IsMonHom φ.hom ∧ Γ.IsTorsionAlong B (𝟙 _) N (φ.hom.left ≫ j.left) := by
  intro R _ _ _ _ B _ hB N hN A _ _ j _ hp hpt
  have := hB.smooth
  have := hB.separated
  have := hB.quasiCompact
  have := hB.comm
  have := GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian (Spec (CommRingCat.of R)) B hB N hN
  have := GlobalTheory.CompanionTheory.Ar.BT.locallyQuasiFinite_pow_semiAbelian (Spec (CommRingCat.of R)) B hB N hN
  have hm := mono_of_pullback hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := kernel_props hp
  have := kernel_base_etale (genPt R).hom hp (isUnit_natCast_generic hN)
  haveI : IsReduced (genPt R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have hred := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd A.hom (genPt R).hom)
  have hv : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ 𝟙 _) ⟶ B) (y : Y ⟶ A),
      y.left ≫ j.left = g.left → y ≫ j = toIdMk Y ≫ g := fun {Y} g y h => by
    ext
    simpa [toIdMk] using h
  refine ⟨genPt R ⟶ A, inferInstance,
    { G := A, flat := h1, quasiFinite := h2, separated := h3, quasiCompact := h4, finPres := h5,
      pt := MonoidHom.id _, pt_inj := ?_, pt_onto := hpt, gen_reduced := hred }, Iso.refl _, ?_, ?_⟩
  · intro s t u v h
    exact Over.OverMorphism.ext (eq_of_same_point A.hom _ _ (Over.w _) (Over.w _) u v h)
  · show IsMonHom (𝟙 A)
    infer_instance
  · refine { isOver := ?_, mul := ?_, inj := ?_, kernel := ?_ }
    · show (𝟙 _ ≫ j.left) ≫ B.hom = A.hom ≫ 𝟙 _
      simpa using Over.w j
    · intro Y y z y₀ z₀ hy hz
      have hy' : y ≫ j = toIdMk Y ≫ y₀ := hv y₀ y (by rw [hy]; simp)
      have hz' : z ≫ j = toIdMk Y ≫ z₀ := hv z₀ z (by rw [hz]; simp)
      have e : (y * z) ≫ j = toIdMk Y ≫ (y₀ * z₀) := by
        rw [MonObj.mul_comp, hy', hz', MonObj.comp_mul]
      have e' := congrArg (fun w => w.left) e
      simpa [toIdMk] using e'.symm
    · intro Y y z h
      rw [← cancel_mono j]
      ext
      simpa using h
    · intro Y g
      constructor
      · intro h
        have h' : (toIdMk Y ≫ g) ^ N = 1 := by
          rw [← MonObj.comp_pow, h, MonObj.comp_one]
        obtain ⟨y, hy⟩ := lift_of_torsion hp _ h'
        refine ⟨y, ?_⟩
        have e := congrArg (fun w => w.left) hy
        simpa [toIdMk] using e
      · rintro ⟨y, hy⟩
        have e : y ≫ j = toIdMk Y ≫ g := hv g y (by rw [← hy]; simp)
        have h' : (toIdMk Y ≫ g) ^ N = 1 := by rw [← e]; exact torsion_of_comp hp y
        have e2 : ofIdMk Y ≫ toIdMk Y ≫ g = g := by
          rw [← Category.assoc, ofIdMk_toIdMk, Category.id_comp]
        rw [← e2, ← MonObj.comp_pow, h', MonObj.comp_one]

end GlobalTheory.CompanionTheory.Ar.BT.Tors
