import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusLieCoord

variable {R : Type} [CommRing R] {r : ℕ}

def valA {A : Type} [CommRing A] [Algebra R A] (t : specO R A ⟶ torus R r) (χ : Fin r → ℤ) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    (t.left.appTop.hom (charUnit (Spec (CommRingCat.of R)) (Fin r → ℤ) χ).val)

theorem valA_eq {A : Type} [CommRing A] [Algebra R A] (t : specO R A ⟶ torus R r) (χ : Fin r → ℤ) :
    valA t χ = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (GlobalTheory.splitTorusPointsEquiv _ _ _ t (Multiplicative.ofAdd χ)).val := by
  rw [GlobalTheory.splitTorusPointsEquiv_val]; rfl

theorem valA_comp {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (t : specO R A ⟶ torus R r) (χ : Fin r → ℤ) :
    valA (ptMap f ≫ t) χ = f (valA t χ) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f.toRingHom)
  unfold valA
  rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact congrArg (fun g => g.hom (t.left.appTop.hom (charUnit (Spec (CommRingCat.of R)) (Fin r → ℤ) χ).val)) h

theorem valA_one {A : Type} [CommRing A] [Algebra R A] (χ : Fin r → ℤ) :
    valA (1 : specO R A ⟶ torus R r) χ = 1 := by
  rw [valA_eq, map_one, MonoidHom.one_apply, Units.val_one, map_one]

theorem valA_mul {A : Type} [CommRing A] [Algebra R A] (s t : specO R A ⟶ torus R r) (χ : Fin r → ℤ) :
    valA (s * t) χ = valA s χ * valA t χ := by
  rw [valA_eq, valA_eq, valA_eq, map_mul, MonoidHom.mul_apply, Units.val_mul, map_mul]

theorem valA_add {A : Type} [CommRing A] [Algebra R A] (t : specO R A ⟶ torus R r) (χ ψ : Fin r → ℤ) :
    valA t (χ + ψ) = valA t χ * valA t ψ := by
  rw [valA_eq, valA_eq, valA_eq, ofAdd_add, map_mul, Units.val_mul, map_mul]

theorem valA_injective {A : Type} [CommRing A] [Algebra R A] {s t : specO R A ⟶ torus R r}
    (h : ∀ χ, valA s χ = valA t χ) : s = t := by
  apply (GlobalTheory.splitTorusPointsEquiv _ _ _).injective
  refine MonoidHom.ext fun χ => Units.ext ?_
  have e := h χ.toAdd
  rw [valA_eq, valA_eq] at e
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective e

theorem valA_toUnit {A : Type} [CommRing A] [Algebra R A] (χ : Fin r → ℤ) :
    valA (toUnit (specO R A) ≫ η[torus R r]) χ = 1 := by
  rw [← Hom.one_def]; exact valA_one χ

theorem fst_val (x : LieG (torus R r)) (χ : Fin r → ℤ) : (valA x.1 χ).fst = 1 := by
  have h : valA (ptMap (TrivSqZeroExt.fstHom R R R) ≫ x.1) χ =
      valA (toUnit (specO R R) ≫ η[torus R r]) χ := congrArg (fun t => valA t χ) x.2
  rw [valA_comp, valA_toUnit] at h
  exact h

def dChar (x : LieG (torus R r)) : (Fin r → ℤ) →+ R where
  toFun χ := (valA x.1 χ).snd
  map_zero' := by
    have h := valA_add x.1 0 0
    rw [add_zero] at h
    have h2 := congrArg TrivSqZeroExt.snd h
    rw [DualNumber.snd_mul, fst_val] at h2
    simpa using h2
  map_add' χ ψ := by
    rw [valA_add, DualNumber.snd_mul, fst_val, fst_val, _root_.one_mul, _root_.mul_one, add_comm]

theorem lieCoord_eq (x : LieG (torus R r)) (i : Fin r) : lieCoord x i = dChar x (Pi.single i 1) := rfl

theorem dChar_apply (x : LieG (torus R r)) (χ : Fin r → ℤ) :
    dChar x χ = ∑ i, (χ i : R) * lieCoord x i := by
  conv_lhs => rw [← Finset.univ_sum_single χ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (χ i) : Fin r → ℤ) = χ i • Pi.single i 1 := by
    ext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
  rw [this, map_zsmul, zsmul_eq_mul, lieCoord_eq]

theorem val_eq_of_lieCoord (x : LieG (torus R r)) (χ : Fin r → ℤ) :
    valA x.1 χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (∑ i, (χ i : R) * lieCoord x i) := by
  ext
  · simp [fst_val]
  · rw [← dChar_apply]; simp [dChar]

def epsUnit : Multiplicative R →* (DualNumber R)ˣ where
  toFun a := ⟨TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr a.toAdd,
    TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (-a.toAdd), by ext <;> simp, by ext <;> simp⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [add_comm]

def linForm (c : Fin r → R) : (Fin r → ℤ) →+ R where
  toFun χ := ∑ i, (χ i : R) * c i
  map_zero' := by simp
  map_add' χ ψ := by simp [add_mul, Finset.sum_add_distrib]

def pt (c : Fin r → R) : specO R (DualNumber R) ⟶ torus R r :=
  (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom.toMonoidHom).comp
      (epsUnit.comp (AddMonoidHom.toMultiplicative (linForm c))))

theorem valA_pt (c : Fin r → R) (χ : Fin r → ℤ) :
    valA (pt c) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (linForm c χ) := by
  rw [valA_eq, pt, MulEquiv.apply_symm_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom _) = _
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

theorem pt_mem (c : Fin r → R) :
    ptMap (TrivSqZeroExt.fstHom R R R) ≫ pt c = toUnit (specO R R) ≫ η[torus R r] :=
  valA_injective fun χ => by
    rw [valA_comp, valA_toUnit, valA_pt]
    simp

theorem lieCoord_bijective_add_smul (R : Type) [CommRing R] (r : ℕ) :
    Function.Bijective (lieCoord : LieG (torus R r) → Fin r → R) ∧
      (∀ x y : LieG (torus R r), lieCoord (lieAdd _ x y) = lieCoord x + lieCoord y) ∧
      ∀ (a : R) (x : LieG (torus R r)), lieCoord (lieScale _ a x) = a • lieCoord x := by
  refine ⟨⟨fun x y h => ?_, fun c => ⟨⟨pt c, pt_mem c⟩, ?_⟩⟩, fun x y => ?_, fun a x => ?_⟩
  · refine Subtype.ext (valA_injective fun χ => ?_)
    rw [val_eq_of_lieCoord x, val_eq_of_lieCoord y, h]
  · funext i
    change (valA (pt c) (Pi.single i 1)).snd = c i
    rw [valA_pt]
    simp [linForm, Pi.single_apply]
  · funext i
    change (valA (x.1 * y.1) (Pi.single i 1)).snd = (valA x.1 (Pi.single i 1)).snd + (valA y.1 (Pi.single i 1)).snd
    rw [valA_mul, DualNumber.snd_mul, fst_val, fst_val, _root_.one_mul, _root_.mul_one, add_comm]
  · funext i
    change (valA (ptMap (dualScale a) ≫ x.1) (Pi.single i 1)).snd = a * (valA x.1 (Pi.single i 1)).snd
    rw [valA_comp]
    simp [dualScale]

end GlobalTheory.TorusLieCoord
