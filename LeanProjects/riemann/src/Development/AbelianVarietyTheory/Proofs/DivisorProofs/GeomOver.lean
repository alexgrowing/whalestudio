import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SectionOfFreeOnUnitComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.CovChar

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def constMor (Y : Scheme.{0}) (a : R) : (freeOn R).obj Y ⟶ coef R :=
  (sectionOf R Y (coef R)).symm
    ((toSheafify Scheme.proetaleTopology.{0} (coefPre R)).app (op Y) (ULift.up (ContinuousMap.const Y a)))

variable {R} {X Y : Scheme.{0}} (f : Y ⟶ X)

abbrev kerSc : ShortComplex (Shv R) :=
  ShortComplex.mk (kernel.ι ((freeOn R).map f)) ((freeOn R).map f) (kernel.condition _)

def CharRel {G : Type} (t : G → (Y ⟶ Y)) (x : H R 1 X) (c : G → R) : Prop :=
  ∃ (hS : (kerSc (R := R) f).ShortExact) (h : kernel ((freeOn R).map f) ⟶ coef R),
    (x : HS R (coef R) 1 X) = hS.extClass.comp (Abelian.Ext.mk₀ h) (add_zero 1) ∧
    ∀ (g : G) (k : (freeOn R).obj Y ⟶ kernel ((freeOn R).map f)),
      k ≫ kernel.ι _ = (freeOn R).map (t g) - 𝟙 _ → k ≫ h = constMor R Y (c g)

end GlobalTheory.Et.CovChar

namespace GlobalTheory.AV.AbVar

open ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K]

abbrev torsPts (A : AbVar K) (n : ℕ) : Subgroup A.Pt := (powMonoidHom n).ker

abbrev geomX (A : AbVar K) : Scheme.{0} := GlobalTheory.Et.geom (AlgebraicClosure K) A.X.hom

def mulGeom (A : AbVar K) (n : ℕ) : geomX A ⟶ geomX A :=
  GlobalTheory.Et.geomMap (AlgebraicClosure K) A.X.hom (n • 𝟙 A : A ⟶ A).hom.left (Over.w _)

abbrev geomOver (A : AbVar K) : Over (Sp K) :=
  Over.mk (pullback.fst A.X.hom (spMap (algebraMap K (AlgebraicClosure K))) ≫ A.X.hom)

def transl (A : AbVar K) (a : A.Pt) : geomX A ⟶ geomX A :=
  pullback.lift
    ((lift (Over.homMk (pullback.fst _ _) : geomOver A ⟶ A.X)
      (Over.homMk (pullback.snd _ _ ≫ a.left) (by
        rw [Category.assoc, Over.w a]; exact pullback.condition.symm) : geomOver A ⟶ A.X) ≫ μ[A.X]).left)
    (pullback.snd _ _) (by
      rw [Over.w]; exact pullback.condition)

def levT {l : ℕ} (A : AbVar K) (t : Tl l A) (m : ℕ) : torsPts A (l ^ m) :=
  ⟨t.lev m, (MonoidHom.mem_ker).2 (by rw [powMonoidHom_apply]; exact GlobalTheory.HTLat.Tate.lev_pow t m)⟩

end GlobalTheory.AV.AbVar
