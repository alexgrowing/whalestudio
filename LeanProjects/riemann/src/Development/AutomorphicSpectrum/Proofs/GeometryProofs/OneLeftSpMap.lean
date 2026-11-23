import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

open GlobalTheory.HolHom

variable {R : Type} [CommRing R]

def cst {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem cst_apply {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) : cst p U a = constFn p U a := rfl

theorem valR_cst {C : Type} [CommRing C] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (θ : R →+* C)
    (y : Sp C ⟶ X) (hy : y ≫ p = spMap θ) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : R) : evalHom y U h (cst p U a) = θ a := by
  have e := GlobalTheory.TangentOrigin.evalPt_constFn p y U h a
  have e2 := GlobalTheory.TangentOrigin.evalPt_spMap θ a
  rw [hy] at e
  exact e.trans e2

theorem exists_pt {G : Over (Sp R)} {V : G.left.Opens} (hV : IsAffineOpen V) (θ : R →+* ℂ)
    (χ : Γ(G.left, V) →+* ℂ) (hχ : ∀ r, χ (cst G.hom V r) = θ r) :
    ∃ x : Over.mk (spMap θ) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V ∧ ∀ a, valAt' x.left V a = χ a := by
  obtain ⟨y, hy, he⟩ := GlobalTheory.TangentOrigin.exists_evalPt_eq hV χ
  have hy' : y ≫ G.hom = spMap θ := GlobalTheory.TangentOrigin.eq_spMap_of_evalPt _ θ (fun a => by
    rw [← GlobalTheory.TangentOrigin.evalPt_constFn G.hom y V hy a, he]; exact hχ a)
  refine ⟨Over.homMk y hy', hy, fun a => ?_⟩
  show valAt' y V a = χ a
  rw [GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ hy, he]

theorem val_cst {G : Over (Sp R)} (V : G.left.Opens) {θ : R →+* ℂ} (x : Over.mk (spMap θ) ⟶ G)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (r : R) : valAt' x.left V (cst G.hom V r) = θ r :=
  (GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ hx _).trans (valR_cst G.hom V θ x.left (Over.w x) hx r)

theorem pt_ext {G : Over (Sp R)} {V : G.left.Opens} (hV : IsAffineOpen V) {θ : R →+* ℂ}
    {x y : Over.mk (spMap θ) ⟶ G} (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V)
    (h : ∀ a, valAt' x.left V a = valAt' y.left V a) : x = y :=
  Over.OverMorphism.ext (point_ext hV hx hy h)

theorem tan_der {X : Scheme.{0}} {x : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) {V : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    ∃ D : Γ(X, V) →+ ℂ, (∀ f, D f = TrivSqZeroExt.snd (valR v V f)) ∧
      ∀ f f', D (f * f') = valAt' x V f * D f' + valAt' x V f' * D f := by
  have hv := (le_preimage_dual_iff h V).2 hx
  refine ⟨AddMonoidHom.mk' (fun f => TrivSqZeroExt.snd (valR v V f)) fun a b => ?_, fun _ => rfl, fun f f' => ?_⟩
  · simp only [valR_eq _ _ hv, map_add, TrivSqZeroExt.snd_add]
  · have e1 := fst_valR h hx f
    have e2 := fst_valR h hx f'
    simp only [AddMonoidHom.mk'_apply]
    rw [← e1, ← e2]
    simp only [valR_eq _ _ hv, map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

theorem one_left_spMap {G : Over (Sp R)} [GrpObj G] (θ : R →+* ℂ) :
    (1 : Over.mk (spMap θ) ⟶ G).left = spMap θ ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left := by
  have e : (Over.homMk (spMap θ) (by simp) : Over.mk (spMap θ) ⟶ Over.mk (𝟙 (Sp R))) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) = 1 := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  exact (congrArg (fun q => Over.Hom.left q) e).symm

theorem tan_base {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 (Sp R)) E) (θ : R →+* ℂ) (w : E) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (dualMap θ) ≫ (M.pt w).left) =
      (1 : Over.mk (spMap θ) ⟶ G).left := by
  rw [one_left_spMap, ← M.tan w, ← Category.assoc, ← Category.assoc]
  congr 1
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  show TrivSqZeroExt.fst (dualMap θ x) = θ (TrivSqZeroExt.fst x)
  simp [dualMap]

theorem tan_over {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 (Sp R)) E) (θ : R →+* ℂ) (w : E) :
    (spMap (dualMap θ) ≫ (M.pt w).left) ≫ G.hom = spMap ((algebraMap ℂ (DualNumber ℂ)).comp θ) := by
  have e : (M.pt w).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) := Over.w (M.pt w)
  rw [Category.assoc, e, Category.comp_id]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart
