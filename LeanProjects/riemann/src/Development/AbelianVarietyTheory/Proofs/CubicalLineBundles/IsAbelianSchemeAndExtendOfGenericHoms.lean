import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeOfGenericallySurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isIso_toUnit_splitTorus_punit (S : Scheme.{0}) : IsIso (toUnit (splitTorus S PUnit)) := by
  have h : 𝟙 (splitTorus S PUnit) = 1 := by
    rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
    congr 1
  exact ⟨η, h.symm, toUnit_unique _ _⟩

theorem isAbelianScheme_pullback_obj {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) where
  comm := by have := h.comm; infer_instance
  smooth := by have := h.smooth; change Smooth (pullback.snd A.hom f); infer_instance
  proper := by have := h.proper; change IsProper (pullback.snd A.hom f); infer_instance
  geomConnected := by
    have := h.geomConnected; change GeometricallyConnected (pullback.snd A.hom f); infer_instance

noncomputable def torusExtensionOfAbelian {K : Type} [Field K] (A : Over (Spec (.of K))) [GrpObj A]
    (h : IsAbelianScheme A) : TorusExtension A where
  X := PUnit
  B := A
  isAbelian := h
  q := 𝟙 A
  q_hom := inferInstance
  q_flat := by rw [Over.id_left]; infer_instance
  q_surjective := by rw [Over.id_left]; infer_instance
  q_quasiCompact := by rw [Over.id_left]; infer_instance
  i := toUnit _ ≫ η
  i_hom := by have := h.comm; infer_instance
  isKernel := by
    have := isIso_toUnit_splitTorus_punit (Spec (.of K))
    exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩

theorem isSemiAbelian_of_isAbelianScheme {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsSemiAbelian A where
  comm := h.comm
  smooth := h.smooth
  separated := by have := h.proper; infer_instance
  quasiCompact := by have := h.proper; infer_instance
  geomConnected := h.geomConnected
  fibres := fun _ _ _ p => ⟨torusExtensionOfAbelian _ (isAbelianScheme_pullback_obj p A h)⟩

theorem isAbelianScheme_powObj_of_isAbelianScheme {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : ∀ n, IsAbelianScheme (Out.powObj A n)
  | 0 => Diag.isAbelianScheme_unit S
  | n + 1 => AbelianSchemeGerms.isAbelianScheme_powObj A h n

theorem comp_list_prod_ofFn {S : Scheme.{0}} {T T' G : Over S} [MonObj G] (t : T' ⟶ T) :
    ∀ {n : ℕ} (u : Fin n → (T ⟶ G)), t ≫ (List.ofFn u).prod = (List.ofFn fun i => t ≫ u i).prod
  | 0, u => by simp
  | n + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul,
      comp_list_prod_ofFn t]

theorem isTangent_comp_of_isMonHom {R : Type} [CommRing R] {B G : Over (Sp R)} [GrpObj B] [GrpObj G]
    (Φ : B ⟶ G) [IsMonHom Φ] (v : epsR R ⟶ B) (hv : IsTangent v) : IsTangent (v ≫ Φ) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

end GlobalTheory
