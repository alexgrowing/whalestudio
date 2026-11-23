import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KerAb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} {φ : Fib k} {m : CubeMap φ.G t.G}

theorem isTanAtG_push (hF : FibAt t x φ m) {w : epsR k ⟶ φ.G} (hw : IsTangent w) :
    Formalism.L2.Pj.IsTanAtG t x (w.left ≫ m.F) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hF.1.1.w, ← Category.assoc, Over.w w]
    rfl
  · have h1 := Formalism.L2.Pj.grpPull_one hF.1 (𝟙_ (Over (Sp k)))
    have h2 : (𝟙_ (Over (Sp k))).hom ≫ x = x := Category.id_comp x
    rw [← Category.assoc, hw]
    rw [h2] at h1
    rw [h1]
    congr 1

theorem isTangent_of_push (hF : FibAt t x φ m) {w' : epsR k ⟶ φ.G} {w : TanM x t.G}
    (h : w'.left ≫ m.F = (tv w).left) : IsTangent w' := by
  have h1 := Formalism.L2.Pj.grpPull_one hF.1 (𝟙_ (Over (Sp k)))
  have h2 : (𝟙_ (Over (Sp k))).hom ≫ x = x := Category.id_comp x
  rw [h2] at h1
  refine hF.1.1.hom_ext ?_ ?_
  · rw [Category.assoc, h, (isTan_tv w).2, h1]
    congr 1
  · rw [Category.assoc, Over.w w', Over.w]
    exact GlobalTheory.Diag.fstHom_base

theorem isTangent_comp {G G' : Over (Sp k)} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f] {w : epsR k ⟶ G}
    (hw : IsTangent w) : IsTangent (w ≫ f) := by
  unfold IsTangent at hw ⊢
  rw [Over.comp_left, ← Category.assoc, hw, ← Over.comp_left, IsMonHom.one_hom]

theorem eq_one_of_isLieComb_zero {G : Over (Sp k)} [GrpObj G] {n : ℕ} {v : Fin n → (epsR k ⟶ G)}
    (hv : ∀ i, IsTangent (v i)) {w : epsR k ⟶ G} (h : IsLieComb 0 v w) : w = 1 := by
  obtain ⟨u, hu, rfl⟩ := h
  have e : spMap (epsScaleR (0 : k)) =
      spMap (algebraMap k (DualNumber k)) ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by
      ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]))
  have h1 : u = fun _ => 1 := funext fun i => Over.OverMorphism.ext (by
    rw [hu i, Pi.zero_apply, e, Category.assoc, hv i]
    rfl)
  rw [h1]
  simp

def torL (hF : FibAt t x φ m) : (φ.X →+ k) →ₗ[k] TanM x t.G :=
  haveI := φ.i_hom
  { toFun := fun c => tanOf (isTanAtG_push hF (isTangent_comp φ.i (GlobalTheory.Diag.isTangent_lieVec c)))
    map_add' := fun c d => tan_ext (by
      rw [left_tanOf, GlobalTheory.Diag.lieVec_add, MonObj.mul_comp, tv_add]
      exact (hF.1.2 (epsR k) _ _ _ _ rfl rfl).symm)
    map_smul' := fun a c => tan_ext (by
      rw [left_tanOf, Over.comp_left, GlobalTheory.Diag.lieVec_smul_left, Category.assoc, Category.assoc]
      rfl) }

theorem left_torL (hF : FibAt t x φ m) (c : φ.X →+ k) :
    (tv (torL hF c)).left = (GlobalTheory.Diag.lieVec c ≫ φ.i).left ≫ m.F := rfl

theorem ker_le_range (hF : FibAt t x φ m) {n : ℕ} {v : Fin n → (epsR k ⟶ φ.P.A)} (hv : IsLieBasis v)
    {q : TanM x t.G →ₗ[k] (Fin n → k)} (hq : IsAbMap φ m v q) : LinearMap.ker q ≤ LinearMap.range (torL hF) := by
  intro w hw
  haveI := φ.i_hom
  obtain ⟨w', h1, h2⟩ := hq w
  rw [LinearMap.mem_ker.1 hw] at h2
  have h3 : w' ≫ φ.q = toUnit _ ≫ η[φ.P.A] := eq_one_of_isLieComb_zero hv.1 h2
  have hl : φ.isKernel.lift _ _ h3 ≫ φ.i = w' := φ.isKernel.lift_fst _ _ h3
  let e₀ : 𝟙_ (Over (Sp k)) ⟶ epsR k :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) GlobalTheory.Diag.fstHom_base
  have h4 : e₀ ≫ φ.isKernel.lift _ _ h3 = η[splitTorus (Sp k) φ.X] := by
    refine φ.isKernel.hom_ext ?_ (toUnit_unique _ _)
    rw [Category.assoc, hl, IsMonHom.one_hom]
    exact Over.OverMorphism.ext (isTangent_of_push hF h1)
  obtain ⟨c, hc⟩ := (GlobalTheory.Diag.isTangent_iff_exists (φ.isKernel.lift _ _ h3)).1 (congrArg Over.Hom.left h4)
  exact ⟨c, tan_ext (by rw [left_torL, hc, hl, h1])⟩

theorem ker_le_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G), FibAt t x φ m → ∀ (n : ℕ) (v : Fin n → (epsR k ⟶ φ.P.A)), IsLieBasis v → ∀ q : TanM x t.G →ₗ[k] (Fin n → k), IsAbMap φ m v q → ∃ s : Fin (Module.finrank ℤ φ.X) → TanM x t.G, LinearMap.ker q ≤ Submodule.span k (Set.range s) := by
  intro E _ _ _ H X t k _ x φ m hF n v hv q hq
  let b := GlobalTheory.Diag.dualBasis k (Module.finBasis ℤ φ.X)
  refine ⟨fun j => torL hF (b j), (ker_le_range hF hv hq).trans ?_⟩
  rintro _ ⟨c, rfl⟩
  rw [← b.sum_repr c, map_sum]
  exact Submodule.sum_mem _ fun j _ => by
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.KerAb

end
