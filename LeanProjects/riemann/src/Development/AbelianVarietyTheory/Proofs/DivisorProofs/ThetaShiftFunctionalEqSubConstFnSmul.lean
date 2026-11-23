import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorFieldZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HeatMod

section Values

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

def germConstHom (q : Z ⟶ Sp R) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_id_scal_eq_germConstHom (q : Z ⟶ Sp R) (z : Z) (a : R) :
    gs (𝟙 Z) z ⊤ (scal q a) = germConstHom q z a := by
  rw [gs_eq (𝟙 Z) z ⊤ trivial]; rfl

theorem gs_constFn_eq_germConstHom (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (constFn p ⊤ a) = germConstHom (r ≫ p) z a := by
  have : constFn p ⊤ a = (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := by
    unfold constFn
    rw [← Scheme.Hom.appLE_eq_app]; rfl
  exact (congrArg (gs r z ⊤) this).trans ((gs_eq r z ⊤ trivial _).trans rfl)

theorem sval_sub_constFn_smul {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Sp R)
    (s s' : LB.Sec (LB.LinComb L φ ε)) (a : R) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (s' - constFn p ⊤ a • s) r z J = sval s' r z J - germConstHom (r ≫ p) z a * sval s r z J := by
  have hm := hJ.mem φ r
  have h₁ : sval (s' - constFn p ⊤ a • s) r z J + sval (constFn p ⊤ a • s) r z J = sval s' r z J :=
    (gs_add r z _ hm _ _).symm.trans (congrArg (gs r z _) (sub_add_cancel _ _))
  have h₂ : sval (constFn p ⊤ a • s) r z J = germConstHom (r ≫ p) z a * sval s r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z le_top hm _).trans (gs_constFn_eq_germConstHom p r z a)) rfl)
  rw [← h₁, h₂, add_sub_cancel_right]

end Values

theorem shiftEq_of_sub_constFn_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)) (c e e₁ : R), ShiftEq Q k mu α σ σ₁ 0 σ₁ → ShiftEq Q k mu α (σ' - constFn Q.P.A.hom ⊤ e • σ) (σ₁' - constFn Q.P.A.hom ⊤ e₁ • σ₁) c σ₁ → ShiftEq Q k mu α σ' σ₁' (c + e₁ - e) σ₁ := by
  intro R _ _ Q k mu α σ σ' σ₁ σ₁' c e e₁ h₀ h₁ u hu hc z J hJ
  have a₀ := h₀ u hu hc z J hJ
  have a₁ := h₁ u hu hc z J hJ
  rw [sval_sub_constFn_smul _ _ _ _ _ _ hJ, sval_sub_constFn_smul _ _ _ _ _ _ hJ, Over.w, Over.w,
    gs_id_scal_eq_germConstHom] at a₁
  rw [gs_id_scal_eq_germConstHom, map_zero, zero_mul, add_zero] at a₀
  rw [gs_id_scal_eq_germConstHom, map_sub, map_add]
  linear_combination a₁ + germConstHom (DegPre.BF Q (FractionRing R)).hom z e * a₀

end GlobalTheory.HeatMod
