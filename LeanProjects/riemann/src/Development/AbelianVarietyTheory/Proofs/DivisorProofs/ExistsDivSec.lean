import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRem
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatRatio

theorem exists_div_sec {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s a b : LB.Sec (LB.LinComb L φ ε)) (U : Y.Opens) (f : Γ(Y, U))
    (hs : ∀ z ∈ U, ∀ J, Good L z J → IsUnit (sval s (𝟙 Y) z J)) :
    ∃ g : Γ(Y, U), ∀ z ∈ U, ∀ J, Good L z J →
      sval a (𝟙 Y) z J = gs (𝟙 Y) z U f * sval b (𝟙 Y) z J + gs (𝟙 Y) z U g * sval s (𝟙 Y) z J := by
  have hun : ∀ (j : K → L.ι) (y : Y), y ∈ U → y ∈ LB.wchart L φ j →
      IsUnit (gs (𝟙 Y) y (LB.wchart L φ j) (s.f j)) := fun j y hU hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    rw [e]
    exact (Units.isUnit _).mul (hs y hU J hJ)
  let W : (K → L.ι) → Y.Opens := fun j => U ⊓ LB.wchart L φ j
  have hloc : ∀ j, ∃ u : Γ(Y, W j), ∀ y ∈ W j,
      gs (𝟙 Y) y (LB.wchart L φ j) (a.f j) = gs (𝟙 Y) y U f * gs (𝟙 Y) y (LB.wchart L φ j) (b.f j) +
        gs (𝟙 Y) y (W j) u * gs (𝟙 Y) y (LB.wchart L φ j) (s.f j) := by
    intro j
    have l₁ : W j ≤ U := inf_le_left
    have l₂ : W j ≤ LB.wchart L φ j := inf_le_right
    have hu : IsUnit ((Y.presheaf.map (homOfLE l₂).op).hom (s.f j)) :=
      Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
        (congrArg IsUnit ((gs_eq (𝟙 Y) y (W j) hy _).symm.trans (gs_res (𝟙 Y) y l₂ hy (s.f j)))).mpr
          (hun j y hy.1 hy.2)
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have key : (Y.presheaf.map (homOfLE l₂).op).hom (a.f j) =
        (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j) +
        (((Y.presheaf.map (homOfLE l₂).op).hom (a.f j) -
          (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j)) * v) *
          (Y.presheaf.map (homOfLE l₂).op).hom (s.f j) := by
      rw [_root_.mul_assoc, hv]; ring
    refine ⟨((Y.presheaf.map (homOfLE l₂).op).hom (a.f j) -
          (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j)) * v, fun y hy => ?_⟩
    refine (gs_res (𝟙 Y) y l₂ hy _).symm.trans ((congrArg (gs (𝟙 Y) y (W j)) key).trans ?_)
    refine (gs_add (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · exact (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 Y) y l₁ hy _) (gs_res (𝟙 Y) y l₂ hy _))
    · exact (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg _ (gs_res (𝟙 Y) y l₂ hy _))
  choose u hu using hloc
  obtain ⟨g, hg, -⟩ := Y.sheaf.existsUnique_gluing' W U (fun j => homOfLE inf_le_left) (fun y hy => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => I (φ k), hy, Set.mem_iInter.2 fun k => hI _⟩) u
    (fun j j' => fn_ext (V := W j ⊓ W j') fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      have e₁ := hu j y hy.1
      have e₂ := hu j' y hy.2
      rw [sec_trans a (𝟙 Y) y hy.1.2 hy.2.2, sec_trans b (𝟙 Y) y hy.1.2 hy.2.2,
        sec_trans s (𝟙 Y) y hy.1.2 hy.2.2] at e₁
      have hc := (Units.isUnit (trF φ ε (𝟙 Y) y j j')).mul (hun j' y hy.1.1 hy.2.2)
      refine hc.mul_right_cancel ?_
      linear_combination (trF φ ε (𝟙 Y) y j j').val * e₂ - e₁)
  refine ⟨g, fun z hz J hJ => ?_⟩
  have hm : z ∈ W (fun k => J (𝟙 Y ≫ φ k)) := ⟨hz, hJ.mem φ (𝟙 Y)⟩
  have e : gs (𝟙 Y) z U g = gs (𝟙 Y) z (W _) (u (fun k => J (𝟙 Y ≫ φ k))) :=
    (gs_res (𝟙 Y) z inf_le_left hm g).symm.trans (congrArg (gs (𝟙 Y) z (W _)) (hg _))
  rw [e]
  exact hu _ z hm

theorem exists_isRem : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (N : ℕ) (α : Q.X) (σ σ' σp σp' : Q.SecB N α) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)), GlobalTheory.HeatRatio.IsRatio Q σ σ' U f → ∃ g : Γ(Q.P.A.left, U), GlobalTheory.HeatRatio.IsRem Q σ' σp σp' U f g := by
  intro R _ _ Q N α σ σ' σp σp' U f h
  exact exists_div_sec Q.P.isLB σ' σp σp' U f fun z hz J hJ => (h z hz J hJ).1

end GlobalTheory.HeatRatio
