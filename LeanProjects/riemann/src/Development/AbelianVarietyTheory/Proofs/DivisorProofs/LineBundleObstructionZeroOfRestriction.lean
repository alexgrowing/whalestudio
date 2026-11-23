import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsObUNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResPullURes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsSquareZeroPresentedScheme
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObsZero

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

def PCh (P : S.Presents s i) (L : LB X) : Type :=
  {p : X₀.affineOpens × L.ι // GlobalTheory.PresCharts.chartOpen P (Opposite.op p.1) ≤ L.U p.2}

instance (P : S.Presents s i) (L : LB X) : Preorder (PCh P L) := Preorder.lift fun p ↦ OrderDual.toDual p.1.1.1

def pG (P : S.Presents s i) (L : LB X) : PCh P L ⥤ AffOp X₀ where
  obj p := Opposite.op p.1.1
  map a := (homOfLE (leOfHom a)).op

theorem isAffineOpen_chartOpen (P : S.Presents s i) (T : AffOp X₀) :
    IsAffineOpen (GlobalTheory.PresCharts.chartOpen P T) := by
  haveI := P.isOpen T
  unfold GlobalTheory.PresCharts.chartOpen
  exact isAffineOpen_opensRange _

def pH (P : S.Presents s i) (L : LB X) : PCh P L ⥤ GlobalTheory.LBObs.Model.Ch L where
  obj p := ⟨(⟨GlobalTheory.PresCharts.chartOpen P (Opposite.op p.1.1), isAffineOpen_chartOpen P _⟩, p.1.2), p.2⟩
  map {p q} a := homOfLE (GlobalTheory.PresCharts.chartOpen_le P ((pG P L).map a))

theorem isBas_pG (hI : I ^ 2 = 0) (P : S.Presents s i) {L : LB X} (hL : L.IsLB) : IsBas (opOf (pG P L)) := by
  have k : ∀ (x : X₀) (U : X₀.Opens), x ∈ U → ∃ t : PCh P L, x ∈ opOf (pG P L) t ∧ opOf (pG P L) t ≤ U :=
    fun x U hx ↦ by
      obtain ⟨m, hm⟩ := LB.mem_of_cover hL (i x)
      obtain ⟨_, ⟨W, hW, rfl⟩, h1, h2⟩ :=
        X₀.isBasis_affineOpens.exists_subset_of_mem_open
          (show x ∈ ((U ⊓ i ⁻¹ᵁ L.U m : X₀.Opens) : Set X₀) from ⟨hx, hm⟩) (U ⊓ i ⁻¹ᵁ L.U m).isOpen
      refine ⟨⟨(⟨W, hW⟩, m), fun y hy ↦ ?_⟩, h1, fun y hy ↦ (h2 hy).1⟩
      obtain ⟨y₀, hy₀, rfl⟩ := GlobalTheory.PresCharts.exists_of_mem_chartOpen hI P _ y hy
      exact (h2 hy₀).2
  refine ⟨k, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  obtain ⟨t, h1, h2⟩ := k x (opOf (pG P L) t₁ ⊓ opOf (pG P L) t₂ ⊓ U) ⟨⟨h₁, h₂⟩, hx⟩
  exact ⟨t, ⟨homOfLE (h2.trans (inf_le_left.trans inf_le_left))⟩, ⟨homOfLE (h2.trans (inf_le_left.trans inf_le_right))⟩,
    h1, h2.trans inf_le_right⟩

end GlobalTheory.LBObsZero

open GlobalTheory.LBObsZero in

theorem GlobalTheory.LBObs.isObL_pull_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L : LB X), IsPullback i s₀ s (spMap π) → L.IsLB → IsObL S α (L.pull i) 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S X s i P L h hL
  have hH : ∀ T : PCh P L, opOf (pG P L) T ≤ i ⁻¹ᵁ opOf (GlobalTheory.LBObs.Model.chG L) ((pH P L).obj T) :=
    fun T ↦ GlobalTheory.PresCharts.le_preimage_chartOpen P _
  let w : ∀ (T T' : GlobalTheory.LBObs.Model.Ch L) (_ : T ⟶ T'), Γ(X, opOf (GlobalTheory.LBObs.Model.chG L) T')ˣ :=
    fun T T' a ↦ res (le_inf T'.2 ((opOf_le (GlobalTheory.LBObs.Model.chG L) a).trans T.2)) (L.g T'.1.2 T.1.2)
  have hw : IsFrame L _ _ w := GlobalTheory.LBObs.Model.isFrame_ch hL
  have hfr := isFrame_pull X _ _ _ L w X₀ i (PCh P L) (opOf (pG P L)) (opOf_le (pG P L)) (pH P L) hH hw
  have hcoc := GlobalTheory.LBObs.Model.isCoc_of_isFrame hL hw
  choose σ hσ using fun T ↦ GlobalTheory.Obs.Model.exists_isSig hI hπ α (((ofSys S).restrict (pG P L)).p T)
    (Pre.semi _ T) (Pre.surj _ T) (Pre.ker _ T)
  refine ⟨PCh P L, inferInstance, inferInstance, pG P L, isBas_pG hI P hL, _, hfr, ?_⟩
  rw [map_zero]
  refine ⟨fun T T' a ↦ Units.map (GlobalTheory.PresCharts.chartSec P ((pG P L).obj T')).hom.toMonoidHom (w _ _ ((pH P L).map a)),
    σ, 0, fun T T' a ↦ ?_, hσ, (map_zero _).symm, fun T T' T'' a b ↦ ⟨map_zero _, ?_⟩⟩
  · have := congrArg (fun f ↦ f.hom (w _ _ ((pH P L).map a)).val)
      (GlobalTheory.PresCharts.appLE_chartSec P ((pG P L).obj T') (hH T'))
    exact this.symm
  · have e0 : (0 : Z2 (ext R₁ ((pG P L) ⋙ OAff s₀))).1 T T' T'' a b = 0 := rfl
    rw [e0, map_zero, add_zero, _root_.one_mul]
    have e1 := hcoc ((pH P L).map a) ((pH P L).map b)
    rw [← Functor.map_comp] at e1
    have e2 := congrArg (fun f ↦ f.hom (w _ _ ((pH P L).map a)).val)
      (GlobalTheory.PresCharts.res_chartSec P ((pG P L).map b))
    show (mp S.F ((pG P L).map b)) ((GlobalTheory.PresCharts.chartSec P ((pG P L).obj T')).hom (w _ _ ((pH P L).map a)).val) *
        (GlobalTheory.PresCharts.chartSec P ((pG P L).obj T'')).hom (w _ _ ((pH P L).map b)).val =
      (GlobalTheory.PresCharts.chartSec P ((pG P L).obj T'')).hom (w _ _ ((pH P L).map (a ≫ b))).val
    rw [e1, Units.val_mul]
    erw [map_mul]
    congr 1
    exact e2.symm
