import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBGlue

variable {R : Type} [CommRing R] {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

abbrev UU (t : (Small i L)ᵒᵖ) : X.Opens := t.unop.1.1.1

theorem le_of_hom {t t' : (Small i L)ᵒᵖ} (a : t ⟶ t') : UU t' ≤ UU t := leOfHom a.unop

theorem hom_eq {t t' : (Small i L)ᵒᵖ} (a b : t ⟶ t') : a = b :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def homOf {t t' : (Small i L)ᵒᵖ} (h : UU t' ≤ UU t) : t ⟶ t' :=
  (homOfLE (show t'.unop ≤ t.unop from h)).op

variable (u : C1 (smallG i L ⋙ OAff s)) (hu : ∀ t t' a, IsUnit (u t t' a))

def uu (t t' : (Small i L)ᵒᵖ) (a : t ⟶ t') : Γ(X, UU t')ˣ := (hu t t' a).unit

variable {u hu}

theorem uu_comp (hm : mdef _ u = 0) {t t' t'' : (Small i L)ᵒᵖ} (a : t ⟶ t') (b : t' ⟶ t'') :
    res (le_of_hom b) (uu u hu t t' a) * uu u hu t' t'' b = uu u hu t t'' (a ≫ b) := by
  apply Units.ext
  have := congrFun (congrFun (congrFun (congrFun (congrFun hm t) t') t'') a) b
  exact sub_eq_zero.1 this

theorem gm_uu (hm : mdef _ u = 0) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {t t' r : (Small i L)ᵒᵖ}
    (a : t ⟶ t') (b : t' ⟶ r) (hy : f y ∈ UU r) :
    gm f y (UU t') (uu u hu t t' a) =
      gm f y (UU r) (uu u hu t r (a ≫ b)) * (gm f y (UU r) (uu u hu t' r b))⁻¹ := by
  rw [← uu_comp hm a b, map_mul, gm_res f y _ hy, mul_inv_cancel_right]

theorem exists_g (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) (t t' : (Small i L)ᵒᵖ) :
    ∃ g : Γ(X, UU t ⊓ UU t')ˣ, ∀ p : (r : (Small i L)ᵒᵖ) × (t ⟶ r) × (t' ⟶ r),
      res (le_inf (le_of_hom p.2.1) (le_of_hom p.2.2)) g = uu u hu t p.1 p.2.1 * (uu u hu t' p.1 p.2.2)⁻¹ := by
  refine glue_unit _ (fun p : (r : (Small i L)ᵒᵖ) × (t ⟶ r) × (t' ⟶ r) ↦ UU p.1)
    (fun p ↦ le_inf (le_of_hom p.2.1) (le_of_hom p.2.2)) (fun x hx ↦ ?_) _ (fun p q x hx ↦ ?_)
  · obtain ⟨r, hr, hle⟩ := hB.cover x _ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r, homOf (hle.trans inf_le_left), homOf (hle.trans inf_le_right)⟩, hr⟩
  · obtain ⟨r, hr, hle⟩ := hB.cover x _ hx
    have c : p.1 ⟶ r := homOf (hle.trans inf_le_left)
    have d : q.1 ⟶ r := homOf (hle.trans inf_le_right)
    rw [map_mul, map_mul, map_inv, map_inv, gm_uu hm (𝟙 X) x p.2.1 c hr, gm_uu hm (𝟙 X) x p.2.2 c hr,
      gm_uu hm (𝟙 X) x q.2.1 d hr, gm_uu hm (𝟙 X) x q.2.2 d hr, hom_eq (q.2.1 ≫ d) (p.2.1 ≫ c),
      hom_eq (q.2.2 ≫ d) (p.2.2 ≫ c)]
    group

variable (u hu)

def glueLB (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) : LB X :=
  ⟨(Small i L)ᵒᵖ, UU, fun t t' ↦ Classical.choose (exists_g (hu := hu) hm hB t t')⟩

variable {u hu}

theorem gm_glue (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y)
    {t t' r : (Small i L)ᵒᵖ} (a : t ⟶ r) (b : t' ⟶ r) (hy : f y ∈ UU r) :
    gm f y (UU t ⊓ UU t') ((glueLB u hu hm hB).g t t') =
      gm f y (UU r) (uu u hu t r a) * (gm f y (UU r) (uu u hu t' r b))⁻¹ := by
  have := Classical.choose_spec (exists_g (hu := hu) hm hB t t') ⟨r, a, b⟩
  show gm f y _ (Classical.choose (exists_g (hu := hu) hm hB t t')) = _
  rw [← gm_res f y (le_inf (le_of_hom a) (le_of_hom b)) hy, this, map_mul, map_inv]

theorem isLB_glue (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) : (glueLB u hu hm hB).IsLB where
  cover := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨r, hr, -⟩ := hB.cover x ⊤ trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨r, hr⟩
  g_self := fun (t : (Small i L)ᵒᵖ) ↦ by
    refine unit_ext fun x hx ↦ ?_
    obtain ⟨r, hr, hle⟩ := hB.cover x (UU t) hx
    rw [gm_res _ x _ hx, map_one]
    exact (gm_glue hm hB (𝟙 X) x (homOf hle) (homOf hle) hr).trans (mul_inv_cancel _)
  cocycle := fun (t t' t'' : (Small i L)ᵒᵖ) ↦ by
    refine unit_ext fun x hx ↦ ?_
    obtain ⟨r, hr, hle⟩ := hB.cover x (UU t ⊓ UU t' ⊓ UU t'') hx
    have a : t ⟶ r := homOf (hle.trans (inf_le_left.trans inf_le_left))
    have b : t' ⟶ r := homOf (hle.trans (inf_le_left.trans inf_le_right))
    have c : t'' ⟶ r := homOf (hle.trans inf_le_right)
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    refine (congrArg₂ (· * ·) (gm_glue hm hB (𝟙 X) x a b hr) (gm_glue hm hB (𝟙 X) x b c hr)).trans
      ((?_ : _ = _).trans (gm_glue hm hB (𝟙 X) x a c hr).symm)
    group

theorem gm_lift (hl : IsLift s i L u) {t r : (Small i L)ᵒᵖ} (a : t ⟶ r) (y : X₀) (hy : i y ∈ UU r) :
    gm i y (UU r) (uu u hu t r a) = gm (𝟙 X₀) y _ (L.g t.unop.1.2 r.unop.1.2) := by
  have e := gm_pull (𝟙 X₀) i y (UU r) hy (uu u hu t r a)
  rw [Category.id_comp] at e
  have e' : pullU i (UU r) (uu u hu t r a) = res (Small.le_inf a) (L.g t.unop.1.2 r.unop.1.2) :=
    Units.ext (hl t r a)
  rw [← e, e', gm_res (𝟙 X₀) y _ hy]

def chart (hL : L.IsLB) (hl : IsLift s i L u) (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) :
    ChartPull ((glueLB u hu hm hB).pull i) L (𝟙 X₀) where
  idx J := (J PUnit.unit).unop.1.2
  le J y hy := (J PUnit.unit).unop.2 (mem_pull.1 hy)
  g y J J' hj hj' := by
    have hx : i y ∈ UU (J PUnit.unit) := mem_pull.1 hj
    have hx' : i y ∈ UU (J' PUnit.unit) := mem_pull.1 hj'
    obtain ⟨r, hr, hle⟩ := hB.cover (i y) (UU (J PUnit.unit) ⊓ UU (J' PUnit.unit)) ⟨hx, hx'⟩
    let t₁ : (Small i L)ᵒᵖ := J PUnit.unit
    let t₂ : (Small i L)ᵒᵖ := J' PUnit.unit
    have a : t₁ ⟶ r := homOf (hle.trans inf_le_left)
    have b : t₂ ⟶ r := homOf (hle.trans inf_le_right)
    have e := gm_pull_g (glueLB u hu hm hB) i (𝟙 X₀) y J J' hj hj'
    rw [Category.id_comp] at e
    refine e.trans ((gm_glue hm hB i y a b hr).trans ?_)
    rw [gm_lift hl a y hr, gm_lift hl b y hr]
    have hjr : (𝟙 X₀) y ∈ L.U r.unop.1.2 := r.unop.2 hr
    have hj₁ : (𝟙 X₀) y ∈ L.U (J PUnit.unit).unop.1.2 := (J PUnit.unit).unop.2 hx
    have hj₂ : (𝟙 X₀) y ∈ L.U (J' PUnit.unit).unop.1.2 := (J' PUnit.unit).unop.2 hx'
    rw [← gm_cocycle hL (𝟙 X₀) y hj₁ hj₂ hjr, mul_inv_cancel_right]

end GlobalTheory.LBGlue

open GlobalTheory.LBGlue in

theorem GlobalTheory.LBLift.exists_pic_of_strict_lift : ∀ (R : Type) [CommRing R] (X X₀ : Scheme.{0}) (s : X ⟶ Sp R)
    (i : X₀ ⟶ X) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsBasis (smallG i L) →
    IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) → mdef _ u = 0 →
    ∃ c : Pic X, GlobalTheory.CechPic.pull i c = cls L hL := by
  intro R _ X X₀ s i L hL u hB hl hu hm
  refine ⟨cls _ (isLB_glue (hu := hu) hm hB), ?_⟩
  rw [← cls_pull (isLB_glue (hu := hu) hm hB) i (pull_isLB (isLB_glue (hu := hu) hm hB) i)]
  exact (cls_eq_iff _ hL).2 (iso_of_chart hL (chart hL hl hm hB))
