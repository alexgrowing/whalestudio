import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def IsFrameOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (T : ∀ k, Γ(X, W ⊓ L.U k)ˣ) : Prop :=
  ∀ k k', res (inf_le_left : W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ W ⊓ L.U k) (T k) =
    res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ L.U k ⊓ L.U k') (L.g k k') *
    res (inf_le_right : W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ W ⊓ L.U k') (T k')

def FrameCarried {X : Scheme.{0}} (L : LB X) (W : X.Opens) (T : ∀ k, Γ(X, W ⊓ L.U k)ˣ) (f : X ⟶ X)
    (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι), z ∈ W → f z ∈ W → z ∈ L.U k → f z ∈ L.U j →
    gm f z (W ⊓ L.U j) (T j) = gw w (𝟙 X) z j k * gm (𝟙 X) z (W ⊓ L.U k) (T k)

theorem gm_eq_map_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U h, Units.coe_map, gm_val (𝟙 X) (f y) U h]
  have := congrArg (fun q => q.hom a.val) (f.germ_stalkMap U y h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem FrameCarried.ratio_fixed {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {W W' O : X.Opens}
    {T : ∀ k, Γ(X, W ⊓ L.U k)ˣ} {T' : ∀ k, Γ(X, W' ⊓ L.U k)ˣ} {f : X ⟶ X} {w : LB.Iso L (L.pull f)}
    (hT : FrameCarried L W T f w) (hT' : FrameCarried L W' T' f w) (hOW : O ≤ W) (hOW' : O ≤ W') (r : Γ(X, O)ˣ)
    (hr : ∀ (z : X) (k : L.ι), z ∈ O → z ∈ L.U k →
      gm (𝟙 X) z O r = gm (𝟙 X) z _ (T' k) * (gm (𝟙 X) z _ (T k))⁻¹)
    (h : O ≤ f ⁻¹ᵁ O) : (f.appLE O O h).hom r.val = r.val := by
  apply TopCat.Presheaf.section_ext X.sheaf O
  intro x hx
  obtain ⟨k, hk⟩ := exists_chart hL x
  have hfx : f x ∈ O := h hx
  obtain ⟨j, hj⟩ := exists_chart hL (f x)
  have key : gm f x O r = gm (𝟙 X) x O r := by
    rw [gm_eq_map_gm f x O hfx, hr (f x) j hfx hj, map_mul, map_inv,
      ← gm_eq_map_gm f x (W' ⊓ L.U j) (show f x ∈ W' ⊓ L.U j from ⟨hOW' hfx, hj⟩),
      ← gm_eq_map_gm f x (W ⊓ L.U j) (show f x ∈ W ⊓ L.U j from ⟨hOW hfx, hj⟩),
      hT' x j k (hOW' hx) (hOW' hfx) hk hj, hT x j k (hOW hx) (hOW hfx) hk hj, hr x k hx hk, _root_.mul_inv,
      _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
  have e1 := congrArg Units.val key
  rw [gm_val f x O hfx, gm_val (𝟙 X) x O hx] at e1
  refine Eq.trans ?_ (e1.trans ?_)
  · simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ x hx _
  · rfl

end GlobalTheory.Mum
