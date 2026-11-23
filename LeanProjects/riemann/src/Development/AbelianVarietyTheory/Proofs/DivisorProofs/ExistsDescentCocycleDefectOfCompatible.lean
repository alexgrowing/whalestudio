import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescDefect

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

theorem compat_gm {L : LB X} {φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ} (hC : DescCompat f L φ)
    {T : Scheme.{0}} (s : T ⟶ pullback f f) (t : T) (i i' j j' : L.ι)
    (hi : pullback.fst f f (s t) ∈ L.U i) (hi' : pullback.fst f f (s t) ∈ L.U i')
    (hj : pullback.snd f f (s t) ∈ L.U j) (hj' : pullback.snd f f (s t) ∈ L.U j') :
    gm s t _ (φ i' j') =
      gm (s ≫ pullback.fst f f) t _ (L.g i i') * gm s t _ (φ i j) * gm (s ≫ pullback.snd f f) t _ (L.g j' j) := by
  have l₁ : chart f L i j ⊓ chart f L i' j' ≤ pullback.fst f f ⁻¹ᵁ (L.U i ⊓ L.U i') :=
    fun z hz => ⟨hz.1.1, hz.2.1⟩
  have l₂ : chart f L i j ⊓ chart f L i' j' ≤ pullback.snd f f ⁻¹ᵁ (L.U j' ⊓ L.U j) :=
    fun z hz => ⟨hz.2.2, hz.1.2⟩
  have hO : res (inf_le_right : chart f L i j ⊓ chart f L i' j' ≤ _) (φ i' j') =
      res l₁ (pullU (pullback.fst f f) _ (L.g i i')) * res inf_le_left (φ i j) *
        res l₂ (pullU (pullback.snd f f) _ (L.g j' j)) := by
    apply unit_ext
    intro z hz
    rw [map_mul, map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz,
      gm_pull (𝟙 _) (pullback.fst f f) z _ (l₁ hz) _, gm_pull (𝟙 _) (pullback.snd f f) z _ (l₂ hz) _,
      Category.id_comp, Category.id_comp]
    exact hC z i i' j j' hz.1.1 hz.2.1 hz.1.2 hz.2.2
  have hst : s t ∈ chart f L i j ⊓ chart f L i' j' := ⟨⟨hi, hj⟩, ⟨hi', hj'⟩⟩
  have e := congrArg (gm s t (chart f L i j ⊓ chart f L i' j')) hO
  rw [map_mul, map_mul, gm_res _ t _ hst, gm_res _ t _ hst, gm_res _ t _ hst, gm_res _ t _ hst,
    gm_pull s (pullback.fst f f) t _ (l₁ hst) _, gm_pull s (pullback.snd f f) t _ (l₂ hst) _] at e
  exact e

theorem defect_exists : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ),
    L.IsLB → DescCompat f L φ → ∃ D : Γ(Triple f, ⊤)ˣ, Defect f L φ D := by
  intro X Y f L φ hL hC
  set a := pullback.fst (pullback.snd f f) (pullback.fst f f) with ha
  set b := pullback.snd (pullback.snd f f) (pullback.fst f f) with hb
  have hab : a ≫ pullback.snd f f = b ≫ pullback.fst f f := pullback.condition
  have hca : pr13 f ≫ pullback.fst f f = a ≫ pullback.fst f f := pullback.lift_fst _ _ _
  have hcb : pr13 f ≫ pullback.snd f f = b ≫ pullback.snd f f := pullback.lift_snd _ _ _
  have pab : ∀ x, pullback.snd f f (a x) = pullback.fst f f (b x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hab
    simpa only [Scheme.Hom.comp_apply] using this
  have pca : ∀ x, pullback.fst f f (pr13 f x) = pullback.fst f f (a x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hca
    simpa only [Scheme.Hom.comp_apply] using this
  have pcb : ∀ x, pullback.snd f f (pr13 f x) = pullback.snd f f (b x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hcb
    simpa only [Scheme.Hom.comp_apply] using this

  have K : ∀ (T : Scheme.{0}) (s : T ⟶ Triple f) (t : T) (i j k i' j' k' : L.ι),
      pullback.fst f f (a (s t)) ∈ L.U i → pullback.fst f f (a (s t)) ∈ L.U i' →
      pullback.snd f f (a (s t)) ∈ L.U j → pullback.snd f f (a (s t)) ∈ L.U j' →
      pullback.snd f f (b (s t)) ∈ L.U k → pullback.snd f f (b (s t)) ∈ L.U k' →
      gm (s ≫ a) t _ (φ i j) * gm (s ≫ b) t _ (φ j k) * (gm (s ≫ pr13 f) t _ (φ i k))⁻¹ =
        gm (s ≫ a) t _ (φ i' j') * gm (s ≫ b) t _ (φ j' k') * (gm (s ≫ pr13 f) t _ (φ i' k'))⁻¹ := by
    intro T s t i j k i' j' k' hi hi' hj hj' hk hk'
    have hjb : pullback.fst f f (b (s t)) ∈ L.U j := pab (s t) ▸ hj
    have hjb' : pullback.fst f f (b (s t)) ∈ L.U j' := pab (s t) ▸ hj'
    have hic : pullback.fst f f (pr13 f (s t)) ∈ L.U i := (pca (s t)).symm ▸ hi
    have hic' : pullback.fst f f (pr13 f (s t)) ∈ L.U i' := (pca (s t)).symm ▸ hi'
    have hkc : pullback.snd f f (pr13 f (s t)) ∈ L.U k := (pcb (s t)).symm ▸ hk
    have hkc' : pullback.snd f f (pr13 f (s t)) ∈ L.U k' := (pcb (s t)).symm ▸ hk'
    have E1 := compat_gm f hC (s ≫ a) t i i' j j' hi hi' hj hj'
    have E2 := compat_gm f hC (s ≫ b) t j j' k k' hjb hjb' hk hk'
    have E3 := compat_gm f hC (s ≫ pr13 f) t i i' k k' hic hic' hkc hkc'
    have hc := gm_cocycle hL (s ≫ b ≫ pullback.fst f f) t (i := j') (j := j) (k := j') hjb' hjb hjb'
    rw [gm_self hL _ t hjb'] at hc
    simp only [Category.assoc] at E1 E2 E3
    rw [hca, hcb] at E3
    rw [hab] at E1
    rw [E1, E2, E3]
    generalize gm (s ≫ b ≫ pullback.fst f f) t _ (L.g j' j) = G2 at hc ⊢
    generalize gm (s ≫ b ≫ pullback.fst f f) t _ (L.g j j') = G3 at hc ⊢
    have : G3 = G2⁻¹ := eq_inv_of_mul_eq_one_right hc
    subst this
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  let V : L.ι × L.ι × L.ι → (Triple f).Opens := fun p =>
    a ⁻¹ᵁ chart f L p.1 p.2.1 ⊓ b ⁻¹ᵁ chart f L p.2.1 p.2.2 ⊓ pr13 f ⁻¹ᵁ chart f L p.1 p.2.2
  have la : ∀ p, V p ≤ a ⁻¹ᵁ chart f L p.1 p.2.1 := fun p => inf_le_left.trans inf_le_left
  have lb : ∀ p, V p ≤ b ⁻¹ᵁ chart f L p.2.1 p.2.2 := fun p => inf_le_left.trans inf_le_right
  have lc : ∀ p, V p ≤ pr13 f ⁻¹ᵁ chart f L p.1 p.2.2 := fun p => inf_le_right
  have memV : ∀ (x : Triple f) (i j k : L.ι), pullback.fst f f (a x) ∈ L.U i → pullback.snd f f (a x) ∈ L.U j →
      pullback.snd f f (b x) ∈ L.U k → x ∈ V (i, j, k) := fun x i j k hi hj hk =>
    ⟨⟨⟨hi, hj⟩, ⟨(show pullback.fst f f (b x) ∈ L.U j from pab x ▸ hj), hk⟩⟩,
      ⟨(show pullback.fst f f (pr13 f x) ∈ L.U i from (pca x).symm ▸ hi),
        (show pullback.snd f f (pr13 f x) ∈ L.U k from (pcb x).symm ▸ hk)⟩⟩
  let u : ∀ p, Γ(Triple f, V p)ˣ := fun p =>
    res (la p) (pullU a _ (φ p.1 p.2.1)) * res (lb p) (pullU b _ (φ p.2.1 p.2.2)) *
      (res (lc p) (pullU (pr13 f) _ (φ p.1 p.2.2)))⁻¹
  have hu : ∀ (T : Scheme.{0}) (s : T ⟶ Triple f) (t : T) (p : L.ι × L.ι × L.ι), s t ∈ V p →
      gm s t (V p) (u p) = gm (s ≫ a) t _ (φ p.1 p.2.1) * gm (s ≫ b) t _ (φ p.2.1 p.2.2) *
        (gm (s ≫ pr13 f) t _ (φ p.1 p.2.2))⁻¹ := by
    intro T s t p hp
    simp only [u, map_mul, map_inv]
    rw [gm_res _ t _ hp, gm_res _ t _ hp, gm_res _ t _ hp, gm_pull s a t _ (la p hp) _,
      gm_pull s b t _ (lb p hp) _, gm_pull s (pr13 f) t _ (lc p hp) _]
  obtain ⟨D, hD⟩ := glue_unit ⊤ V (fun _ => le_top) (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (a x))
      obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (a x))
      obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (b x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j, k), memV x i j k hi hj hk⟩) u (fun p p' x hx => by
      rw [hu _ (𝟙 _) x p hx.1, hu _ (𝟙 _) x p' hx.2]
      exact K _ (𝟙 _) x _ _ _ _ _ _ hx.1.1.1.1 hx.2.1.1.1 hx.1.1.1.2 hx.2.1.1.2 hx.1.1.2.2 hx.2.1.2.2)
  refine ⟨D, fun T r t i j k hi hj hk => ?_⟩
  have hm := memV (r t) i j k hi hj hk
  rw [← gm_res r t (fun _ _ => trivial : V (i, j, k) ≤ ⊤) hm D, hD (i, j, k), hu T r t (i, j, k) hm]
  exact inv_mul_cancel_right _ _

end GlobalTheory.DescDefect
