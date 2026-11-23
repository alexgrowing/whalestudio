import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.DisjointCoverLB

theorem gm_imageUnit {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsOpenImmersion ι] (V : Z.Opens) (v : Γ(Z, V)ˣ) (z : Z)
    (hz : z ∈ V) :
    gm ι z (ι ''ᵁ V) (GlobalTheory.ExtendLineBundle.imageUnit ι V v) = gm (𝟙 Z) z V v := by
  have hz' : ι z ∈ ι ''ᵁ V := ι.apply_mem_image_iff.2 hz
  apply Units.ext
  rw [gm_val ι z _ hz', gm_val (𝟙 Z) z V hz]
  have e := congrArg (fun q => q.hom v.val) (ι.appIso_inv_app V)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  change (Z.presheaf.germ _ z _).hom ((ι.app _).hom ((ι.appIso V).inv.hom v.val)) = _
  rw [e]
  exact TopCat.Presheaf.germ_res_apply Z.presheaf _ z _ _

theorem units_eq_of_gm {X : Scheme.{0}} {V : X.Opens} {a b : Γ(X, V)ˣ}
    (h : ∀ x ∈ V, ∃ (Z : Scheme.{0}) (ι : Z ⟶ X) (_ : IsOpenImmersion ι) (z : Z), ι z = x ∧ gm ι z V a = gm ι z V b) :
    a = b := by
  refine unit_ext fun x hx => ?_
  obtain ⟨Z, ι, hι, z, rfl, e⟩ := h x hx
  have e' := congrArg Units.val e
  rw [gm_val ι z V hx, gm_val ι z V hx, ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e'
  have key := (ConcreteCategory.bijective_of_isIso (ι.stalkMap z)).1 e'
  apply Units.ext
  rw [gm_val (𝟙 X) (ι z) V hx, gm_val (𝟙 X) (ι z) V hx]
  exact key

end GlobalTheory.DisjointCoverLB

namespace GlobalTheory.DisjointCoverLB

theorem lbIso_of_disjoint_cover : ∀ (Y : Scheme.{0}) (A : Type) (W : A → Y.Opens), (∀ a b y, y ∈ W a → y ∈ W b → a = b) →
    (∀ y, ∃ a, y ∈ W a) → ∀ (P Q : LB Y), P.IsLB → Q.IsLB → (∀ a, LBIso (P.pull (W a).ι) (Q.pull (W a).ι)) →
    LBIso P Q := by
  intro Y A W hdisj hcov P Q hP hQ hw
  choose w hwg using hw
  have hmemC : ∀ a (c : Q.ι × P.ι) (y : W a), (W a).ι y ∈ (LB.div Q P).U c →
      y ∈ (LB.div (Q.pull (W a).ι) (P.pull (W a).ι)).U (fun _ => c.1, fun _ => c.2) :=
    fun a c y hy => ⟨mem_pull.2 hy.1, mem_pull.2 hy.2⟩
  have hpt : ∀ a (x : Y) (hx : x ∈ W a), ∃ y : W a, (W a).ι y = x := fun a x hx => ⟨⟨x, hx⟩, rfl⟩
  have hin : ∀ a (y : W a), (W a).ι y ∈ W a := fun a y => y.2
  have hle : ∀ a (c : Q.ι × P.ι), (LB.div Q P).U c ⊓ W a ≤
      (W a).ι ''ᵁ (LB.div (Q.pull (W a).ι) (P.pull (W a).ι)).U (fun _ => c.1, fun _ => c.2) := by
    intro a c x hx
    obtain ⟨y, rfl⟩ := hpt a x hx.2
    exact (W a).ι.apply_mem_image_iff.2 (hmemC a c y hx.1)
  let u : ∀ (c : Q.ι × P.ι) a, Γ(Y, (LB.div Q P).U c ⊓ W a)ˣ := fun c a =>
    res (hle a c) (GlobalTheory.ExtendLineBundle.imageUnit (W a).ι _ ((w a).s (fun _ => c.1, fun _ => c.2)))
  have glue : ∀ c : Q.ι × P.ι, ∃ s : Γ(Y, (LB.div Q P).U c)ˣ,
      ∀ a, res (inf_le_left : (LB.div Q P).U c ⊓ W a ≤ _) s = u c a := fun c =>
    glue_unit _ (fun a => (LB.div Q P).U c ⊓ W a) (fun a => inf_le_left)
      (fun x hx => by obtain ⟨a, ha⟩ := hcov x; exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hx, ha⟩) (u c)
      (fun a b x hx => by obtain rfl := hdisj a b x hx.1.2 hx.2.2; rfl)
  choose s hs using glue
  have key : ∀ (c : Q.ι × P.ι) a (y : W a), (W a).ι y ∈ (LB.div Q P).U c →
      gm (W a).ι y ((LB.div Q P).U c) (s c) = gw (w a) (𝟙 _) y c.1 (fun _ => c.2) := by
    intro c a y hy
    have hyW : (W a).ι y ∈ (LB.div Q P).U c ⊓ W a := ⟨hy, hin a y⟩
    calc gm (W a).ι y ((LB.div Q P).U c) (s c) = gm (W a).ι y _ (res (inf_le_left : (LB.div Q P).U c ⊓ W a ≤ _) (s c)) :=
          (gm_res (W a).ι y inf_le_left hyW _).symm
      _ = gm (W a).ι y _ (u c a) := by rw [hs c a]
      _ = gm (W a).ι y _ (GlobalTheory.ExtendLineBundle.imageUnit (W a).ι _ ((w a).s (fun _ => c.1, fun _ => c.2))) :=
          by show gm (W a).ι y _ (res (hle a c) _) = _; exact gm_res (W a).ι y (hle a c) hyW _
      _ = gm (𝟙 _) y _ ((w a).s (fun _ => c.1, fun _ => c.2)) := by
          exact gm_imageUnit (W a).ι _ ((w a).s (fun _ => c.1, fun _ => c.2)) y (hmemC a c y hy)
  refine ⟨⟨s⟩, fun c c' => units_eq_of_gm fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := hcov x
  obtain ⟨y, rfl⟩ := hpt a x ha
  refine ⟨W a, (W a).ι, inferInstance, y, rfl, ?_⟩
  have h1 : (W a).ι y ∈ (LB.div Q P).U c := hx.1
  have h2 : (W a).ι y ∈ (LB.div Q P).U c' := hx.2
  have pg := (isGen_iff (w a)).1 (hwg a) (W a) (𝟙 _) y c.1 c'.1 (fun _ => c.2) (fun _ => c'.2) h1.1 h2.1
    (mem_pull.2 h1.2) (mem_pull.2 h2.2)
  rw [gm_pull_g P (W a).ι (𝟙 _) y _ _ (mem_pull.2 h1.2) (mem_pull.2 h2.2), Category.id_comp] at pg
  dsimp only
  refine (gm_res (W a).ι y _ hx _).trans ?_
  rw [key c a y h1]
  refine pg.trans ?_
  refine Eq.trans ?_ (map_mul _ _ _).symm
  exact congrArg₂ (· * ·) (gm_div P Q (W a).ι y c c' hx).symm
    ((gm_res (W a).ι y _ hx _).trans (key c' a y h2)).symm

end GlobalTheory.DisjointCoverLB
