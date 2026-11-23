import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.AbLocusPull

variable {X Y Z : Scheme.{0}}

theorem isUnit_gs_iff (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h a]
  show _ ↔ z ∈ r ⁻¹ᵁ X.basicOpen a
  rw [Scheme.preimage_basicOpen]
  exact (Scheme.mem_basicOpen Z ((r.app U) a) z h).symm

theorem glue_fn {κ : Type} (V : X.Opens) (O : κ → X.Opens) (hO : ∀ k, O k ≤ V)
    (hc : ∀ x ∈ V, ∃ k, x ∈ O k) (a : ∀ k, Γ(X, O k))
    (h : ∀ k l x, x ∈ O k → x ∈ O l → gs (𝟙 X) x (O k) (a k) = gs (𝟙 X) x (O l) (a l)) :
    ∃ b : Γ(X, V), ∀ x k, x ∈ O k → gs (𝟙 X) x V b = gs (𝟙 X) x (O k) (a k) := by
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf O a := by
    intro k l
    apply fn_ext
    intro x hx
    have e1 := gs_res (𝟙 X) x (inf_le_left : O k ⊓ O l ≤ O k) hx (a k)
    have e2 := gs_res (𝟙 X) x (inf_le_right : O k ⊓ O l ≤ O l) hx (a l)
    exact e1.trans ((h k l x hx.1 hx.2).trans e2.symm)
  have hcov : V ≤ iSup O := fun x hx => by
    obtain ⟨k, hk⟩ := hc x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' O V (fun k => homOfLE (hO k)) hcov a hcomp
  refine ⟨b, fun x k hx => ?_⟩
  rw [← gs_res (𝟙 X) x (hO k) hx b]
  exact congrArg (gs (𝟙 X) x (O k)) (hb k)

theorem gs_secOn {M : LB X} {V : X.Opens} {t : ∀ i, Γ(X, V ⊓ M.U i)} (ht : t ∈ secOn M V) (r : Z ⟶ X) (z : Z)
    (i j : M.ι) (hV : r z ∈ V) (hi : r z ∈ M.U i) (hj : r z ∈ M.U j) :
    gs r z _ (t i) = (gm r z (M.U i ⊓ M.U j) (M.g i j)).val * gs r z _ (t j) := by
  have hz : r z ∈ V ⊓ M.U i ⊓ M.U j := ⟨⟨hV, hi⟩, hj⟩
  have e := congrArg (gs r z (V ⊓ M.U i ⊓ M.U j)) (ht i j)
  dsimp only [resG] at e
  rw [gs_mul r z _ hz, gs_res r z _ hz, gs_res r z _ hz, gs_res r z _ hz, gs_unit r z _ (show r z ∈ M.U i ⊓ M.U j from ⟨hi, hj⟩)] at e
  exact e

private lemma toFld_gm_res {T : Scheme.{0}} {U V : T.Opens} (h : V ≤ U) (y : T) (hy : y ∈ V) (u : Γ(T, U)ˣ) :
    gm (𝟙 T) y V (res h u) = gm (𝟙 T) y U u :=
  Units.ext ((gs_unit (𝟙 T) y V hy (res h u)).symm.trans
    ((gs_res (𝟙 T) y h hy u.val).trans (gs_unit (𝟙 T) y U (h hy) u)))

private lemma gm_id_pull_g_eq_gm_comp {A B : Scheme.{0}} (L : LB A) (F : B ⟶ A) (x : B) (J J' : (L.pull F).ι)
    (h1 : x ∈ (L.pull F).U J) (h2 : x ∈ (L.pull F).U J') :
    gm (𝟙 B) x ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm F x (L.U (J ⟨⟩) ⊓ L.U (J' ⟨⟩)) (L.g (J ⟨⟩) (J' ⟨⟩)) := by
  have e := gm_linComb L (fun _ : PUnit => F) (fun _ => 1) (𝟙 B) x J J' h1 h2
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one, Category.id_comp] at e
  exact e

private lemma gm_id_div_g_eq_mul_inv {T : Scheme.{0}} (M N : LB T) (y : T) (p q : M.ι × N.ι)
    (hy : y ∈ (M.div N).U p ⊓ (M.div N).U q) :
    gm (𝟙 T) y ((M.div N).U p ⊓ (M.div N).U q) ((M.div N).g p q) =
      gm (𝟙 T) y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm (𝟙 T) y (N.U p.2 ⊓ N.U q.2) (N.g p.2 q.2))⁻¹ := by
  show gm (𝟙 T) y _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (toFld_gm_res _ y hy _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (toFld_gm_res _ y hy _))))

theorem exists_secOn_pull {X' : Scheme.{0}} {F : X' ⟶ X} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {W : X.Opens} {W' : X'.Opens} (hW : W' ≤ F ⁻¹ᵁ W) {θ : ∀ i, Γ(X, W ⊓ L.U i)}
    (hθ : θ ∈ secOn L W) :
    ∃ θ' ∈ secOn L' W', ∀ x ∈ W', ∀ j k, x ∈ L'.U k → F x ∈ X.basicOpen (θ j) → x ∈ X'.basicOpen (θ' k) := by
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨hcovL, -, -⟩ := hL
  obtain ⟨-, hself', -⟩ := hL'
  have m1 : ∀ (J : (L.pull F).ι) (y : X'), y ∈ (L.pull F).U J ↔ F y ∈ L.U (J ⟨⟩) := fun J y => by
    simp [LB.pull, LB.LinComb, LB.wchart]
    exact ⟨fun h => h _, fun h _ => h⟩
  have hchart : ∀ y : X, ∃ i, y ∈ L.U i := fun y => by
    have hy : y ∈ (⨆ i, L.U i) := by rw [hcovL]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  have hwrel : ∀ (x : X') (J J' : (L.pull F).ι) (k k' : L'.ι), x ∈ (L.pull F).U J ⊓ L'.U k →
      x ∈ (L.pull F).U J' ⊓ L'.U k' →
      gm (𝟙 X') x ((L.pull F).U J ⊓ L'.U k) (w.s (J, k)) =
        gm F x (L.U (J ⟨⟩) ⊓ L.U (J' ⟨⟩)) (L.g (J ⟨⟩) (J' ⟨⟩)) *
          (gm (𝟙 X') x (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ * gm (𝟙 X') x ((L.pull F).U J' ⊓ L'.U k') (w.s (J', k')) := by
    intro x J J' k k' h1 h2
    have h12 : x ∈ ((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k') := ⟨h1, h2⟩
    have e := congrArg (gm (𝟙 X') x (((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k')))
      (hwg (J, k) (J', k'))
    rw [map_mul, toFld_gm_res _ x h12, toFld_gm_res _ x h12, gm_id_div_g_eq_mul_inv (L.pull F) L' x (J, k) (J', k') h12,
      gm_id_pull_g_eq_gm_comp L F x J J' h1.1 h2.1] at e
    exact e
  have hone : ∀ k x, x ∈ L'.U k → gm (𝟙 X') x (L'.U k ⊓ L'.U k) (L'.g k k) = 1 := by
    intro k x hx
    have e := congrArg (gm (𝟙 X') x (L'.U k)) (hself' k)
    rwa [map_one, toFld_gm_res _ x hx] at e
  have hind : ∀ (x : X') (J J' : (L.pull F).ι) (k k' : L'.ι), x ∈ (L.pull F).U J ⊓ L'.U k →
      x ∈ (L.pull F).U J' ⊓ L'.U k' → F x ∈ W →
      gs F x (W ⊓ L.U (J ⟨⟩)) (θ (J ⟨⟩)) * ((gm (𝟙 X') x ((L.pull F).U J ⊓ L'.U k) (w.s (J, k)))⁻¹).val =
        (gm (𝟙 X') x (L'.U k ⊓ L'.U k') (L'.g k k')).val *
          (gs F x (W ⊓ L.U (J' ⟨⟩)) (θ (J' ⟨⟩)) *
            ((gm (𝟙 X') x ((L.pull F).U J' ⊓ L'.U k') (w.s (J', k')))⁻¹).val) := by
    intro x J J' k k' h1 h2 hxW
    rw [gs_secOn hθ F x (J ⟨⟩) (J' ⟨⟩) hxW ((m1 J x).1 h1.1) ((m1 J' x).1 h2.1), hwrel x J J' k k' h1 h2]
    simp only [mul_inv_rev, inv_inv, Units.val_mul]
    linear_combination (gs F x (W ⊓ L.U (J' ⟨⟩)) (θ (J' ⟨⟩)) *
      ((gm (𝟙 X') x ((L.pull F).U J' ⊓ L'.U k') (w.s (J', k')))⁻¹).val *
      (gm (𝟙 X') x (L'.U k ⊓ L'.U k') (L'.g k k')).val) *
      Units.mul_inv (gm F x (L.U (J ⟨⟩) ⊓ L.U (J' ⟨⟩)) (L.g (J ⟨⟩) (J' ⟨⟩)))
  have hOa : ∀ k J, W' ⊓ L'.U k ⊓ (L.pull F).U J ≤ F ⁻¹ᵁ (W ⊓ L.U (J ⟨⟩)) := fun k J x hx =>
    (show F x ∈ W ⊓ L.U (J ⟨⟩) from ⟨hW hx.1.1, (m1 J x).1 hx.2⟩)
  have hOb : ∀ k J, W' ⊓ L'.U k ⊓ (L.pull F).U J ≤ (L.pull F).U J ⊓ L'.U k := fun k J x hx =>
    (show x ∈ (L.pull F).U J ⊓ L'.U k from ⟨hx.2, hx.1.2⟩)
  obtain ⟨a, ha⟩ : ∃ a : ∀ k J, Γ(X', W' ⊓ L'.U k ⊓ (L.pull F).U J), ∀ k J, a k J =
      (X'.presheaf.map (homOfLE (hOa k J)).op).hom ((F.app (W ⊓ L.U (J ⟨⟩))).hom (θ (J ⟨⟩))) *
        ((res (hOb k J) (w.s (J, k)))⁻¹).val := ⟨_, fun _ _ => rfl⟩
  have hE : ∀ k J x (hx : x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U J),
      gs (𝟙 X') x _ (a k J) = gs F x (W ⊓ L.U (J ⟨⟩)) (θ (J ⟨⟩)) *
        ((gm (𝟙 X') x ((L.pull F).U J ⊓ L'.U k) (w.s (J, k)))⁻¹).val := by
    intro k J x hx
    rw [ha, gs_mul (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx, gs_pull (𝟙 X') F x _ (hOa k J hx), Category.id_comp,
      gs_unit (𝟙 X') x _ hx, map_inv, toFld_gm_res (hOb k J) x hx (w.s (J, k))]
  have hglue : ∀ k, ∃ b : Γ(X', W' ⊓ L'.U k), ∀ x J, x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U J →
      gs (𝟙 X') x (W' ⊓ L'.U k) b = gs (𝟙 X') x _ (a k J) := by
    intro k
    obtain ⟨b, hb⟩ := glue_fn (W' ⊓ L'.U k) (fun J => W' ⊓ L'.U k ⊓ (L.pull F).U J) (fun J => inf_le_left)
      (fun x hx => by
        obtain ⟨i, hi⟩ := hchart (F x)
        exact ⟨fun _ => i, (show x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U (fun _ => i) from ⟨hx, (m1 _ x).2 hi⟩)⟩)
      (a k) (fun J J' x hx hx' => by
        rw [hE k J x hx, hE k J' x hx', hind x J J' k k ⟨hx.2, hx.1.2⟩ ⟨hx'.2, hx'.1.2⟩ (hW hx.1.1),
          hone k x hx.1.2, Units.val_one, _root_.one_mul])
    exact ⟨b, fun x J hx => hb x J hx⟩
  choose θ' hθ' using hglue
  refine ⟨θ', ?_, ?_⟩
  · intro k k'
    apply fn_ext
    intro x hx
    dsimp only [resG]
    rw [gs_mul (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx,
      gs_unit (𝟙 X') x _ (show x ∈ L'.U k ⊓ L'.U k' from ⟨hx.1.2, hx.2⟩)]
    obtain ⟨i, hi⟩ := hchart (F x)
    have hx1 : x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U (fun _ => i) := ⟨hx.1, (m1 _ x).2 hi⟩
    have hx2 : x ∈ W' ⊓ L'.U k' ⊓ (L.pull F).U (fun _ => i) := ⟨⟨hx.1.1, hx.2⟩, (m1 _ x).2 hi⟩
    rw [hθ' k x _ hx1, hθ' k' x _ hx2, hE k _ x hx1, hE k' _ x hx2]
    exact hind x _ _ k k' ⟨hx1.2, hx1.1.2⟩ ⟨hx2.2, hx2.1.2⟩ (hW hx.1.1)
  · intro x hxW j k hk hj
    have hFj : F x ∈ W ⊓ L.U j := Scheme.basicOpen_le X (θ j) hj
    have hx1 : x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U (fun _ => j) := ⟨⟨hxW, hk⟩, (m1 _ x).2 hFj.2⟩
    have hu : IsUnit (gs (𝟙 X') x (W' ⊓ L'.U k) (θ' k)) := by
      rw [hθ' k x _ hx1, hE k _ x hx1]
      exact ((isUnit_gs_iff F x _ hFj (θ j)).2 hj).mul (Units.isUnit _)
    exact (isUnit_gs_iff (𝟙 X') x (W' ⊓ L'.U k) ⟨hxW, hk⟩ (θ' k)).1 hu

theorem isProper_restrict_pull {S S' X' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {t : S' ⟶ S} {F : X' ⟶ X}
    (h : IsPullback F p' p t) (U : S.Opens) [IsProper (p ∣_ U)] : IsProper (p' ∣_ (t ⁻¹ᵁ U)) := by
  have e0 : F ⁻¹ᵁ (p ⁻¹ᵁ U) = p' ⁻¹ᵁ (t ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
  have hUY : p' ⁻¹ᵁ (t ⁻¹ᵁ U) = F ⁻¹ᵁ (p ⁻¹ᵁ U) ⊓ p' ⁻¹ᵁ (t ⁻¹ᵁ U) := by rw [e0, inf_idem]
  have sq := Scheme.Hom.isPullback_resLE h (le_refl (t ⁻¹ᵁ U)) (le_refl (p ⁻¹ᵁ U)) hUY
  have hp : IsProper (p.resLE U (p ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  have hq := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) sq hp
  rwa [Scheme.Hom.resLE_eq_morphismRestrict] at hq

theorem abLocus_sections_pull : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G f φ → ((∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)) → (∃ U : X'.Opens, (U : Set X') = abLocus G' ∧ IsProper (G'.hom ∣_ U))) ∧ ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)) → (∀ x : X', ∃ V : X'.Opens, x ∈ V ∧ ∃ θ ∈ secOn L' (G'.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G'.left) (i : L'.ι), G'.hom g = y ∧ g ∈ G'.left.basicOpen (θ i)) := by
  intro X X' f G _ G' _ φ hG hp
  refine ⟨?_, ?_⟩
  · rintro ⟨U, hU, hUp⟩
    refine ⟨f ⁻¹ᵁ U, ?_, ?_⟩
    · ext x
      change f x ∈ (U : Set X) ↔ x ∈ abLocus G'
      rw [hU]
      exact abLocus_pullback abLocusOne hG hp.1 x
    · have := hUp
      exact isProper_restrict_pull hp.1 U
  · intro L L' hL hL' hw hsec x
    obtain ⟨V, hxV, θ, hθ, hV⟩ := hsec (f x)
    have hW : G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V) ≤ φ ⁻¹ᵁ (G.hom ⁻¹ᵁ V) := by
      intro g hg
      show G.hom (φ g) ∈ V
      rw [← Scheme.Hom.comp_apply, hp.1.w, Scheme.Hom.comp_apply]
      exact hg
    obtain ⟨θ', hθ', hnz⟩ := exists_secOn_pull hL hL' hw hW hθ
    refine ⟨f ⁻¹ᵁ V, hxV, θ', hθ', fun y hy => ?_⟩
    obtain ⟨g, i, hg, hgi⟩ := hV (f y) hy
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := f) g y hg
    have e1 : φ (hp.1.isoPullback.inv z) = g := by
      rw [← Scheme.Hom.comp_apply, hp.1.isoPullback_inv_fst, hz1]
    have e2 : G'.hom (hp.1.isoPullback.inv z) = y := by
      rw [← Scheme.Hom.comp_apply, hp.1.isoPullback_inv_snd, hz2]
    obtain ⟨hcov', -, -⟩ := hL'
    obtain ⟨k, hk⟩ : ∃ k, hp.1.isoPullback.inv z ∈ L'.U k := by
      have hm : hp.1.isoPullback.inv z ∈ (⨆ i, L'.U i) := by rw [hcov']; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 hm
    refine ⟨hp.1.isoPullback.inv z, k, e2, hnz _ ?_ i k hk ?_⟩
    · show G'.hom (hp.1.isoPullback.inv z) ∈ f ⁻¹ᵁ V
      rw [e2]; exact hy
    · rw [e1]; exact hgi

end GlobalTheory.AbLocusPull
