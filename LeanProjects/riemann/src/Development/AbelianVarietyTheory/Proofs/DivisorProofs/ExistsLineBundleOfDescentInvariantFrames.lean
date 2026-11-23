import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfGeneratorFpqcDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false

namespace GlobalTheory.LBDescent

private theorem ratio_eq {G : Type} [CommGroup G] (A B C D g : G) (h1 : A = g * B) (h2 : C = g * D) :
    C * A⁻¹ = D * B⁻¹ := by
  subst h1 h2; rw [mul_inv_rev, mul_comm g D, _root_.mul_assoc, mul_inv_cancel_comm_assoc]

private theorem ratio_mul {G : Type} [CommGroup G] (A B C : G) : (B * A⁻¹) * (C * B⁻¹) = C * A⁻¹ := by
  rw [mul_comm (B * A⁻¹), _root_.mul_assoc, inv_mul_cancel_left]

private theorem ratio_inv {G : Type} [CommGroup G] (A S g T : G) (h : S = g * T) :
    A⁻¹ = S * A⁻¹ * g⁻¹ * T⁻¹ := by
  rw [_root_.mul_assoc _ g⁻¹, ← mul_inv, ← h, mul_inv_cancel_comm]

theorem exists_lb_of_invariant_frames : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [Flat f] [Surjective f] (L : LB X), L.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ),
    (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j)) →
    ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  intro X Y f _ _ _ L hL φ H
  choose V hV s hs1 hs2 using H
  have hW : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ (V a ⊓ V b) := fun a b i => inf_le_left
  have lb : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ V b ⊓ L.U i := fun a b i x hx => ⟨hx.1.2, hx.2⟩
  have la : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ V a ⊓ L.U i := fun a b i x hx => ⟨hx.1.1, hx.2⟩
  have hex : ∀ a b, ∃ t : Γ(X, f ⁻¹ᵁ (V a ⊓ V b))ˣ, ∀ i,
      res (hW a b i) t = res (lb a b i) (s b i) * (res (la a b i) (s a i))⁻¹ := by
    intro a b
    refine glue_unit _ _ (hW a b) ?_ _ ?_
    · intro x hx
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, hi⟩
    · intro i j x hx
      simp only [map_mul, map_inv]
      rw [gm_res _ x (lb a b i) hx.1, gm_res _ x (la a b i) hx.1, gm_res _ x (lb a b j) hx.2,
        gm_res _ x (la a b j) hx.2]
      exact ratio_eq _ _ _ _ _ (hs1 a i j x hx.1.1.1 hx.1.2 hx.2.2) (hs1 b i j x hx.1.1.2 hx.1.2 hx.2.2)
  choose t ht using hex
  have tform : ∀ a b {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) (i : L.ι), f (g z) ∈ V a → f (g z) ∈ V b →
      g z ∈ L.U i → gm g z _ (t a b) = gm g z _ (s b i) * (gm g z _ (s a i))⁻¹ := by
    intro a b Z g z i ha hb hi
    have hm : g z ∈ f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i := ⟨⟨ha, hb⟩, hi⟩
    rw [← gm_res g z (hW a b i) hm, ht a b i, map_mul, map_inv, gm_res g z (lb a b i) hm,
      gm_res g z (la a b i) hm]
  have hk : ∀ a b, ∃ k : Γ(Y, V a ⊓ V b)ˣ, pullU f _ k = t a b := by
    intro a b
    refine GlobalTheory.FlatDescent.exists_unit_of_gm_eq f (IsPullback.of_hasPullback f f) _ _ fun z hz => ?_
    obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f z)
    obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f z)
    have e : f (pullback.snd f f z) = f (pullback.fst f f z) :=
      congrArg (fun q : pullback f f ⟶ Y => q z) pullback.condition.symm
    rw [tform a b _ z i hz.1 hz.2 hi, tform a b _ z j (e ▸ hz.1) (e ▸ hz.2) hj,
      ← hs2 a z i j hz.1 hi hj, ← hs2 b z i j hz.2 hi hj]
    group
  choose k hk using hk
  have kform : ∀ a b (x : X) (i : L.ι), f x ∈ V a → f x ∈ V b → x ∈ L.U i →
      gm f x (V a ⊓ V b) (k a b) = gm (𝟙 X) x _ (s b i) * (gm (𝟙 X) x _ (s a i))⁻¹ := by
    intro a b x i ha hb hi
    have := gm_pull (𝟙 X) f x (V a ⊓ V b) ⟨ha, hb⟩ (k a b)
    rw [Category.id_comp, hk] at this
    rw [← this]
    exact tform a b (𝟙 X) x i ha hb hi
  have hL' : LB.IsLB (⟨Y, V, k⟩ : LB Y) := by
    refine ⟨?_, fun a => ?_, fun a b c => ?_⟩
    · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hV y⟩
    · refine GlobalTheory.FlatDescent.unit_ext_of_flat f fun x hx => ?_
      obtain ⟨i, hi⟩ := exists_chart hL x
      rw [gm_res f x _ hx, map_one]
      exact (kform a a x i hx hx hi).trans (mul_inv_cancel _)
    · refine GlobalTheory.FlatDescent.unit_ext_of_flat f fun x hx => ?_
      obtain ⟨i, hi⟩ := exists_chart hL x
      rw [map_mul, gm_res f x _ hx, gm_res f x _ hx, gm_res f x _ hx]
      exact ((congrArg₂ (· * ·) (kform a b x i hx.1.1 hx.1.2 hi) (kform b c x i hx.1.2 hx.2 hi)).trans
        (ratio_mul _ _ _)).trans (kform a c x i hx.1.1 hx.2 hi).symm
  have le1 : ∀ (J : PUnit → Y) (i : L.ι), ((⟨Y, V, k⟩ : LB Y).pull f).U J ⊓ L.U i ≤ f ⁻¹ᵁ V (J PUnit.unit) ⊓ L.U i :=
    fun J i x hx => ⟨mem_pull.1 hx.1, hx.2⟩
  refine ⟨⟨Y, V, k⟩, hL', ⟨fun p => (res (le1 p.1 p.2) (s (p.1 PUnit.unit) p.2))⁻¹⟩, ?_⟩
  rintro ⟨J, i⟩ ⟨J', i'⟩
  apply unit_ext
  intro x hx
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have d := gm_div_g (L := (⟨Y, V, k⟩ : LB Y)) (L' := L) (F := f) (𝟙 X) x (J PUnit.unit) (J' PUnit.unit) i i'
    hj hj' hx.1.2 hx.2.2
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx]
  erw [d]
  erw [map_inv, map_inv, gm_res (𝟙 X) x (le1 J i) (show x ∈ ((⟨Y, V, k⟩ : LB Y).pull f).U J ⊓ L.U i from hx.1),
    gm_res (𝟙 X) x (le1 J' i') (show x ∈ ((⟨Y, V, k⟩ : LB Y).pull f).U J' ⊓ L.U i' from hx.2)]
  rw [Category.id_comp]
  erw [kform (J PUnit.unit) (J' PUnit.unit) x i hj hj' hx.1.2]
  exact ratio_inv _ _ _ _ (hs1 (J' PUnit.unit) i i' x hj' hx.1.2 hx.2.2)
end GlobalTheory.LBDescent
