import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum.LBDesc

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull unit_ext glue_unit exists_chart gw PGen)

variable {Z Y : Scheme.{0}}

def toZ (V : Z.Opens) {O : V.toScheme.Opens} (a : Γ(V.toScheme, O)ˣ) : Γ(Z, V.ι ''ᵁ O)ˣ := a

theorem toZ_res (V : Z.Opens) {O O' : V.toScheme.Opens} (h : O' ≤ O) (a : Γ(V.toScheme, O)ˣ) :
    toZ V (res h a) = res (V.ι.image_mono h) (toZ V a) := rfl

theorem toZ_mul (V : Z.Opens) {O : V.toScheme.Opens} (a b : Γ(V.toScheme, O)ˣ) :
    toZ V (a * b) = toZ V a * toZ V b := rfl

theorem image_preimage_le' (V : Z.Opens) (O : Z.Opens) : V.ι ''ᵁ V.ι ⁻¹ᵁ O ≤ O :=
  Set.image_preimage_subset _ _

theorem toZ_pullU (V : Z.Opens) (O : Z.Opens) (a : Γ(Z, O)ˣ) :
    toZ V (pullU V.ι O a) = res (image_preimage_le' V O) a := rfl

theorem res_toZ_pullU (V : Z.Opens) (O : Z.Opens) {W : Z.Opens} (hW : W ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ O) (a : Γ(Z, O)ˣ) :
    res hW (toZ V (pullU V.ι O a)) = res (hW.trans (image_preimage_le' V O)) a := by
  rw [toZ_pullU, LB.res_res]

theorem transport (L' : LB Z) (V : Z.Opens) (t : LB.Gen (L'.pull V.ι)) (ht : t.IsGen) :
    ∃ T : ∀ k : L'.ι, Γ(Z, V ⊓ L'.U k)ˣ, ∀ k k',
      res (inf_le_left : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k) (T k) =
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k') *
        res (inf_le_right : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k') (T k') := by
  have hle : ∀ k, V ⊓ L'.U k ≤ V.ι ''ᵁ LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k) := by
    intro k z hz
    exact ⟨⟨z, hz.1⟩, Set.mem_iInter.2 fun _ => hz.2, rfl⟩
  refine ⟨fun k => res (hle k) (toZ V (LB.ts t (fun _ => k))), fun k k' => ?_⟩
  have hle2 : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V.ι ''ᵁ (LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k) ⊓
      LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k')) := fun z hz =>
    ⟨⟨z, hz.1.1⟩, ⟨Set.mem_iInter.2 fun _ => hz.1.2, Set.mem_iInter.2 fun _ => hz.2.2⟩, rfl⟩
  have e := congrArg (fun x => res hle2 (toZ V x)) ((LB.isGen_iff L' t).1 ht (fun _ => k) (fun _ => k'))
  simp only [toZ_mul, toZ_res, map_mul, LB.res_res, LB.lcg, Fintype.prod_unique, zpow_one, res_toZ_pullU] at e
  simp only [LB.res_res]
  exact e

theorem gm_compat (L' : LB Z) (V : Z.Opens) (T : ∀ k : L'.ι, Γ(Z, V ⊓ L'.U k)ˣ)
    (hT : ∀ k k', res (inf_le_left : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k) (T k) =
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k') *
        res (inf_le_right : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k') (T k'))
    {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι) (hV : f w ∈ V) (hk : f w ∈ L'.U k)
    (hk' : f w ∈ L'.U k') :
    gm f w (V ⊓ L'.U k) (T k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w (V ⊓ L'.U k') (T k') := by
  have hm : f w ∈ V ⊓ L'.U k ⊓ (V ⊓ L'.U k') := ⟨⟨hV, hk⟩, hV, hk'⟩
  have e := congrArg (gm f w (V ⊓ L'.U k ⊓ (V ⊓ L'.U k'))) (hT k k')
  rwa [map_mul, gm_res f w _ hm, gm_res f w _ hm, gm_res f w _ hm] at e

theorem ratio (p : Z ⟶ Y) (L' : LB Z) (hL' : L'.IsLB) {V₁ V₂ : Y.Opens}
    (T₁ : ∀ k : L'.ι, Γ(Z, p ⁻¹ᵁ V₁ ⊓ L'.U k)ˣ) (T₂ : ∀ k : L'.ι, Γ(Z, p ⁻¹ᵁ V₂ ⊓ L'.U k)ˣ)
    (h₁ : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V₁ → f w ∈ L'.U k → f w ∈ L'.U k' →
      gm f w _ (T₁ k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T₁ k'))
    (h₂ : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V₂ → f w ∈ L'.U k → f w ∈ L'.U k' →
      gm f w _ (T₂ k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T₂ k')) :
    ∃ r : Γ(Z, p ⁻¹ᵁ (V₁ ⊓ V₂))ˣ, ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k : L'.ι),
      f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) → f w ∈ L'.U k → gm f w _ r = gm f w _ (T₂ k) * (gm f w _ (T₁ k))⁻¹ := by
  have l₁ : ∀ k, p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k ≤ p ⁻¹ᵁ V₁ ⊓ L'.U k := fun _ x hx => ⟨hx.1.1, hx.2⟩
  have l₂ : ∀ k, p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k ≤ p ⁻¹ᵁ V₂ ⊓ L'.U k := fun _ x hx => ⟨hx.1.2, hx.2⟩
  have hu : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k : L'.ι) (hw : f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k),
      gm f w _ (res (l₂ k) (T₂ k) * (res (l₁ k) (T₁ k))⁻¹) = gm f w _ (T₂ k) * (gm f w _ (T₁ k))⁻¹ := by
    intro W f w k hw
    rw [map_mul, map_inv, gm_res f w _ hw, gm_res f w _ hw]
  obtain ⟨s, hs⟩ := glue_unit (p ⁻¹ᵁ (V₁ ⊓ V₂)) (fun k => p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k) (fun _ => inf_le_left)
    (fun x hx => by
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact Opens.mem_iSup.2 ⟨k, hx, hk⟩)
    (fun k => res (l₂ k) (T₂ k) * (res (l₁ k) (T₁ k))⁻¹)
    (fun i j x hx => by
      rw [hu (𝟙 Z) x i hx.1, hu (𝟙 Z) x j hx.2, h₁ (𝟙 Z) x i j hx.1.1.1 hx.1.2 hx.2.2,
        h₂ (𝟙 Z) x i j hx.1.1.2 hx.1.2 hx.2.2, mul_inv, _root_.mul_mul_mul_comm, _root_.mul_inv_cancel, _root_.one_mul])
  refine ⟨s, fun f w k hw hk => ?_⟩
  have hm : f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k := ⟨hw, hk⟩
  rw [← gm_res f w inf_le_left hm s, hs k, hu f w k hm]

theorem descend (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) (O : Y.Opens)
    (r : Γ(Z, p ⁻¹ᵁ O)ˣ) : ∃ g : Γ(Y, O)ˣ, pullU p O g = r := by
  let e := RingEquiv.ofBijective (p.app O).hom (hp O)
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom r, Units.ext ?_⟩
  exact e.apply_symm_apply r.val

theorem eq_of_gm (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) {O : Y.Opens}
    {a b : Γ(Y, O)ˣ} (h : ∀ z : Z, p z ∈ O → gm (𝟙 Z ≫ p) z O a = gm (𝟙 Z ≫ p) z O b) : a = b := by
  have e : pullU p O a = pullU p O b := unit_ext fun z hz => by
    rw [gm_pull (𝟙 Z) p z O hz a, gm_pull (𝟙 Z) p z O hz b]
    exact h z hz
  exact Units.ext ((hp O).1 (congrArg Units.val e))

def descLB (V : Y → Y.Opens) (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) : LB Y := ⟨Y, V, g⟩

theorem isLB_descLB (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) (L' : LB Z) (hL' : L'.IsLB)
    (V : Y → Y.Opens) (hyV : ∀ y, y ∈ V y) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descLB V g).IsLB where
  cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hyV y⟩
  g_self := fun y => eq_of_gm p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [gm_res (𝟙 Z ≫ p) z _ hz, map_one]
    exact (key (𝟙 Z) z y y k hz hz hk).trans (mul_inv_cancel _)
  cocycle := fun a b c => eq_of_gm p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [map_mul, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz,
      key (𝟙 Z) z a b k hz.1.1 hz.1.2 hk, key (𝟙 Z) z b c k hz.1.2 hz.2 hk,
      key (𝟙 Z) z a c k hz.1.1 hz.2 hk]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem chart_le (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (q : (LB.div ((descLB V g).pull p) L').ι) :
    (LB.div ((descLB V g).pull p) L').U q ≤ p ⁻¹ᵁ V (q.1 PUnit.unit) ⊓ L'.U q.2 :=
  fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, hx.2⟩

def descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) : LB.Iso L' ((descLB V g).pull p) :=
  ⟨fun q => (res (chart_le p L' V g q) (T (q.1 PUnit.unit) q.2))⁻¹⟩

theorem gw_descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) {W : Scheme.{0}} (f : W ⟶ Z) (x : W) (j : Y) (k : L'.ι)
    (hj : p (f x) ∈ V j) (hk : f x ∈ L'.U k) :
    gw (descIso p L' V T g) f x j k = (gm f x _ (T j k))⁻¹ := by
  unfold gw descIso
  exact (map_inv (gm f x _) _).trans (congrArg (·⁻¹) (gm_res f x (chart_le p L' V g (fun _ => j, k))
    ⟨Set.mem_iInter.2 fun _ => hj, hk⟩ (T j k)))

theorem isGen_descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (hc : ∀ (y : Y) {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V y → f w ∈ L'.U k →
      f w ∈ L'.U k' → gm f w _ (T y k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T y k'))
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descIso p L' V T g).IsGen := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff]
  intro W f x j j' k k' hj hj' hk hk'
  rw [gw_descIso p L' V T g f x j k hj hk, gw_descIso p L' V T g f x j' k' hj' hk',
    key f x j j' k hj hj' hk, hc j' f x k k' hj' hk hk']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.Mum.LBDesc

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_pull)
open GlobalTheory.Mum.LBDesc

theorem lb_descend : ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), (∀ V : Y.Opens, Function.Bijective (p.app V).hom) →
    ∀ L' : LB Z, L'.IsLB → (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen) →
    ∃ L : LB Y, L.IsLB ∧ LBIso L' (L.pull p) := by
  intro Z Y p hp L' hL' hloc
  choose V hyV t ht using hloc
  choose T hT using fun y => transport L' (p ⁻¹ᵁ V y) (t y) (ht y)
  have hc : ∀ (y : Y) {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V y → f w ∈ L'.U k →
      f w ∈ L'.U k' → gm f w _ (T y k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T y k') :=
    fun y _ f w k k' h hk hk' => gm_compat L' _ (T y) (hT y) f w k k' h hk hk'
  choose r hr using fun y y' => ratio p L' hL' (T y) (T y') (hc y) (hc y')
  choose g hg using fun y y' => descend p hp _ (r y y')
  have key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹ := by
    intro W f w y y' k h1 h2 hk
    exact (gm_pull f p w (V y ⊓ V y') ⟨h1, h2⟩ (g y y')).symm.trans
      ((congrArg _ (hg y y')).trans (hr y y' f w k ⟨h1, h2⟩ hk))
  exact ⟨descLB V g, isLB_descLB p hp L' hL' V hyV T g key, descIso p L' V T g,
    isGen_descIso p L' V T g hc key⟩

end GlobalTheory.Mum
