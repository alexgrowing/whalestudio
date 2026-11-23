import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NormRos

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_gen_of_lbIso {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k))), t.IsGen := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ j : K' ⊕ K → L.ι, LB.wchart L (Sum.elim φ' φ) j ≤
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩
  refine ⟨⟨fun j => res (le j) (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩,
    fun (p q : K' ⊕ K → L.ι) => unit_ext fun y hy => ?_⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr)) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 Y) y (LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr))))
    (hw (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr))
  have e' := (gm_res (𝟙 Y) y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr) hm)
    (gm_res (𝟙 Y) y _ hm _))))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 Y) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.2 _)))
  refine (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hm.1.1 hm.2.1).symm ?_)
  refine Eq.trans ?_ (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hm.1.2 hm.2.2).symm)
  simp only [Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp_apply]

theorem gen_s_ext {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good L y J → val u (𝟙 Y) y J = val u' (𝟙 Y) y J) : u.s = u'.s :=
  funext fun j => Units.ext (sec_ext_val hL (s := genSec u hu) (s' := genSec u' hu') (fun y J hJ => by
    rw [sval_genSec u hu _ y hJ, sval_genSec u' hu' _ y hJ, h y J hJ]) j)

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem prod_square {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum G ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum G ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card))) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem exists_gen_rosati {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G)
    (H : LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L)) :
    ∃ t : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε), t.IsGen := by
  obtain ⟨t, ht⟩ := exists_gen_of_lbIso H
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := rosatiφ G f g) (ε' := rosatiε) (fun V _ k => by
      have p := prod_ros f g (fst G G) (snd G G) k
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      refine (DVR.prod_neg _ _ (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2)))
        (U := V) _ (prod_square (fst G G) (snd G G ≫ g) k)
        (DVR.prod_neg _ _ (prod_square (fst G G ≫ f) (snd G G) k)))).trans ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
  exact ⟨u, hu⟩

theorem exists_isNormRos {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G) [IsMonHom f] [IsMonHom g]
    (t : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε)) (ht : t.IsGen) : ∃ u, IsNormRos L f g u := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := rosatiφ G f g) (ε' := rosatiε)
    (fun V _ k => by
      have p := prod_ros f g (1 : G ⊗ G ⟶ G) (1 : G ⊗ G ⟶ G) k
      rw [MonObj.one_comp, MonObj.one_comp, _root_.mul_one] at p
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
        (c := ∏ i, k (rosatiφ G f g i) ^ rosatiε i) rfl (DVR.prod_neg _ _ p)) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (lift (1 : G ⊗ G ⟶ G) (1 : G ⊗ G ⟶ G)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_⟩
  have e : zero2 G ≫ (lift (1 : G ⊗ G ⟶ G) (1 : G ⊗ G ⟶ G)).left = zero2 G := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one]
    congr 1
  rw [val_one, val_pull hJ, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]

omit [IsCommMonObj G] in

theorem isNormRos_unique {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G)
    (hs : Function.Surjective (G ⊗ G).hom.appTop.hom) {u u' : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε)}
    (h : IsNormRos L f g u) (h' : IsNormRos L f g u') : u.s = u'.s := by
  have z2 : zero2 G ≫ (G ⊗ G).hom = 𝟙 S := Over.w (lift η[G] η[G])
  refine gen_s_ext hL h.1 h'.1 fun y J hJ =>
    gen_unique hL (S₀ := S) (G ⊗ G).hom (zero2 G) z2 hs h.1 h'.1 (fun s I hI => ?_) _ _ y J hJ
  have a := val_corr hI h.2 (𝟙 _)
  have b := val_corr hI h'.2 (𝟙 _)
  rw [val_pull hI, Category.id_comp, val_one] at a b
  exact a.trans b.symm

theorem normRos_of_lbIso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB →
    ∀ (f g : G ⟶ G) [IsMonHom f] [IsMonHom g],
    LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) →
    (∃ u, IsNormRos L f g u) ∧ (Function.Surjective (G ⊗ G).hom.appTop.hom →
      ∀ u u', IsNormRos L f g u → IsNormRos L f g u' → u.s = u'.s) := by
  intro S G _ _ L hL f g _ _ H
  obtain ⟨t, ht⟩ := exists_gen_rosati hL f g H
  exact ⟨exists_isNormRos hL f g t ht, fun hs u u' h h' => isNormRos_unique hL f g hs h h'⟩

end GlobalTheory.NormRos
