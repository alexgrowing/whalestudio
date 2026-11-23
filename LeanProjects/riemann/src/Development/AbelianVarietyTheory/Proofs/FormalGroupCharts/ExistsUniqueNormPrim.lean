import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_gen_of_lbIso {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (X ⟶ X)) (ε : K → ℤ)
    (H : LBIso L (LB.LinComb L φ ε)) :
    ∃ t : LB.Gen (LB.LinComb L (K := K ⊕ PUnit) (Sum.elim φ (fun _ => 𝟙 X)) (Sum.elim ε (fun _ => -1))), t.IsGen := by
  obtain ⟨v, hv⟩ := H
  have le : ∀ j : K ⊕ PUnit → L.ι, LB.wchart L (Sum.elim φ (fun _ : PUnit => 𝟙 X)) j ≤
      LB.wchart L φ (j ∘ Sum.inl) ⊓ L.U (j (Sum.inr PUnit.unit)) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.1 hy (Sum.inr PUnit.unit)⟩
  refine ⟨⟨fun j => res (le j) (v.s (j ∘ Sum.inl, j (Sum.inr PUnit.unit)))⟩,
    fun (p q : K ⊕ PUnit → L.ι) => unit_ext fun y hy => ?_⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ LB.wchart L φ (p ∘ Sum.inl) ⊓ L.U (p (Sum.inr PUnit.unit)) ⊓
      (LB.wchart L φ (q ∘ Sum.inl) ⊓ L.U (q (Sum.inr PUnit.unit))) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (LB.wchart L φ (p ∘ Sum.inl) ⊓ L.U (p (Sum.inr PUnit.unit)) ⊓
      (LB.wchart L φ (q ∘ Sum.inl) ⊓ L.U (q (Sum.inr PUnit.unit)))))
    (hv (p ∘ Sum.inl, p (Sum.inr PUnit.unit)) (q ∘ Sum.inl, q (Sum.inr PUnit.unit)))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div L (LB.LinComb L φ ε) (𝟙 X) y (p ∘ Sum.inl, p (Sum.inr PUnit.unit))
      (q ∘ Sum.inl, q (Sum.inr PUnit.unit)) hm).trans (congrArg₂ (· * ·)
        (gm_linComb L φ ε (𝟙 X) y _ _ hm.1.1 hm.2.1) rfl)) (gm_res _ y _ hm _))))
  refine ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 X) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y (le q) hy.2 _)))
  exact DVR.prod_sum₂ (K := K) (K' := PUnit) _ rfl ((Fintype.prod_unique _).trans (zpow_neg_one _))

theorem gen_ext_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t t' : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (h : ∀ y J, Good L y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : t.s = t'.s := by
  funext j
  exact Units.ext (sec_ext_val hL (s := genSec t ht) (s' := genSec t' ht') (fun y J hJ => by
    rw [sval_genSec t ht _ y hJ, sval_genSec t' ht' _ y hJ, h y J hJ]) j)

theorem prod_lam {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] (x y : T ⟶ G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ G.left) → U) :
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

theorem prod_prim {S : Scheme.{0}} {G T : Over S} [GrpObj G] (w : G ⟶ G) (x : T ⟶ G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ G.left) → U) :
    ∏ i, h (x.left ≫ primφ w i) ^ primε i =
      h x.left * (h (x * (x ≫ w)).left)⁻¹ * h x.left * h (x ≫ w).left * (h (1 : T ⟶ G).left)⁻¹ := by
  have e₁ : x ≫ (𝟙 G * w) = x * (x ≫ w) := (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have e₄ : x ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  rw [Fin.prod_univ_five]
  show h (x.left ≫ 𝟙 _) ^ (1 : ℤ) * h (x ≫ (𝟙 G * w)).left ^ (-1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (1 : ℤ) *
    h (x ≫ w).left ^ (1 : ℤ) * h (x ≫ (1 : G ⟶ G)).left ^ (-1 : ℤ) = _
  rw [e₁, e₄, Category.comp_id]
  simp only [zpow_neg, zpow_one]

theorem exists_unique_normPrim : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (w : G ⟶ G) [IsMonHom w],
    LBIso Lr.L (cubeLB G ![𝟙 G, w] Lr.L) →
    (∃ ρ : LB.Gen (LB.LinComb Lr.L (primφ w) primε), ρ.IsGen ∧
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (eSec G)) Lr.rig) ∧
    (Function.Surjective G.hom.appTop.hom → ∀ ρ ρ' : LB.Gen (LB.LinComb Lr.L (primφ w) primε), ρ.IsGen → ρ'.IsGen →
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (eSec G)) Lr.rig →
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ' (eSec G)) Lr.rig → ρ.s = ρ'.s) := by
  intro S G _ _ Lr w _ H
  have he : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]
  refine ⟨?_, fun hp ρ ρ' h h' c c' => gen_ext_val Lr.isLB h h' fun y J hJ =>
    gen_unique Lr.isLB G.hom (eSec G) he hp h h' (fun y J hJ => ?_) _ _ y J hJ⟩
  · obtain ⟨t₀, ht₀⟩ := exists_gen_of_lbIso Lr.L _ _ H
    have P : ∀ (V : Type) [CommGroup V] (k : (G.left ⟶ G.left) → V), ∏ i, k (primφ w i) ^ primε i =
        k (𝟙 _) * (k (𝟙 G * w : G ⟶ G).left)⁻¹ * k (𝟙 _) * k w.left * (k (1 : G ⟶ G).left)⁻¹ := fun V _ k => by
      have := prod_prim w (𝟙 G) k
      simpa only [Over.id_left, Category.id_comp] using this
    obtain ⟨t, ht, -⟩ := exists_gen Lr.isLB (φ' := primφ w) (ε' := primε) (fun V _ k => by
      refine (DVR.prod_neg _ _ (DVR.prod_sum₂ (K' := PUnit) (U := V) _ (prod_lam (𝟙 G) w k)
        (c' := (k (𝟙 _))⁻¹) (by simp))).trans ?_
      rw [P]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, Over.id_left]
      abel) _ (DVR.invGen_isGen _ _ _ _ ht₀)
    have n : G.hom ≫ eSec G = (1 : G ⟶ G).left := rfl
    obtain ⟨ρ, hρ, hv⟩ := exists_gen Lr.isLB (φ' := primφ w) (ε' := primε) (fun V _ k => by
      have p := prod_prim w (1 : G ⟶ G) k
      rw [MonObj.one_comp, _root_.mul_one] at p
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5 ⊕ PUnit) (U := V) _
        (c := ∏ i, k (primφ w i) ^ primε i) rfl
        (DVR.prod_sum₂ (K := Fin 5) (K' := PUnit) (U := V) _ (DVR.prod_neg _ _ p) (c' := k (1 : G ⟶ G).left)
          (by rw [Fintype.prod_unique]; exact zpow_one _))) ?_
      simp)
      (LB.mulGen Lr.L _ _ _ _ t (LB.mulGen Lr.L _ _ _ _
        (LB.invGen Lr.L _ _ (LB.pullGen Lr.L _ _ t (1 : G ⟶ G).left)) (LB.pullGen Lr.L _ _ Lr.rig G.hom)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)) (DVR.pullGen_isGen _ _ _ _ Lr.rigGen _)))
    refine ⟨ρ, hρ, corr_of_val Lr.isLB fun y J hJ => ?_⟩
    have e₁ : eSec G ≫ (1 : G ⟶ G).left = eSec G := by
      rw [← n, ← Category.assoc, he]; exact Category.id_comp _
    rw [val_pull hJ, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, e₁,
      mul_inv_cancel_left]
    exact congrArg (fun q => val Lr.rig q y J) he
  · have a := val_corr hJ c (𝟙 _)
    have b := val_corr hJ c' (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at a b
    exact a.trans b.symm

end GlobalTheory.JetSer
