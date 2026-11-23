import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.PowData

section ProdPow

variable {X Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]

def prodZGen (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ) (n : I → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (K := I × K) (fun p => φ p.1 p.2) (fun p => n p.1 * ε p.1 p.2)) where
  s := fun j => ∏ i, res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)) :
      LB.wchart L (fun p : I × K => φ p.1 p.2) j ≤ LB.wchart L (φ i) (fun k => j (i, k)))
    ((t i).s fun k => j (i, k)) ^ n i

variable {L}

theorem val_prodZGen (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ) (n : I → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (prodZGen L φ ε n t) r z J = ∏ i, val (t i) r z J ^ n i := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans ?_)
  exact congrArg (· ^ n i) (gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

theorem prodZGen_isGen (hL : L.IsLB) {φ : I → K → (Y ⟶ X)} {ε : I → K → ℤ} (n : I → ℤ)
    {t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))} (ht : ∀ i, (t i).IsGen) : (prodZGen L φ ε n t).IsGen := by
  intro j j'
  refine unit_ext fun y hy => ?_
  have m : ∀ (j : I × K → L.ι) (i : I), y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (φ i) (fun k => j (i, k)) :=
    fun _ i hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y _ ((prodZGen L φ ε n t).s j) = ∏ i, gm (𝟙 Y) y _ ((t i).s fun k => j (i, k)) ^ n i := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans
      (congrArg (· ^ n i) (gm_res _ y _ hj _)))
  rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy, v j hy.1, v j' hy.2]
  erw [gm_linComb L (fun p : I × K => φ p.1 p.2) (fun p => n p.1 * ε p.1 p.2) (𝟙 Y) y j j' hy.1 hy.2]
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  erw [gen_trans (ht i) (𝟙 Y) y (m j i hy.1) (m j' i hy.2)]
  rw [mul_zpow, trF, ← Finset.prod_zpow]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, mul_comm]

end ProdPow

end GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

section JoinIso

variable {X X₁ X₂ Z : Scheme.{0}}

theorem part_gm_g_eq_one {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} (h : IsPart N M e π) (hM : M.IsLB)
    {ψ : Z ⟶ X₁} {f : Z ⟶ X} (hf : f = ψ ≫ e) {z : Z} {i j : N.ι} (e₀ : π i = π j) (hi : ψ z ∈ M.U (π i)) :
    gm f z (N.U i ⊓ N.U j) (N.g i j) = 1 := by
  subst hf
  rw [h.g _ ψ z i j hi (e₀ ▸ hi)]
  have : ∀ b, π i = b → gm ψ z (M.U (π i) ⊓ M.U b) (M.g (π i) b) = 1 := by
    rintro _ rfl; exact gm_self hM _ z hi
  exact this _ e₀

theorem part_gm_g_sec {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} (h : IsPart N M e π) {σ : M.ι → N.ι}
    (hσ : ∀ i, π (σ i) = i) {ψ : Z ⟶ X₁} {f : Z ⟶ X} (hf : f = ψ ≫ e) {z : Z} {a b : M.ι} (ha : ψ z ∈ M.U a)
    (hb : ψ z ∈ M.U b) : gm f z (N.U (σ a) ⊓ N.U (σ b)) (N.g (σ a) (σ b)) = gm ψ z (M.U a ⊓ M.U b) (M.g a b) := by
  subst hf
  rw [h.g _ ψ z _ _ (by rw [hσ]; exact ha) (by rw [hσ]; exact hb)]
  have : ∀ a b a' b', a = a' → b = b' → gm ψ z (M.U a ⊓ M.U b) (M.g a b) = gm ψ z (M.U a' ⊓ M.U b') (M.g a' b') := by
    rintro _ _ _ _ rfl rfl; rfl
  exact this _ _ _ _ (hσ a) (hσ b)

variable {M₁ : LB X₁} {M₂ : LB X₂} {K : Type} [Fintype K]

theorem exists_iso_of_joinGen (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) [Nonempty X₁] [Nonempty X₂] {φ : K → (X₁ ⟶ X₂)}
    {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl))
      (Sum.elim ε (fun _ => -1)))) (ht : t.IsGen) :
    ∃ w : LB.Iso M₁ (LB.LinComb M₂ φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ X₁) (z : Z) (J),
      Good (join M₁ M₂) z J → gm p z _ (w.s (fun k => rr J (p ≫ φ k), rl J p)) = val t p z J := by
  have hp₁ := isPart_inl M₁ M₂
  have hp₂ := isPart_inr M₁ M₂
  choose σ₂ hσ₂ using snd_surjective (M₂ := M₂) h₁
  choose σ₁ hσ₁ using fst_surjective (M₁ := M₁) h₂
  let ix : (K → M₂.ι) × M₁.ι → K ⊕ PUnit → (join M₁ M₂).ι := fun a =>
    Sum.elim (fun k => σ₂ (a.1 k)) (fun _ => σ₁ a.2)
  have le : ∀ a, (LB.div (LB.LinComb M₂ φ ε) M₁).U a ≤
      LB.wchart (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl)) (ix a) :=
    fun a y hy => Set.mem_iInter.2 fun k => by
      rcases k with k | u
      · exact (hp₂.mem _ _).2 ((hσ₂ _).symm ▸ Set.mem_iInter.1 hy.1 k)
      · exact (hp₁.mem _ _).2 ((hσ₁ _).symm ▸ hy.2)
  let c : ChartPull (LB.div (LB.LinComb M₂ φ ε) M₁)
      (LB.LinComb (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl))
        (Sum.elim ε (fun _ => -1))) (𝟙 X₁) :=
    { idx := ix
      le := le
      g := fun y a b ha hb => by
        erw [gm_div M₁ (LB.LinComb M₂ φ ε) (𝟙 X₁) y a b ⟨ha, hb⟩, gm_linComb M₂ φ ε (𝟙 X₁) y a.1 b.1 ha.1 hb.1,
          gm_linComb (join M₁ M₂) _ _ (𝟙 X₁) y (ix a) (ix b) (le a ha) (le b hb)]
        rw [Fintype.prod_sum_type]
        simp only [Finset.univ_unique, Finset.prod_singleton]
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) ?_
        · exact congrArg (· ^ ε k) (part_gm_g_sec hp₂ hσ₂ (ψ := 𝟙 X₁ ≫ φ k) (f := 𝟙 X₁ ≫ φ k ≫ coprod.inr)
            (Category.assoc _ _ _).symm (a := a.1 k) (b := b.1 k) (Set.mem_iInter.1 ha.1 k)
            (Set.mem_iInter.1 hb.1 k)).symm
        · refine (congrArg (·⁻¹) ?_).trans (zpow_neg_one _).symm
          refine Eq.trans ?_ (part_gm_g_sec hp₁ hσ₁ (ψ := 𝟙 X₁) (f := 𝟙 X₁ ≫ 𝟙 X₁ ≫ coprod.inl)
            (by rw [Category.id_comp]) (a := a.2) (b := b.2) ha.2 hb.2).symm
          rfl }
  refine ⟨cGen c t, cGen_isGen c ht, fun Z p z J hJ => ?_⟩
  have m : p z ∈ (LB.div (LB.LinComb M₂ φ ε) M₁).U (fun k => rr J (p ≫ φ k), rl J p) :=
    ⟨(hp₂.good hJ).mem φ p, hp₁.good hJ p⟩
  have n := hJ.mem (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl)) p
  refine (gm_res p z _ m _).trans ((gen_trans ht p z (le _ m) n).trans ?_)
  refine (congrArg (· * val t p z J) ?_).trans (one_mul _)
  rw [trF, Fintype.prod_sum_type]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  refine (congrArg₂ (· * ·) (Finset.prod_eq_one fun k _ => ?_) ?_).trans (one_mul 1)
  · refine (congrArg (· ^ ε k) (part_gm_g_eq_one hp₂ h₂ (ψ := p ≫ φ k) (f := p ≫ φ k ≫ coprod.inr)
      (Category.assoc _ _ _).symm (i := σ₂ (rr J (p ≫ φ k))) (j := J (p ≫ φ k ≫ coprod.inr))
      ((hσ₂ _).trans (show (J ((p ≫ φ k) ≫ coprod.inr)).2 = _ by rw [Category.assoc])) ?_)).trans (one_zpow _)
    rw [hσ₂]; exact (hp₂.good hJ) (p ≫ φ k)
  · refine (congrArg (· ^ (-1 : ℤ)) (part_gm_g_eq_one hp₁ h₁ (ψ := p) (f := p ≫ 𝟙 X₁ ≫ coprod.inl)
      (by rw [Category.id_comp]) (i := σ₁ (rl J p)) (j := J (p ≫ 𝟙 X₁ ≫ coprod.inl))
      ((hσ₁ _).trans (show (J (p ≫ coprod.inl)).1 = _ by rw [Category.id_comp])) ?_)).trans (one_zpow _)
    rw [hσ₁]; exact hp₁.good hJ p

end JoinIso

end GlobalTheory.Mum.PowData
