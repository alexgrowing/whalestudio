import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

noncomputable section

namespace GlobalTheory.SqLB

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

abbrev sq (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)

theorem mem_sq {x : X} {j : L.ι} (h : x ∈ L.U j) : x ∈ (sq L).U (fun _ => j) :=
  Set.mem_iInter.2 fun _ => h

theorem gm_sq_g (f : Y ⟶ X) (y : Y) {j j' : L.ι} (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y ((sq L).U (fun _ => j) ⊓ (sq L).U (fun _ => j')) ((sq L).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ (2 : ℤ) := by
  refine (gm_linComb L (fun _ => 𝟙 X) (fun _ => 2) f y _ _ (mem_sq hj) (mem_sq hj')).trans ?_
  rw [Fintype.prod_unique, Category.comp_id]

def gq (w : LB.Iso (sq L') ((sq L).pull F)) (f : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
  gw w f y (fun _ => j) (fun _ => k)

theorem gq_trans {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (f : Y ⟶ X') (y : Y) {j j' : L.ι} {k k' : L'.ι}
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
    gq w f y j k = gm (f ≫ F) y _ (L.g j j') ^ (2 : ℤ) * (gm f y _ (L'.g k k') ^ (2 : ℤ))⁻¹ * gq w f y j' k' := by
  rw [gq, gq, hw Y f y _ _ _ _ (mem_sq hj) (mem_sq hj') (mem_sq hk) (mem_sq hk'), gm_sq_g (f ≫ F) y hj hj',
    gm_sq_g f y hk hk']

def pq (w : LB.Iso (sq L') ((sq L).pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι)
    (q : K → L'.ι) : (Z.presheaf.stalk z)ˣ := ∏ k, gq w (r ≫ φ' k) z (p k) (q k) ^ ε k

theorem trF_two {M : LB X} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (j j' : K → M.ι) :
    trF φ (fun k => 2 * ε k) r z j j' = trF φ ε r z j j' ^ (2 : ℤ) := by
  rw [trF, trF, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, mul_comm]

theorem pq_trans {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y)
    (z : Z) {p p' : K → L.ι} {q q' : K → L'.ι} (hp : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p') (hq : r z ∈ LB.wchart L' φ' q) (hq' : r z ∈ LB.wchart L' φ' q') :
    pq w φ' ε r z p q = trF (fun k => φ' k ≫ F) (fun k => 2 * ε k) r z p p' *
      (trF φ' (fun k => 2 * ε k) r z q q')⁻¹ * pq w φ' ε r z p' q' := by
  rw [trF_two, trF_two, pq, pq, trF, trF, ← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gq_trans hw (r ≫ φ' k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), Category.assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  rw [smul_add, smul_add, smul_comm (ε k) (2 : ℤ), smul_neg, smul_comm (ε k) (2 : ℤ)]

theorem exists_pq (w : LB.Iso (sq L') ((sq L).pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (p : K → L.ι) (q : K → L'.ι) :
    ∃ u : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q → gm r z _ u = pq w φ' ε r z p q := by
  have le : ∀ k, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      φ' k ⁻¹ᵁ (((sq L).pull F).U (fun _ => fun _ => p k) ⊓ (sq L').U (fun _ => q k)) := fun k y hy =>
    ⟨mem_pull.2 (mem_sq (Set.mem_iInter.1 hy.1 k)), mem_sq (Set.mem_iInter.1 hy.2 k)⟩
  exact ⟨∏ k, res (le k) (pullU (φ' k) _ (w.s (fun _ => fun _ => p k, fun _ => q k))) ^ ε k, fun Z r z hz =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
      ((gm_res r z (le k) hz _).trans (gm_pull r (φ' k) z _ (le k hz) _))))⟩

theorem exists_sq_up {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
        r z ∈ LB.wchart L' φ' q → gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 := by
  choose u hu using fun p q => exists_pq w φ' ε p q
  have glue : ∀ p : K → L.ι, ∃ s : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 := by
    intro p
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ (u p q * res inf_le_right (a.s q) ^ 2) =
          pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 :=
      fun Z r z q hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (hu p q Z r z hz)
        ((map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hz _))))
    obtain ⟨s, hs⟩ := glue_unit _ (fun q => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_left)
      (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ' k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) (fun q => u p q * res inf_le_right (a.s q) ^ 2)
      (fun q q' y hy => by
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, pq_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hL _ _ (𝟙 Y) y hy.1.1, trF_two, gen_trans ha (𝟙 Y) y hy.1.2 hy.2.2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
        abel)
    refine ⟨s, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res r z inf_le_left hz s).symm.trans ((congrArg (gm r z _) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q => hs p Z r z q⟩
  choose q hq using fun k => exists_chart hL' (φ' k y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
  refine (hs j _ (𝟙 Y) y q hj m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y q hj' m)).symm)
  rw [pq_trans hw φ' ε (𝟙 Y) y hj hj' m m, trF_self hL' _ _ (𝟙 Y) y m, inv_one, _root_.mul_one, _root_.mul_assoc]

theorem exists_sq_gen : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}, L.IsLB → L'.IsLB →
    ∀ (w : LB.Iso (LB.LinComb L' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => 2))
      ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).pull F)), w.IsGen →
    ∀ {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∃ W : ∀ (Z : Scheme.{0}) (z : Z), (K → (Z ⟶ X')) → ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) →
          (Z.presheaf.stalk z)ˣ,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι),
          Good L z J → Good L' z J' → val t r z J = W Z z (fun k => r ≫ φ' k) J J' * val a r z J' ^ 2 := by
  intro X X' Y L L' F hL hL' w hwg K _ φ' ε a ha
  obtain ⟨t, ht, hv⟩ := exists_sq_up ((isGen_iff w).1 hwg) hL hL' a ha
  refine ⟨t, ht, fun Z z ψ J J' => ∏ k, gq w (ψ k) z (J (ψ k ≫ F)) (J' (ψ k)) ^ ε k, fun Z r z J J' hJ hJ' => ?_⟩
  refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans ?_
  simp only [pq, Category.assoc]
  rfl

end GlobalTheory.SqLB
