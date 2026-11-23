import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBalUniq

open TopologicalSpace

variable {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ}

theorem w_trans (w : LB.Iso M' (LB.LinComb M ψ δ)) (hw : w.IsGen) {Z : Scheme.{0}} (χ : Z ⟶ X') (z : Z)
    {jj jj' : K₀ → M.ι} {k k' : M'.ι} (h₁ : χ z ∈ LB.wchart M ψ jj) (h₁' : χ z ∈ LB.wchart M ψ jj')
    (h₂ : χ z ∈ M'.U k) (h₂' : χ z ∈ M'.U k') :
    gm χ z (LB.wchart M ψ jj ⊓ M'.U k) (w.s (jj, k)) =
      (∏ i, gm (χ ≫ ψ i) z (M.U (jj i) ⊓ M.U (jj' i)) (M.g (jj i) (jj' i)) ^ δ i) *
        (gm χ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * gm χ z (LB.wchart M ψ jj' ⊓ M'.U k') (w.s (jj', k')) := by
  have hm : χ z ∈ LB.wchart M ψ jj ⊓ M'.U k ⊓ (LB.wchart M ψ jj' ⊓ M'.U k') := ⟨⟨h₁, h₂⟩, h₁', h₂'⟩
  have e := congrArg (gm χ z (LB.wchart M ψ jj ⊓ M'.U k ⊓ (LB.wchart M ψ jj' ⊓ M'.U k'))) (hw (jj, k) (jj', k'))
  have d := gm_div M' (LB.LinComb M ψ δ) χ z (jj, k) (jj', k') hm
  have l := gm_linComb M ψ δ χ z jj jj' h₁ h₁'
  exact (gm_res χ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (d.trans (congrArg₂ (· * ·) l rfl)) (gm_res χ z _ hm _))))

theorem prod_split {G : Type} [CommGroup G] {K : Type} [Fintype K] (ε : K → ℤ) (f : K × K₀ → G) :
    ∏ p, f p ^ (ε p.1 * δ p.2) = ∏ a, (∏ i, f (a, i) ^ δ i) ^ ε a := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_mul, mul_comm]

section Gen

variable {K : Type} [Fintype K] {φ' : K → (Y ⟶ X')} {ε : K → ℤ}

theorem chart_le (j : K × K₀ → M.ι) (q : K → M'.ι) (a : K) :
    LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q ≤
      φ' a ⁻¹ᵁ (LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a) := fun _ hy =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (a, k), Set.mem_iInter.1 hy.2 a⟩

def locU (w : LB.Iso M' (LB.LinComb M ψ δ)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (j : K × K₀ → M.ι)
    (q : K → M'.ι) : Γ(Y, LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q)ˣ :=
  (∏ a, res (chart_le j q a) (pullU (φ' a) _ (w.s (fun k => j (a, k), q a))) ^ ε a) * res inf_le_right (t'.s q)

theorem gm_locU (w : LB.Iso M' (LB.LinComb M ψ δ)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (j : K × K₀ → M.ι)
    (q : K → M'.ι) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) :
    gm r z (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) (locU w t' j q) =
      (∏ a, gm (r ≫ φ' a) z (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q a))
        (w.s (fun k => j (a, k), q a)) ^ ε a) * gm r z (LB.wchart M' φ' q) (t'.s q) := by
  refine (map_mul (gm r z _) _ _).trans (congrArg₂ (· * ·) ((map_prod (gm r z _) _ _).trans
    (Finset.prod_congr rfl fun a _ => ?_)) ?_)
  · refine (map_zpow (gm r z _) _ _).trans (congrArg (· ^ ε a) ?_)
    have hm : r z ∈ φ' a ⁻¹ᵁ (LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a) := chart_le (δ := δ) j q a hz
    have h1 := gm_res r z (chart_le (δ := δ) j q a) hz (pullU (φ' a) _ (w.s (fun k => j (a, k), q a)))
    have h2 := gm_pull r (φ' a) z ((LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a)) hm
      (w.s (fun k => j (a, k), q a))
    exact h1.trans h2
  · exact gm_res r z (inf_le_right : LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q ≤
      LB.wchart M' φ' q) hz (t'.s q)

theorem exists_gen_iso (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M ψ δ)) (hw : w.IsGen)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) :
    ∃ u : LB.Gen (LB.LinComb M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι), Good M z J →
        Good M' z J' → val u r z J = (∏ a, GlobalTheory.TensBal.isoV w z J J' (r ≫ φ' a) ^ ε a) * val t' r z J' := by
  have tr : ∀ (j : K × K₀ → M.ι) (q q' : K → M'.ι) (y : Y),
      y ∈ (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) ⊓
        (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q') →
      gm (𝟙 Y) y _ (locU w t' j q) = gm (𝟙 Y) y _ (locU w t' j q') := by
    intro j q q' y hy
    rw [gm_locU w t' j q (𝟙 Y) y hy.1, gm_locU w t' j q' (𝟙 Y) y hy.2, gen_trans ht' (𝟙 Y) y hy.1.2 hy.2.2]
    simp only [trF, Category.id_comp]
    have e : ∀ a, gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q a)) (w.s (fun k => j (a, k), q a)) =
        (gm (φ' a) y (M'.U (q a) ⊓ M'.U (q' a)) (M'.g (q a) (q' a)))⁻¹ *
          gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q' a)) (w.s (fun k => j (a, k), q' a)) := by
      intro a
      have m := chart_le (δ := δ) j q a hy.1
      have m' := chart_le (δ := δ) j q' a hy.2
      rw [w_trans w hw (φ' a) y m.1 m.1 m.2 m'.2, Finset.prod_eq_one fun i _ => ?_, _root_.one_mul]
      exact (congrArg (· ^ δ i) (gm_self hM _ y (Set.mem_iInter.1 hy.1.1 (a, i)))).trans (one_zpow _)
    rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e a)]
    simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ j : K × K₀ → M.ι, ∃ s : Γ(Y, LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j)ˣ,
      ∀ q, res inf_le_left s = locU w t' j q := fun j =>
    glue_unit _ (fun q => LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q)
      (fun _ => inf_le_left) (fun y hy => by
        choose b hb using fun a => exists_chart hM' (φ' a y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨b, hy, Set.mem_iInter.2 hb⟩) (locU w t' j) (tr j)
  choose s hs using glue
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K × K₀ → M.ι) (q : K → M'.ι)
      (hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q),
      gm r z _ (s j) = gm r z _ (locU w t' j q) := fun Z r z j q hz =>
    (gm_res r z inf_le_left hz (s j)).symm.trans (congrArg (gm r z _) (hs j q))
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · choose b hb using fun a => exists_chart hM' (φ' a y)
    have hq : y ∈ LB.wchart M' φ' b := Set.mem_iInter.2 hb
    erw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_linComb M _ (fun p : K × K₀ => ε p.1 * δ p.2) (𝟙 Y) y j j' hy.1 hy.2]
    erw [hv Y (𝟙 Y) y j b ⟨hy.1, hq⟩, hv Y (𝟙 Y) y j' b ⟨hy.2, hq⟩, gm_locU w t' j b (𝟙 Y) y ⟨hy.1, hq⟩,
      gm_locU w t' j' b (𝟙 Y) y ⟨hy.2, hq⟩]
    simp only [Category.id_comp]
    have e : ∀ a, gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (b a)) (w.s (fun k => j (a, k), b a)) =
        (∏ i, gm (φ' a ≫ ψ i) y (M.U (j (a, i)) ⊓ M.U (j' (a, i))) (M.g (j (a, i)) (j' (a, i))) ^ δ i) *
          gm (φ' a) y (LB.wchart M ψ (fun k => j' (a, k)) ⊓ M'.U (b a)) (w.s (fun k => j' (a, k), b a)) := by
      intro a
      have m := chart_le (δ := δ) j b a ⟨hy.1, hq⟩
      have m' := chart_le (δ := δ) j' b a ⟨hy.2, hq⟩
      rw [w_trans w hw (φ' a) y m.1 m'.1 m.2 m.2, gm_self hM' _ y m.2, inv_one, _root_.mul_one]
    rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e a), prod_split ε]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    rw [_root_.mul_assoc]
  · have hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => J (r ≫ φ' p.1 ≫ ψ p.2)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) := ⟨hJ.mem _ r, hJ'.mem φ' r⟩
    refine (hv Z r z _ _ hz).trans ((gm_locU w t' _ _ r z hz).trans ?_)
    refine congrArg (· * _) (Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) ?_)
    unfold GlobalTheory.TensBal.isoV
    have : (fun k => J ((r ≫ φ' a) ≫ ψ k)) = fun k => J (r ≫ φ' a ≫ ψ k) := funext fun k => by rw [Category.assoc]
    rw [this]
    rfl

end Gen

theorem iso_unique : ∀ {X X' Y S₀ : Scheme.{0}} {M : LB X} {M' : LB X'}, M.IsLB → M'.IsLB → ∀ {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ} (w : LB.Iso M' (LB.LinComb M ψ δ)), w.IsGen → ∀ {K K₁ : Type} [Fintype K] [Fintype K₁] {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}, FormEq (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2) φ ε₁ → ∀ {t' : LB.Gen (LB.LinComb M' φ' ε)}, t'.IsGen → ∀ {t : LB.Gen (LB.LinComb M φ ε₁)}, t.IsGen → ∀ (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 _ → Function.Surjective p.appTop.hom → (∀ (y : S₀) (J : (S₀ ⟶ X) → M.ι) (J' : (S₀ ⟶ X') → M'.ι), Good M y J → Good M' y J' → (∏ a, GlobalTheory.TensBal.isoV w y J J' (e ≫ φ' a) ^ ε a) * val t' e y J' = val t e y J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι), Good M z J → Good M' z J' → (∏ a, GlobalTheory.TensBal.isoV w z J J' (r ≫ φ' a) ^ ε a) * val t' r z J' = val t r z J := by
  intro X X' Y S₀ M M' hM hM' K₀ _ ψ δ w hw K K₁ _ _ φ' ε φ ε₁ hF t' ht' t ht p e he hp h Z r z J J' hJ hJ'
  obtain ⟨u, hu, hv⟩ := exists_gen_iso hM hM' w hw ht'
  have key := gen_unique' hM hF p e he hp ht hu (fun y I hI => by
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    exact (h y I I' hI hI').symm.trans (hv _ e y I I' hI hI').symm) Z r z J hJ
  exact (hv Z r z J J' hJ hJ').symm.trans key.symm

end GlobalTheory.TensBalUniq
