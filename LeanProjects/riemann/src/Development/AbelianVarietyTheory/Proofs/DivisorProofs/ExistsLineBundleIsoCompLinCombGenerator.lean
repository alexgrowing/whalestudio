import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LinCombComp

variable {X Y Z : Scheme.{0}}

theorem gm_gen {M : LB Y} {t : LB.Gen M} (ht : t.IsGen) (f : Z ⟶ Y) (z : Z) {i j : M.ι}
    (hi : f z ∈ M.U i) (hj : f z ∈ M.U j) :
    gm f z (M.U i) (t.s i) = gm f z (M.U i ⊓ M.U j) (M.g i j) * gm f z (M.U j) (t.s j) := by
  have hm : f z ∈ M.U i ⊓ M.U j := ⟨hi, hj⟩
  exact (gm_res f z _ hm _).symm.trans ((congrArg (gm f z _) (ht i j)).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res f z _ hm _))))

theorem gm_div (M N : LB Y) (f : Z ⟶ Y) (z : Z) (p q : (LB.div M N).ι)
    (hp : f z ∈ (LB.div M N).U p) (hq : f z ∈ (LB.div M N).U q) :
    gm f z ((LB.div M N).U p ⊓ (LB.div M N).U q) ((LB.div M N).g p q) =
      gm f z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm f z (N.U p.2 ⊓ N.U q.2) (N.g p.2 q.2))⁻¹ := by
  have hm : f z ∈ (LB.div M N).U p ⊓ (LB.div M N).U q := ⟨hp, hq⟩
  show gm f z _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z _ hm _)
    ((map_inv _ _).trans (congrArg _ (gm_res f z _ hm _))))

theorem trF_self {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y)
    (z : Z) (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j) : trF φ ε r z j j = 1 :=
  Finset.prod_eq_one fun k _ => by
    rw [gm_self hL (r ≫ φ k) z (Set.mem_iInter.1 hj k), one_zpow]

theorem trF_sum {L : LB X} {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ)
    (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (r : Z ⟶ Y) (z : Z) (j₁ j₁' : K₁ → L.ι) (j₀ j₀' : K → L.ι) :
    trF (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)) r z (Sum.elim j₁ j₀) (Sum.elim j₁' j₀') =
      trF φ₁ ε₁ r z j₁ j₁' * (trF φ₀ ε₀ r z j₀ j₀')⁻¹ := by
  rw [trF, trF, trF, Fintype.prod_sum_type, ← Finset.prod_inv_distrib]
  congr 1
  exact Finset.prod_congr rfl fun k _ => zpow_neg _ _

theorem wchart_sum_le (L : LB X) {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X))
    (φ₁ : K₁ → (Y ⟶ X)) (j₁ : K₁ → L.ι) (j₀ : K → L.ι) :
    LB.wchart L φ₁ j₁ ⊓ LB.wchart L φ₀ j₀ ≤ LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀) :=
  fun _ hy => Set.mem_iInter.2 fun k => by
    cases k with
    | inl k => exact Set.mem_iInter.1 hy.1 k
    | inr k => exact Set.mem_iInter.1 hy.2 k

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem gm_iso_linComb {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K : Type} [Fintype K]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (u : LB.Iso A (LB.LinComb L φ₀ ε₀)) (hu : u.IsGen)
    (y : Y) (j₀ j₀' : K → L.ι) (a a' : A.ι) (h0 : y ∈ LB.wchart L φ₀ j₀) (ha : y ∈ A.U a)
    (h0' : y ∈ LB.wchart L φ₀ j₀') (ha' : y ∈ A.U a') :
    gm (𝟙 Y) y (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) =
      (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀' * (gm (𝟙 Y) y (A.U a ⊓ A.U a') (A.g a a'))⁻¹) *
        gm (𝟙 Y) y (LB.wchart L φ₀ j₀' ⊓ A.U a') (u.s (j₀', a')) := by
  have hp : (𝟙 Y) y ∈ (LB.div (LB.LinComb L φ₀ ε₀) A).U (j₀, a) := ⟨h0, ha⟩
  have hq : (𝟙 Y) y ∈ (LB.div (LB.LinComb L φ₀ ε₀) A).U (j₀', a') := ⟨h0', ha'⟩
  have e1 := gm_gen hu (𝟙 Y) y hp hq
  have e2 := gm_div (LB.LinComb L φ₀ ε₀) A (𝟙 Y) y (j₀, a) (j₀', a') hp hq
  have e3 : gm (𝟙 Y) y (LB.wchart L φ₀ j₀ ⊓ LB.wchart L φ₀ j₀') ((LB.LinComb L φ₀ ε₀).g j₀ j₀') =
      trF φ₀ ε₀ (𝟙 Y) y j₀ j₀' := gm_linComb L φ₀ ε₀ (𝟙 Y) y j₀ j₀' h0 h0'
  rw [e2] at e1
  exact e1.trans (congrArg (fun t => t * (gm (𝟙 Y) y (A.U a ⊓ A.U a') (A.g a a'))⁻¹ *
    gm (𝟙 Y) y (LB.wchart L φ₀ j₀' ⊓ A.U a') (u.s (j₀', a'))) e3)

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem gm_gen_sum {X Y : Scheme.{0}} {L : LB X} {K K₁ : Type} [Fintype K] [Fintype K₁]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ)
    (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))) (hc : c.IsGen)
    (y : Y) (j₁ j₁' : K₁ → L.ι) (j₀ j₀' : K → L.ι) (h1 : y ∈ LB.wchart L φ₁ j₁) (h0 : y ∈ LB.wchart L φ₀ j₀)
    (h1' : y ∈ LB.wchart L φ₁ j₁') (h0' : y ∈ LB.wchart L φ₀ j₀') :
    gm (𝟙 Y) y (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) =
      (trF φ₁ ε₁ (𝟙 Y) y j₁ j₁' * (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀')⁻¹) *
        gm (𝟙 Y) y (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁' j₀')) (c.s (Sum.elim j₁' j₀')) := by
  rw [← trF_sum]
  exact gen_trans hc (𝟙 Y) y (wchart_sum_le L φ₀ φ₁ j₁ j₀ ⟨h1, h0⟩) (wchart_sum_le L φ₀ φ₁ j₁' j₀' ⟨h1', h0'⟩)

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem exists_iso_comp_val {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K K₁ : Type} [Fintype K] [Fintype K₁]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (hL : L.IsLB) (hA : A.IsLB)
    (u : LB.Iso A (LB.LinComb L φ₀ ε₀)) (hu : u.IsGen)
    (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))) (hc : c.IsGen) :
    ∃ u' : LB.Iso A (LB.LinComb L φ₁ ε₁), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z)
      (J : (Z ⟶ X) → L.ι) (a : A.ι), q z ∈ A.U a → Good L z J →
      gm q z _ (u'.s (fun k => J (q ≫ φ₁ k), a)) = gm q z _ (u.s (fun k => J (q ≫ φ₀ k), a)) * val c q z J := by
  have eu := gm_iso_linComb φ₀ ε₀ u hu
  have ec := gm_gen_sum φ₀ ε₀ φ₁ ε₁ c hc
  have glue : ∀ (j₁ : K₁ → L.ι) (a : A.ι), ∃ s : Γ(Y, LB.wchart L φ₁ j₁ ⊓ A.U a)ˣ,
      ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K → L.ι), q z ∈ LB.wchart L φ₁ j₁ → q z ∈ A.U a →
        q z ∈ LB.wchart L φ₀ j₀ →
        gm q z (LB.wchart L φ₁ j₁ ⊓ A.U a) s =
          gm q z (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) *
            gm q z (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) := by
    intro j₁ a
    obtain ⟨W, hW⟩ : ∃ W : (K → L.ι) → Y.Opens, ∀ j₀, W j₀ = LB.wchart L φ₁ j₁ ⊓ A.U a ⊓ LB.wchart L φ₀ j₀ :=
      ⟨_, fun _ => rfl⟩
    have l₀ : ∀ j₀, W j₀ ≤ LB.wchart L φ₁ j₁ ⊓ A.U a := fun j₀ => (hW j₀).le.trans inf_le_left
    have l₁ : ∀ j₀, W j₀ ≤ LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀) := fun j₀ y hy => by
      rw [hW] at hy; exact wchart_sum_le L φ₀ φ₁ j₁ j₀ ⟨hy.1.1, hy.2⟩
    have l₂ : ∀ j₀, W j₀ ≤ LB.wchart L φ₀ j₀ ⊓ A.U a := fun j₀ y hy => by
      rw [hW] at hy; exact ⟨hy.2, hy.1.2⟩
    obtain ⟨uu, hu'⟩ : ∃ uu : ∀ j₀, Γ(Y, W j₀)ˣ, ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K → L.ι),
        q z ∈ W j₀ → gm q z (W j₀) (uu j₀) =
          gm q z (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) *
            gm q z (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) :=
      ⟨fun j₀ => res (l₁ j₀) (c.s (Sum.elim j₁ j₀)) * res (l₂ j₀) (u.s (j₀, a)), fun Z' q z j₀ h =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res q z (l₁ j₀) h _) (gm_res q z (l₂ j₀) h _))⟩
    have memW : ∀ y j₀, y ∈ W j₀ ↔ (y ∈ LB.wchart L φ₁ j₁ ∧ y ∈ A.U a) ∧ y ∈ LB.wchart L φ₀ j₀ := fun y j₀ => by
      rw [hW]; exact Iff.rfl
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart L φ₁ j₁ ⊓ A.U a) W l₀ (fun y hy => by
        choose j₀ hj₀ using fun k => exists_chart hL (φ₀ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j₀, (memW y j₀).2 ⟨hy, Set.mem_iInter.2 hj₀⟩⟩) uu (fun j₀ j₀' y hy => by
        obtain ⟨⟨h1, ha⟩, h0⟩ := (memW y j₀).1 hy.1
        obtain ⟨-, h0'⟩ := (memW y j₀').1 hy.2
        refine (hu' Y (𝟙 Y) y j₀ hy.1).trans (Eq.trans ?_ (hu' Y (𝟙 Y) y j₀' hy.2).symm)
        rw [ec y j₁ j₁ j₀ j₀' h1 h0 h1 h0', eu y j₀ j₀' a a h0 ha h0' ha, trF_self hL φ₁ ε₁ (𝟙 Y) y j₁ h1,
          gm_self hA (𝟙 Y) y ha, _root_.one_mul, _root_.inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, _root_.inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z' q z j₀ h1 ha h0 => ?_⟩
    have hy : q z ∈ W j₀ := (memW _ j₀).2 ⟨⟨h1, ha⟩, h0⟩
    exact (gm_res q z (l₀ j₀) hy s).symm.trans ((congrArg (gm q z (W j₀)) (hs j₀)).trans (hu' Z' q z j₀ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun p p' => unit_ext fun y hy => ?_, fun Z q z J a ha hJ => ?_⟩
  · obtain ⟨⟨h1, ha⟩, h1', ha'⟩ := hy
    choose j₀ hj₀ using fun k => exists_chart hL (φ₀ k y)
    have h0 : y ∈ LB.wchart L φ₀ j₀ := Set.mem_iInter.2 hj₀
    have key : gm (𝟙 Y) y (LB.wchart L φ₁ p.1 ⊓ A.U p.2) (s p.1 p.2) =
        (trF φ₁ ε₁ (𝟙 Y) y p.1 p'.1 * (gm (𝟙 Y) y (A.U p.2 ⊓ A.U p'.2) (A.g p.2 p'.2))⁻¹) *
          gm (𝟙 Y) y (LB.wchart L φ₁ p'.1 ⊓ A.U p'.2) (s p'.1 p'.2) := by
      rw [hs p.1 p.2 Y (𝟙 Y) y j₀ h1 ha h0, hs p'.1 p'.2 Y (𝟙 Y) y j₀ h1' ha' h0,
        ec y p.1 p'.1 j₀ j₀ h1 h0 h1' h0, eu y j₀ j₀ p.2 p'.2 h0 ha h0 ha', trF_self hL φ₀ ε₀ (𝟙 Y) y j₀ h0,
        _root_.inv_one, _root_.mul_one, _root_.one_mul, _root_.mul_mul_mul_comm, _root_.mul_assoc]
    have hm : y ∈ (LB.div (LB.LinComb L φ₁ ε₁) A).U p ⊓ (LB.div (LB.LinComb L φ₁ ε₁) A).U p' :=
      ⟨⟨h1, ha⟩, h1', ha'⟩
    have ed := (gm_div _ _ (𝟙 Y) y p p' hm.1 hm.2).trans
      (congrArg (· * _) (gm_linComb L φ₁ ε₁ (𝟙 Y) y p.1 p'.1 h1 h1'))
    exact (gm_res _ y _ hm _).trans (key.trans ((congrArg₂ (· * ·) ed.symm (gm_res _ y _ hm _).symm).trans
      (map_mul _ _ _).symm))
  · have h1 := hJ.mem φ₁ q
    have h0 := hJ.mem φ₀ q
    refine (hs _ a Z q z (fun k => J (q ≫ φ₀ k)) h1 ha h0).trans ((mul_comm _ _).trans (congrArg _ ?_))
    exact (val_of c q z J _ (fun k => by cases k <;> rfl)).symm

end GlobalTheory.LinCombComp
