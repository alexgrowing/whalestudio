import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Mum

variable {X Y Z : Scheme.{0}} {L : LB X} {k k' : ℕ}

abbrev secGerm (u : Y ⟶ X) (y : Y) (s : H0 L k) (i : Fin 1 → L.ι) : Y.presheaf.stalk y :=
  gs u y (secChart L i) (s.f i)

theorem secRatioEq_iff_germ {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'} :
    SecRatioEq L u v s₁ s₂ t₁ t₂ ↔ ∀ (y : Y) (i i' : Fin 1 → L.ι), u y ∈ secChart L i → v y ∈ secChart L i' →
      secGerm u y s₁ i * secGerm v y t₂ i' = secGerm u y s₂ i * secGerm v y t₁ i' := by
  have key : ∀ (y : Y) (i i' : Fin 1 → L.ι) (hi : u y ∈ secChart L i) (hi' : v y ∈ secChart L i') (s : H0 L k)
      (t : H0 L k'), gs (𝟙 Y) y (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
        ((Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
          ((u.app (secChart L i)).hom (s.f i)) *
        (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
          ((v.app (secChart L i')).hom (t.f i'))) = secGerm u y s i * secGerm v y t i' := by
    intro y i i' hi hi' s t
    have hy : (𝟙 Y : Y ⟶ Y) y ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := ⟨hi, hi'⟩
    rw [gs_mul _ _ _ hy, gs_res _ _ _ hy, gs_res _ _ _ hy]
    exact congrArg₂ (· * ·) (gs_pull (𝟙 Y) u y _ hi _) (gs_pull (𝟙 Y) v y _ hi' _)
  refine ⟨fun h y i i' hi hi' => ?_, fun h i i' => fn_ext fun y hy => ?_⟩
  · rw [← key y i i' hi hi', ← key y i i' hi hi', h i i']
  · rw [key y i i' hy.1 hy.2, key y i i' hy.1 hy.2]
    exact h y i i' hy.1 hy.2

theorem exists_unit_secGerm (k : ℕ) (u : Y ⟶ X) (y : Y) {i j : Fin 1 → L.ι} (hi : u y ∈ secChart L i)
    (hj : u y ∈ secChart L j) :
    ∃ c : (Y.presheaf.stalk y)ˣ, ∀ s : H0 L k, secGerm u y s i = c.val * secGerm u y s j := by
  have hy : u y ∈ secChart L i ⊓ secChart L j := ⟨hi, hj⟩
  refine ⟨gm u y (secChart L i ⊓ secChart L j)
    ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))).g i j), fun s => ?_⟩
  have h := congrArg (gs u y (secChart L i ⊓ secChart L j)) (s.compat i j)
  refine (gs_res u y inf_le_left hy _).symm.trans (h.trans ((gs_mul u y _ hy _ _).trans ?_))
  exact congrArg₂ (· * ·) (gs_unit u y _ hy _) (gs_res u y inf_le_right hy _)

theorem secRatioEq_of_exists_germ {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'}
    (h : ∀ y : Y, ∃ i i' : Fin 1 → L.ι, u y ∈ secChart L i ∧ v y ∈ secChart L i' ∧
      secGerm u y s₁ i * secGerm v y t₂ i' = secGerm u y s₂ i * secGerm v y t₁ i') :
    SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  refine secRatioEq_iff_germ.2 fun y j j' hj hj' => ?_
  obtain ⟨i, i', hi, hi', e⟩ := h y
  obtain ⟨c, hc⟩ := exists_unit_secGerm k u y hj hi
  obtain ⟨c', hc'⟩ := exists_unit_secGerm k' v y hj' hi'
  rw [hc, hc, hc', hc']
  linear_combination (c.val * c'.val) * e

theorem secGerm_comp (w : Z ⟶ Y) (u : Y ⟶ X) (z : Z) (s : H0 L k) {i : Fin 1 → L.ι} (hi : u (w z) ∈ secChart L i) :
    secGerm (w ≫ u) z s i = (w.stalkMap z).hom (secGerm u (w z) s i) := by
  have key : ∀ a : Γ(X, secChart L i), gs (w ≫ u) z _ a = (w.stalkMap z).hom (gs u (w z) _ a) := fun a => by
    rw [gs_eq u (w z) _ hi, ← gs_pull w u z _ hi, gs_eq w z _ hi]
    exact (Scheme.Hom.germ_stalkMap_apply w _ z hi _).symm
  exact key _

theorem SecRatioEq.comp {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'} (h : SecRatioEq L u v s₁ s₂ t₁ t₂)
    (w : Z ⟶ Y) : SecRatioEq L (w ≫ u) (w ≫ v) s₁ s₂ t₁ t₂ := by
  refine secRatioEq_iff_germ.2 fun z i i' hi hi' => ?_
  rw [secGerm_comp w u z _ hi, secGerm_comp w u z _ hi, secGerm_comp w v z _ hi', secGerm_comp w v z _ hi',
    ← map_mul, ← map_mul, secRatioEq_iff_germ.1 h (w z) i i' hi hi']

theorem app_injective_of_isDominant [IsReduced Y] (w : Z ⟶ Y) [IsDominant w] (W : Y.Opens) :
    Function.Injective (w.app W).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply eq_zero_of_basicOpen_eq_bot
  by_contra hne
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  obtain ⟨z, hz⟩ := w.denseRange.exists_mem_open (Y.basicOpen a).isOpen ⟨y, hy⟩
  have hz' : z ∈ w ⁻¹ᵁ Y.basicOpen a := hz
  rw [Scheme.preimage_basicOpen, ha, Scheme.basicOpen_zero] at hz'
  exact hz'

theorem SecRatioEq.of_isDominant [IsReduced Y] (w : Z ⟶ Y) [IsDominant w] {u v : Y ⟶ X} {s₁ s₂ : H0 L k}
    {t₁ t₂ : H0 L k'} (h : SecRatioEq L (w ≫ u) (w ≫ v) s₁ s₂ t₁ t₂) : SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  intro i i'
  apply app_injective_of_isDominant w
  refine fn_ext fun z hz => ?_
  have hz' : w z ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := hz
  rw [gs_pull (𝟙 Z) w z _ hz', gs_pull (𝟙 Z) w z _ hz', Category.id_comp, gs_mul _ _ _ hz', gs_mul _ _ _ hz',
    gs_res _ _ _ hz', gs_res _ _ _ hz', gs_res _ _ _ hz', gs_res _ _ _ hz']
  exact (congrArg₂ (· * ·) (gs_pull w u z _ hz'.1 _) (gs_pull w v z _ hz'.2 _)).trans
    ((secRatioEq_iff_germ.1 h z i i' hz'.1 hz'.2).trans
      (congrArg₂ (· * ·) (gs_pull w u z _ hz'.1 _) (gs_pull w v z _ hz'.2 _)).symm)

def VeryAmpleAlong {K : Type} [CommRing K] {A : Scheme.{0}} (p : A ⟶ Spec (CommRingCat.of K)) (π : A ⟶ X)
    (L : LB X) {k m : ℕ} (σ : Fin (m + 1) → H0 L k) : Prop :=
  (⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) = ⊤) ∧ ∀ i, IsAffineOpen (π ⁻¹ᵁ nonzeroLocus (σ i)) ∧
    ∃ r : Fin (m + 1) → Γ(A, π ⁻¹ᵁ nonzeroLocus (σ i)),
      (∀ (j : Fin (m + 1)) (c : Fin 1 → L.ι) (a : A), π a ∈ nonzeroLocus (σ i) → π a ∈ secChart L c →
        secGerm π a (σ j) c = gs (𝟙 A) a (π ⁻¹ᵁ nonzeroLocus (σ i)) (r j) * secGerm π a (σ i) c) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) r)

end GlobalTheory.Mum
