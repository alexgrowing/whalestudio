import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem alg_cancel {G : Type*} [CommGroup G] (c a b : G) : a * b⁻¹ = (c * a) * (c * b)⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem alg_chain {G : Type*} [CommGroup G] (a b c : G) : (b * a⁻¹) * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem alg_swap {G : Type*} [CommGroup G] (c a b : G) : c * a = c * (b * a⁻¹)⁻¹ * b := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem ratio_unit {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {V V₁ V₂ : Y.Opens} (h₁ : V ≤ V₁) (h₂ : V ≤ V₂)
    {a₁ : ∀ k, Γ(Y, V₁ ⊓ L.U k)ˣ} {a₂ : ∀ k, Γ(Y, V₂ ⊓ L.U k)ˣ} (ha₁ : LocGen L V₁ a₁) (ha₂ : LocGen L V₂ a₂) :
    ∃ s : Γ(Y, V)ˣ, ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ V → f t ∈ L.U k →
      gm f t V s = gm f t (V₂ ⊓ L.U k) (a₂ k) * (gm f t (V₁ ⊓ L.U k) (a₁ k))⁻¹ := by
  have l₁ : ∀ k, V ⊓ L.U k ≤ V₁ ⊓ L.U k := fun k => inf_le_inf_right _ h₁
  have l₂ : ∀ k, V ⊓ L.U k ≤ V₂ ⊓ L.U k := fun k => inf_le_inf_right _ h₂
  obtain ⟨s, hs⟩ := glue_unit V (fun k => V ⊓ L.U k) (fun k => inf_le_left)
    (fun y hy => by
      obtain ⟨k, hk⟩ := exists_chart hL y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩)
    (fun k => res (l₂ k) (a₂ k) * (res (l₁ k) (a₁ k))⁻¹)
    (fun k k' y hy => by
      rw [map_mul, map_inv, map_mul, map_inv, gm_res _ y (l₂ k) hy.1, gm_res _ y (l₁ k) hy.1,
        gm_res _ y (l₂ k') hy.2, gm_res _ y (l₁ k') hy.2, ha₁ y k k' (h₁ hy.1.1) hy.1.2 hy.2.2,
        ha₂ y k k' (h₂ hy.1.1) hy.1.2 hy.2.2]
      exact (alg_cancel _ _ _).symm)
  refine ⟨s, fun T f t k ht hk => ?_⟩
  have hm : f t ∈ V ⊓ L.U k := ⟨ht, hk⟩
  rw [← gm_res f t (inf_le_left : V ⊓ L.U k ≤ V) hm s, hs k, map_mul, map_inv, gm_res f t (l₂ k) hm,
    gm_res f t (l₁ k) hm]

theorem eq_of_gm {X X' : Scheme.{0}} (p : X' ⟶ X) {V : X.Opens} (hinj : Function.Injective (pullU p V))
    {u v : Γ(X, V)ˣ} (h : ∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) : u = v :=
  hinj (unit_ext fun x' hx' => by
    rw [gm_pull (𝟙 X') p x' V hx', gm_pull (𝟙 X') p x' V hx', Category.id_comp]
    exact h x' hx')

end GlobalTheory.Pinch

namespace GlobalTheory.Pinch

theorem exists_lb_of_matching_gens : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    i' ≫ p = p' ≫ i → GlobalTheory.Pinch.UnitsPatch p i i' p' → ∀ (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB →
    ∀ (w : LB.Iso (L'.pull i') (N.pull p')) (W : X → X.Opens) (a : ∀ x k, Γ(X', p ⁻¹ᵁ (W x) ⊓ L'.U k)ˣ)
      (b : ∀ x l, Γ(Z, i ⁻¹ᵁ (W x) ⊓ N.U l)ˣ), (∀ x, x ∈ W x) →
      (∀ x, GlobalTheory.Pinch.LocGen L' (p ⁻¹ᵁ (W x)) (a x)) → (∀ x, GlobalTheory.Pinch.LocGen N (i ⁻¹ᵁ (W x)) (b x)) →
      (∀ x, GlobalTheory.Pinch.Matches i' p' w (a x) (b x)) → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull p) L' := by
  intro X X' Z Z' p i i' p' hsq hU L' N hL' hN w W a b hW ha hb hm
  have pt : ∀ z : Z', p (i' z) = i (p' z) := fun z => congrArg (fun f => f z) hsq
  have key : ∀ x y, ∃ g : Γ(X, W x ⊓ W y)ˣ, ∀ (x' : X') (k : L'.ι), p x' ∈ W x ⊓ W y → x' ∈ L'.U k →
      gm p x' _ g = gm (𝟙 X') x' _ (a y k) * (gm (𝟙 X') x' _ (a x k))⁻¹ := by
    intro x y
    obtain ⟨s, hs⟩ := ratio_unit hL' (V := p ⁻¹ᵁ (W x ⊓ W y)) (fun _ h => h.1) (fun _ h => h.2) (ha x) (ha y)
    obtain ⟨t, ht⟩ := ratio_unit hN (V := i ⁻¹ᵁ (W x ⊓ W y)) (fun _ h => h.1) (fun _ h => h.2) (hb x) (hb y)
    obtain ⟨u, hu⟩ := (hU (W x ⊓ W y)).2 s t (fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hL' (i' z)
      obtain ⟨l, hl⟩ := exists_chart hN (p' z)
      have hz' : i (p' z) ∈ W x ⊓ W y := pt z ▸ hz
      rw [hs Z' i' z k hz hk, ht Z' p' z l hz' hl, hm x z k l hz.1 hz'.1 hk hl, hm y z k l hz.2 hz'.2 hk hl]
      exact alg_cancel _ _ _)
    refine ⟨u, fun x' k hx hk => ?_⟩
    have e := gm_pull (𝟙 X') p x' _ hx u
    rw [Category.id_comp] at e
    rw [← e, hu]
    exact hs X' (𝟙 X') x' k hx hk
  choose g hg using key
  have hL : (⟨X, W, g⟩ : LB X).IsLB :=
    { cover := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩
      g_self := fun x => eq_of_gm p (hU (W x)).1 fun x' hx => by
        obtain ⟨k, hk⟩ := exists_chart hL' x'
        refine (gm_res p x' _ hx _).trans ((hg x x x' k ⟨hx, hx⟩ hk).trans ?_)
        rw [mul_inv_cancel, map_one]
      cocycle := fun x y z => eq_of_gm p (hU _).1 fun x' hx => by
        obtain ⟨k, hk⟩ := exists_chart hL' x'
        exact ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res p x' _ hx _).trans (hg x y x' k ⟨hx.1.1, hx.1.2⟩ hk))
          ((gm_res p x' _ hx _).trans (hg y z x' k ⟨hx.1.2, hx.2⟩ hk)))).trans
          ((alg_chain _ _ _).trans ((gm_res p x' _ hx _).trans (hg x z x' k ⟨hx.1.1, hx.2⟩ hk)).symm) }
  refine ⟨⟨X, W, g⟩, hL, ⟨fun P => res (fun x' hx' => ⟨mem_pull.1 hx'.2, hx'.1⟩ :
    L'.U P.1 ⊓ ((⟨X, W, g⟩ : LB X).pull p).U P.2 ≤ p ⁻¹ᵁ W (P.2 PUnit.unit) ⊓ L'.U P.1) (a (P.2 PUnit.unit) P.1)⟩, ?_⟩
  rintro ⟨k, J⟩ ⟨k', J'⟩
  apply unit_ext
  intro x' hx'
  have hJ : p x' ∈ W (J PUnit.unit) := mem_pull.1 hx'.1.2
  have hJ' : p x' ∈ W (J' PUnit.unit) := mem_pull.1 hx'.2.2
  have e : gm (𝟙 X') x' (((⟨X, W, g⟩ : LB X).pull p).U J ⊓ ((⟨X, W, g⟩ : LB X).pull p).U J')
      (((⟨X, W, g⟩ : LB X).pull p).g J J') = gm p x' _ (g (J PUnit.unit) (J' PUnit.unit)) := by
    show gm (𝟙 X') x' _ (∏ _k : PUnit, (res _ (pullU p _ (g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    have hq : x' ∈ ((⟨X, W, g⟩ : LB X).pull p).U J ⊓ ((⟨X, W, g⟩ : LB X).pull p).U J' := ⟨hx'.1.2, hx'.2.2⟩
    exact (gm_res _ x' _ hq _).trans ((gm_pull (𝟙 X') p x' (W (J PUnit.unit) ⊓ W (J' PUnit.unit))
      (⟨hJ, hJ'⟩ : p x' ∈ W (J PUnit.unit) ⊓ W (J' PUnit.unit)) _).trans (congrArg (fun f => gm f x' _ (g (J PUnit.unit) (J' PUnit.unit))) (Category.id_comp p)))
  have hdiv : gm (𝟙 X') x' _ ((LB.div L' ((⟨X, W, g⟩ : LB X).pull p)).g (k, J) (k', J')) =
      gm (𝟙 X') x' _ (L'.g k k') * (gm p x' _ (g (J PUnit.unit) (J' PUnit.unit)))⁻¹ :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x' _ hx' _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res _ x' _ hx' _).trans e))))
  refine (gm_res _ x' _ hx' _).trans ((gm_res _ x' _ hx'.1 _).trans ?_)
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) hdiv
    ((gm_res _ x' _ hx' _).trans (gm_res _ x' _ hx'.2 _)))).symm
  have h2 := hg (J PUnit.unit) (J' PUnit.unit) x' k' ⟨hJ, hJ'⟩ hx'.2.1
  rw [h2]
  exact (ha (J PUnit.unit) x' k k' hJ hx'.1.1 hx'.2.1).trans (alg_swap _ _ _)

end GlobalTheory.Pinch
