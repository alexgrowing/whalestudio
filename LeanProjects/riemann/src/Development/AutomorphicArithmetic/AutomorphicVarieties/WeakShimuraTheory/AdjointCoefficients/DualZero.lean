import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

private theorem tri_zero {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (ht : Fin 4 → ℤ)
    (hinj : Function.Injective ht) (hb : ∀ i j, ht i - ht j < 4) (hr : ∀ g i j, ht i < ht j → r g i j = 0)
    (ω : Γ → k) (hω : ∀ i j, ∃ g, r g i i * r g⁻¹ j j ≠ ω g) (F : M4 k →ₗ[k] k)
    (hF : ∀ g Y, F (r g * Y * r g⁻¹) = ω g * F Y) : F = 0 := by
  have hexp : ∀ Y : M4 k, F Y = ∑ a, ∑ b, Y a b * F (Matrix.single a b 1) := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : k) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  have hent : ∀ (A B : M4 k) (i j a b : Fin 4), (A * (Matrix.single i j 1 : M4 k) * B : M4 k) a b = A a i * B j b := by
    intro A B i j a b
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul]
  have main : ∀ n : ℕ, ∀ i j, 4 - (n : ℤ) ≤ ht i - ht j → F (Matrix.single i j 1) = 0 := by
    intro n
    induction n with
    | zero =>
      intro i j hij
      exfalso
      have := hb i j
      push_cast at hij
      omega
    | succ n ih =>
      intro i j hij
      by_cases hlt : 4 - (n : ℤ) ≤ ht i - ht j
      · exact ih i j hlt
      obtain ⟨g, hg⟩ := hω i j
      have hsum := hF g (Matrix.single i j 1)
      rw [hexp (r g * Matrix.single i j 1 * r g⁻¹)] at hsum
      simp only [hent] at hsum
      have inner : ∑ b, r g i i * r g⁻¹ j b * F (Matrix.single i b 1)
          = r g i i * r g⁻¹ j j * F (Matrix.single i j 1) := by
        refine Finset.sum_eq_single j (fun b _ hbj => ?_) (fun h => absurd (Finset.mem_univ _) h)
        by_cases hjb : ht j < ht b
        · rw [hr g⁻¹ j b hjb]
          ring
        · have hne : ht b ≠ ht j := fun e => hbj (hinj e)
          rw [ih i b (by push_cast at hij hlt ⊢; omega)]
          ring
      have outer : ∑ a, ∑ b, r g a i * r g⁻¹ j b * F (Matrix.single a b 1)
          = ∑ b, r g i i * r g⁻¹ j b * F (Matrix.single i b 1) := by
        refine Finset.sum_eq_single i (fun a _ hai => ?_) (fun h => absurd (Finset.mem_univ _) h)
        apply Finset.sum_eq_zero
        intro b _
        by_cases hia : ht a < ht i
        · rw [hr g a i hia]
          ring
        by_cases hjb : ht j < ht b
        · rw [hr g⁻¹ j b hjb]
          ring
        have hne : ht a ≠ ht i := fun e => hai (hinj e)
        rw [ih a b (by push_cast at hij hlt ⊢; omega)]
        ring
      rw [outer, inner] at hsum
      have e : (r g i i * r g⁻¹ j j - ω g) * F (Matrix.single i j 1) = 0 := by
        rw [sub_mul, hsum, sub_self]
      exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hg)
  apply LinearMap.ext
  intro Y
  rw [hexp Y, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  rw [main 8 a b (by have := hb b a; push_cast; omega), mul_zero]

private theorem adj_conj {Γ k : Type} [Group Γ] [CommRing k] {r : Γ →* M4 k} (h : ∀ g, ∃ ν, IsGSp ν (r g)) (g : Γ)
    (X : M4 k) : adj (r g * X * r g⁻¹) = r g * adj X * r g⁻¹ := by
  obtain ⟨ν, hν⟩ := h g
  obtain ⟨μ, hμ⟩ := h g⁻¹
  have G := grp k
  have e1 : r g * r g⁻¹ = 1 := by rw [← r.map_mul, mul_inv_cancel, r.map_one]
  have e2 : r g⁻¹ * r g = 1 := by rw [← r.map_mul, inv_mul_cancel, r.map_one]
  have a1 : adj (r g) = ν • r g⁻¹ := G.2.2.2.2.2.2.1 ν _ _ hν e1
  have a2 : adj (r g⁻¹) = μ • r g := G.2.2.2.2.2.2.1 μ _ _ hμ e2
  have hprod := G.2.2.2.2.2.2.2.1 ν μ _ _ hν hμ
  rw [e1] at hprod
  have e : adj (1 : M4 k) * 1 = (ν * μ) • (1 : M4 k) := hprod
  rw [G.2.2.2.2.1, Matrix.mul_one] at e
  have e00 := congrFun (congrFun e 0) 0
  simp at e00
  have hμν : μ * ν = 1 := by rw [mul_comm]; exact e00.symm
  rw [G.1, G.1, a1, a2, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, hμν, one_smul, Matrix.mul_assoc]

private theorem rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ)
    (hm : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) (i j : Fin 4) (g : Γ) :
    Φ.rt (wt i j) g = Φ.χ i g * Φ.χ j g⁻¹ := by
  have hd : Φ.χ 3 g = Φ.ν g * (Φ.χ 0 g)⁻¹ := eq_mul_inv_of_mul_eq (by rw [mul_comm]; exact hm 0 g)
  have hc : Φ.χ 2 g = Φ.ν g * (Φ.χ 1 g)⁻¹ := eq_mul_inv_of_mul_eq (by rw [mul_comm]; exact hm 1 g)
  rw [map_inv]
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hc, hd] <;>
    (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]; abel)

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.dualZero :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k), Φ.Ok a → ∀ (c : PD Φ.ι Γ k), Φ.Res a c → ∀ (h : ∀ g, ∃ x, IsGSp x (c.r g)) (ω : Γ → k), (∀ w, ∃ g, a (Φ.rt w g) ≠ ω g) → ∀ f : sp4 k →ₗ[k] k, (∀ g X, f (adSp c.r h g X) = ω g * f X) → f = 0 := by
  intro O Γ _ _ _ Φ k _ a hok c hres h ω hωw f hf
  have G := grp k
  have adj_add := G.2.2.1
  have adj_smul := G.2.2.2.1
  have adj_adj := G.2.1
  let AdjL : M4 k →ₗ[k] M4 k := { toFun := adj, map_add' := adj_add, map_smul' := adj_smul }
  have h2 : (2 : k) ≠ 0 := hok.two.ne_zero
  set t : k := (2 : k)⁻¹ with htdef
  have hsub : ∀ Y : M4 k, adj (Y - adj Y) = adj Y - Y := by
    intro Y
    have e := map_sub AdjL Y (adj Y)
    simp only [AdjL, LinearMap.coe_mk, AddHom.coe_mk] at e
    rw [e, adj_adj]
  let π : M4 k →ₗ[k] sp4 k := LinearMap.codRestrict (sp4 k) (t • (LinearMap.id - AdjL)) (fun Y => by
    show adj (t • (Y - adj Y)) = -(t • (Y - adj Y))
    rw [adj_smul, hsub, ← smul_neg, neg_sub])
  have hπ : ∀ Y, ((π Y : sp4 k) : M4 k) = t • (Y - adj Y) := fun Y => rfl
  let F : M4 k →ₗ[k] k := f ∘ₗ π
  have hFc : ∀ g Y, F (c.r g * Y * c.r g⁻¹) = ω g * F Y := by
    intro g Y
    have e : π (c.r g * Y * c.r g⁻¹) = adSp c.r h g (π Y) := by
      apply Subtype.ext
      rw [adSp_val, hπ, hπ, adj_conj h g Y]
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    show f (π _) = ω g * f (π Y)
    rw [e, hf]
  have hfix : ∀ X : sp4 k, π X = X := by
    intro X
    apply Subtype.ext
    rw [hπ]
    have hX : adj (X : M4 k) = -(X : M4 k) := X.2
    rw [hX, sub_neg_eq_add, ← two_smul k (X : M4 k), smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hω' : ∀ i j, ∃ g, c.r g i i * c.r g⁻¹ j j ≠ ω g := by
    intro i j
    obtain ⟨g, hg⟩ := hωw (wt i j)
    refine ⟨g, ?_⟩
    rw [hres.diag, hres.diag]
    rw [rt_wt Φ hok.mul i j g, Units.val_mul, map_mul] at hg
    exact hg
  have key : ∀ ht : Fin 4 → ℤ, Function.Injective ht → (∀ i j, ht i - ht j < 4) →
      (∀ g i j, ht i < ht j → c.r g i j = 0) → f = 0 := by
    intro ht hi hb hr
    have hF0 := tri_zero c.r ht hi hb hr ω hω' F hFc
    apply LinearMap.ext
    intro X
    have e : F X = 0 := by rw [hF0]; rfl
    calc f X = f (π X) := by rw [hfix X]
      _ = F X := rfl
      _ = 0 := e
  rcases hres.shape with ⟨hS, _⟩ | hS
  · refine key ![-3, -1, -2, 0] (by decide) (by decide) ?_
    intro g i j hlt
    apply hS g i j
    · fin_cases i <;> fin_cases j <;> simp at hlt ⊢
    · fin_cases i <;> fin_cases j <;> simp [nP, wt, lamW, muW, wAl, wBe, wPs, wTh] at hlt ⊢
  · refine key ![-3, -2, -1, 0] (by decide) (by decide) ?_
    intro g i j hlt
    apply hS g i j
    · fin_cases i <;> fin_cases j <;> simp at hlt ⊢
    · fin_cases i <;> fin_cases j <;> simp [nM, wt, lamW, muW, wAl, wBe, wPs, wTh] at hlt ⊢
