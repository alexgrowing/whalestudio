import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

namespace StarUpper

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone_cell {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCell bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

omit [Module O X] [Module.Finite O X] in

theorem sum_mem_rcone {p : ℕ} {δ : Fin p → LinearMap.BilinForm ℤ X} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (x : Fin p → ℝ) (hx : ∀ i, 0 ≤ x i)
    (h : ∀ i, x i ≠ 0 → ∃ (k : ℕ) (d : Fin m → ℕ), 0 < k ∧ k • δ i = ∑ j, d j • γ j) :
    ∑ i, x i • toReal (δ i) ∈ rcone γ := by
  classical
  have hi : ∀ i, ∃ g : Fin m → ℝ, (∀ j, 0 ≤ g j) ∧ x i • toReal (δ i) = ∑ j, g j • toReal (γ j) := by
    intro i
    by_cases h0 : x i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    obtain ⟨k, d, hk, hkd⟩ := h i h0
    have hxi := hx i
    refine ⟨fun j => x i / k * d j, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
    have e := LinearMap.congr_fun₂ hkd a b
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul, smul_eq_mul] at e
    have e' : (k : ℝ) * (δ i a b : ℝ) = ∑ j, (d j : ℝ) * (γ j a b : ℝ) := by exact_mod_cast e
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, smul_eq_mul]
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    calc x i * (δ i a b : ℝ) = x i / k * ((k : ℝ) * (δ i a b : ℝ)) := by field_simp
      _ = _ := by rw [e', Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  choose g hg hgs using hi
  refine ⟨fun j => ∑ i, g i j, fun j => Finset.sum_nonneg fun i _ => hg i j, ?_⟩
  rw [Finset.sum_congr rfl fun i _ => hgs i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

end StarUpper

open StarUpper in

theorem evalR_starDepth_le : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (s : ℝ),
    IsCell bar ψ γ → B ∈ rcone γ → 0 ≤ s → (∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v →
      ∀ t : ℝ, 0 < t → B - t • toReal v ∈ rcone γ → t ≤ s) → evalR (starDepth bar ψ w) B ≤ s := by
  intro O _ bar ψ w X _ _ _ m γ B s hγ hB hs H
  obtain ⟨c, hc, hBc⟩ := hB
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' O X
  show (starDepth bar ψ w).eval X (fun a b => B a b) ≤ s
  rw [InvFun.eval_eq _ hq]
  refine Real.sSup_le (fun t ht => ?_) hs
  obtain ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB₁, ht0, m₁, γ₁, v₁, hγ₁, hv₁, hv₁p, hwv₁, ⟨e, he, hev⟩, -,
    ⟨d, hd, hdv⟩⟩ := ht
  rcases ht0.eq_or_lt with rfl | htpos
  · exact hs

  have hker : LinearMap.ker q ≤ LinearMap.ker ρ := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    refine hrad _ fun y => ?_
    obtain ⟨y', rfl⟩ := hρ y
    have h1 := hB₁ x y'
    simp only [hx, map_zero, LinearMap.zero_apply] at h1
    exact h1.symm
  let ρ' : X →ₗ[O] X₁ := (LinearMap.ker q).liftQ ρ hker ∘ₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hρ' : ∀ a, ρ' (q a) = ρ a := fun a => by
    have : (q.quotKerEquivOfSurjective hq).symm (q a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hρs : Function.Surjective ρ' := fun x => by
    obtain ⟨a, rfl⟩ := hρ x
    exact ⟨q a, hρ' a⟩
  have hBB : ∀ x y, B x y = B₁ (ρ' x) (ρ' y) := fun x y => by
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    rw [hρ', hρ']
    exact hB₁ a b

  set δ : Fin m₁ → LinearMap.BilinForm ℤ X := fun i => pull ρ' (γ₁ i) with hδ
  set v : LinearMap.BilinForm ℤ X := pull ρ' v₁ with hv
  have hv_eq : toReal v = ∑ i, e i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hev (ρ' a) (ρ' b)
    simpa [hδ, hv, LinearMap.sum_apply] using this
  have hd_eq : B - t • toReal v = ∑ i, d i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hdv (ρ' a) (ρ' b)
    simpa [hδ, hv, hBB, LinearMap.sum_apply] using this
  have hrel : ∑ i, (d i + t * e i) • toReal (δ i) = ∑ j, c j • toReal (γ j) := by
    rw [← hBc]
    refine LinearMap.ext₂ fun a b => ?_
    have h1 := LinearMap.congr_fun₂ hd_eq a b
    have h2 := LinearMap.congr_fun₂ hv_eq a b
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at h1 h2 ⊢
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [← h1, ← h2]
    ring
  have hnn : ∀ i, 0 ≤ d i + t * e i := fun i => add_nonneg (hd i) (mul_nonneg ht0 (he i))
  have hlin : evalR ψ (∑ i, (d i + t * e i) • toReal (δ i)) = ∑ i, (d i + t * e i) * ψ.evalZ (δ i) :=
    (linearOn_iff ψ δ).1 ((linearOn_pull_iff hρs).2 hγ₁.linear) _ hnn
  have hcone := inCone_cell hγ (fun i => pull_mem ρ' (hγ₁.mem i)) (fun i y => hγ₁.nonneg i _) hnn hc hlin hrel
  have hInR : InRCone γ v := by
    obtain ⟨c', hc', h'⟩ := sum_mem_rcone e he fun i hi => hcone i
      (add_pos_of_nonneg_of_pos (hd i) (mul_pos htpos (lt_of_le_of_ne (he i) (Ne.symm hi)))).ne'
    exact ⟨c', hc', hv_eq.trans h'⟩
  have hBt : B - t • toReal v ∈ rcone γ := by
    rw [hd_eq]
    exact sum_mem_rcone d hd fun i hi => hcone i
      (add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hd i) (Ne.symm hi)) (mul_nonneg ht0 (he i))).ne'
  exact H v (pull_mem ρ' hv₁) (fun y => hv₁p _) (by rw [hv, evalZ_pull w hρs]; exact hwv₁) hInR t htpos hBt

end GlobalTheory.PolFan
