import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

namespace DepthBdd

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone_of_strict {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hstr : IsStrict bar φ γ')
    (hlin' : φ.LinearOn γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hstr
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
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hlin' b hb
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

theorem zero_mem_rcone (u : Fin m → LinearMap.BilinForm ℤ X) : (0 : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) ∈ rcone u :=
  ⟨0, fun _ => le_rfl, by simp⟩

theorem add_mem_rcone {u : Fin m → LinearMap.BilinForm ℤ X} {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ rcone u)
    (h' : B' ∈ rcone u) : B + B' ∈ rcone u := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨t', ht', rfl⟩ := h'
  exact ⟨t + t', fun i => add_nonneg (ht i) (ht' i), by simp [add_smul, Finset.sum_add_distrib]⟩

theorem smul_mem_rcone {u : Fin m → LinearMap.BilinForm ℤ X} {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ rcone u) {s : ℝ}
    (hs : 0 ≤ s) : s • B ∈ rcone u := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨s • t, fun i => mul_nonneg hs (ht i), by simp [Finset.smul_sum, smul_smul]⟩

theorem finsum_mem_rcone {u : Fin m → LinearMap.BilinForm ℤ X} {ι : Type} (s : Finset ι)
    (f : ι → X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (h : ∀ i ∈ s, f i ∈ rcone u) : ∑ i ∈ s, f i ∈ rcone u :=
  Finset.sum_induction f (· ∈ rcone u) (fun _ _ => add_mem_rcone) (zero_mem_rcone u) h

end DepthBdd

end GlobalTheory.PolFan

namespace GlobalTheory.PolFan

open DepthBdd in

theorem depthSet_bddAbove_of_unique_centre : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X →
    (∀ y, 0 ≤ v y y) → v ≠ 0 →
    (∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v) →
    ∀ (n : ℕ) (π : (Fin n → O) →ₗ[O] X), Function.Surjective π →
      BddAbove (depthSet bar ψ w n (fun a b => B (π a) (π b))) := by
  intro O _ bar ψ w X _ _ _ m γ B v hγ hB hv hvp hv0 huniq n π hπ
  obtain ⟨y₀, hy₀⟩ : ∃ y, 0 < v y y := by
    by_contra hc
    push_neg at hc
    apply hv0
    have hz : ∀ y, v y y = 0 := fun y => le_antisymm (hc y) (hvp y)
    refine LinearMap.ext₂ fun x y => ?_
    have h := hz (x + y)
    simp only [map_add, LinearMap.add_apply, hz x, hz y, hv.1 y x] at h
    simp only [LinearMap.zero_apply]
    omega
  have hy₀' : (0 : ℝ) < v y₀ y₀ := by exact_mod_cast hy₀
  refine ⟨max (B y₀ y₀ / v y₀ y₀) 0, ?_⟩
  rintro t ⟨X₂, i1, i2, i3, ρ, B₂, hρ, hrad, hB2, ht, m₂, δ₂, v₂, hδ₂, hv₂, hv₂p, hw, ⟨e, he, hev⟩, -, ⟨d, hd, hdB⟩⟩
  rcases ht.eq_or_lt with rfl | htpos
  · exact le_max_right _ _
  refine le_max_of_le_left ?_
  have hker : LinearMap.ker π ≤ LinearMap.ker ρ := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    refine hrad _ fun y => ?_
    obtain ⟨y', rfl⟩ := hρ y
    have h1 := hB2 x y'
    simp only [hx, map_zero, LinearMap.zero_apply] at h1
    exact h1.symm
  let ρ' : X →ₗ[O] X₂ :=
    (LinearMap.ker π).liftQ ρ hker ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
  have hρ' : ∀ a, ρ' (π a) = ρ a := fun a => by
    have : (π.quotKerEquivOfSurjective hπ).symm (π a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hρs : Function.Surjective ρ' := fun x => by
    obtain ⟨a, rfl⟩ := hρ x
    exact ⟨π a, hρ' a⟩
  have hBB : ∀ x y, B x y = B₂ (ρ' x) (ρ' y) := fun x y => by
    obtain ⟨a, rfl⟩ := hπ x
    obtain ⟨b, rfl⟩ := hπ y
    rw [hρ', hρ']
    exact hB2 a b
  have hev' : ∀ p q, (v₂ p q : ℝ) = ∑ i, e i * (δ₂ i p q : ℝ) := fun p q => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hev p q
  have hdB' : ∀ p q, B₂ p q - t * (v₂ p q : ℝ) = ∑ i, d i * (δ₂ i p q : ℝ) := fun p q => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hdB p q
  set δ : Fin m₂ → LinearMap.BilinForm ℤ X := fun i => pull ρ' (δ₂ i) with hδdef
  set v' : LinearMap.BilinForm ℤ X := pull ρ' v₂ with hv'def
  set a : Fin m₂ → ℝ := fun i => d i + t * e i with hadef
  have ha : ∀ i, 0 ≤ a i := fun i => add_nonneg (hd i) (mul_nonneg htpos.le (he i))
  have hsumB : B = ∑ i, a i • toReal (δ i) := LinearMap.ext₂ fun x y => by
    have h1 := hdB' (ρ' x) (ρ' y)
    have h2 := hev' (ρ' x) (ρ' y)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, smul_eq_mul, hBB, δ, a, add_mul,
      Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ← h2, ← h1]
    ring
  have hv'sum : toReal v' = ∑ i, e i • toReal (δ i) := LinearMap.ext₂ fun x y => by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, smul_eq_mul, δ, v']
    exact hev' _ _
  have hBv' : B - t • toReal v' = ∑ i, d i • toReal (δ i) := LinearMap.ext₂ fun x y => by
    simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, smul_eq_mul, δ,
      v', hBB]
    exact hdB' _ _
  obtain ⟨b, hb, hBb⟩ := hB
  have hlinδ : ψ.LinearOn δ := (linearOn_pull_iff hρs).2 hδ₂.linear
  have key : ∀ i, a i ≠ 0 → toReal (δ i) ∈ rcone γ := fun i hai => by
    obtain ⟨k, c, hk, hkc⟩ := inCone_of_strict hγ.strict hγ.linear (fun i => pull_mem ρ' (hδ₂.mem i))
      (fun i y => hδ₂.nonneg i (ρ' y)) ha hb ((linearOn_iff ψ δ).1 hlinδ a ha) (hsumB.symm.trans hBb) i hai
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    refine ⟨fun j => (c j : ℝ) / k, fun j => by positivity, LinearMap.ext₂ fun x y => ?_⟩
    have h := LinearMap.congr_fun₂ hkc x y
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h
    have h' : (k : ℝ) * (δ i x y : ℝ) = ∑ j, (c j : ℝ) * (γ j x y : ℝ) := by exact_mod_cast h
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
    rw [show ∑ j, (c j : ℝ) / k * (γ j x y : ℝ) = (∑ j, (c j : ℝ) * (γ j x y : ℝ)) / k by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => by ring, ← h']
    field_simp
  have hterm : ∀ s : Fin m₂ → ℝ, (∀ i, 0 ≤ s i) → (∀ i, 0 < s i → 0 < a i) → ∑ i, s i • toReal (δ i) ∈ rcone γ :=
    fun s hs hsa => finsum_mem_rcone _ _ fun i _ => by
      rcases (hs i).eq_or_lt with h | h
      · rw [← h, zero_smul]; exact zero_mem_rcone γ
      · exact smul_mem_rcone (key i (hsa i h).ne') (hs i)
  have hv'in : InRCone γ v' := by
    show toReal v' ∈ rcone γ
    rw [hv'sum]
    exact hterm e he fun i h => by have := hd i; simp only [a]; nlinarith
  have hBin : B - t • toReal v' ∈ rcone γ := by
    rw [hBv']
    exact hterm d hd fun i h => by have := he i; simp only [a]; nlinarith
  have hvv : v' = v := huniq v' (pull_mem ρ' hv₂) (fun y => hv₂p (ρ' y))
    (by rw [evalZ_pull w hρs]; exact hw) hv'in
  rw [hvv] at hBin
  obtain ⟨s, hs, hsB⟩ := hBin
  have h0 := LinearMap.congr_fun₂ hsB y₀ y₀
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, smul_eq_mul] at h0
  have hnn : 0 ≤ ∑ j, s j * (γ j y₀ y₀ : ℝ) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hs j) (by exact_mod_cast hγ.nonneg j y₀)
  rw [le_div_iff₀ hy₀']
  linarith

end GlobalTheory.PolFan
