import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeOnCentreCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey.OffCell

theorem lin_eq_sum {X : Type} [AddCommGroup X] {n : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X}
    {t : Fin n → ℝ} (hsum : toReal β = ∑ i, t i • toReal (u i)) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (ℓ β : ℝ) = ∑ i, t i * ℓ (u i) := by
  have h1 : ∑ i : Fin (n + 1), (Fin.cons (-1) t : Fin (n + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β u : Fin (n + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  simp at h2
  linarith

theorem inRCone_of_sum {X : Type} [AddCommGroup X] {n m : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X}
    {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {t : Fin n → ℝ} (ht : ∀ i, 0 ≤ t i)
    (hsum : toReal β = ∑ i, t i • toReal (u i)) (h : ∀ i, t i ≠ 0 → InRCone γ (u i)) : InRCone γ β := by
  have h' : ∀ i, ∃ c : Fin m → ℝ, (∀ j, 0 ≤ c j) ∧ t i • toReal (u i) = ∑ j, c j • toReal (γ j) := fun i => by
    by_cases h0 : t i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    · obtain ⟨c, hc, e⟩ := h i h0
      refine ⟨fun j => t i * c j, fun j => mul_nonneg (ht i) (hc j), ?_⟩
      rw [e, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  choose c hc e using h'
  refine ⟨fun j => ∑ i, c i j, fun j => Finset.sum_nonneg fun i _ => hc i j, ?_⟩
  rw [hsum, Finset.sum_congr rfl fun i _ => e i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

theorem inRCone_of_nsmul {X : Type} [AddCommGroup X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {k : ℕ} {c : Fin m → ℕ} (hk : 0 < k) (e : k • β = ∑ i, c i • γ i) : InRCone γ β := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨fun i => c i / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 := congrArg (fun B : LinearMap.BilinForm ℤ X => ((B a b : ℤ) : ℝ)) e
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h1
  push_cast at h1
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hk'.ne'
  rw [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by field_simp

theorem arith {K N C b h₀ f ps h l p : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C) (hb : 0 ≤ b) (hh₀ : 1 ≤ h₀) (hf : 1 ≤ f)
    (hfe : f = l - N * p) (hp : p ≤ b) (hps : ps ≤ 1) (hh : -h ≤ C * l) (hK : N + N * C + N ^ 2 * C * b + 1 ≤ K) :
    N * h₀ * ps - N * h < K * h₀ * (l - N * p) := by
  rw [← hfe]
  have hl : l = f + N * p := by linarith
  have hhf : 1 ≤ h₀ * f := by nlinarith
  have a1 : (N + N * C + N ^ 2 * C * b + 1) * (h₀ * f) ≤ K * (h₀ * f) := by gcongr
  have a2 : N * h₀ * ps ≤ N * (h₀ * f) := by
    rw [mul_assoc]; gcongr; linarith
  have a3 : N * C * f ≤ N * C * (h₀ * f) := by
    gcongr; nlinarith
  have a4 : N ^ 2 * C * b ≤ N ^ 2 * C * b * (h₀ * f) := le_mul_of_one_le_right (by positivity) hhf
  have a5 : N * (-h) ≤ N * (C * l) := by gcongr
  have a6 : N ^ 2 * C * p ≤ N ^ 2 * C * b := by gcongr
  rw [hl] at a5
  nlinarith

theorem off_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (b : ℕ), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → ∀ C : ℕ, (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β) ≤ C * ℓ β) → ∀ K : ℕ, N + N * C + N ^ 2 * C * b + 1 ≤ K → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ¬ InRCone γ β → (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ β - N * h β < K * h β₀ * (ℓ β - N * ψ.evalZ β) := by
  intro E _ _ _ H q ψ w b hψ hw X _ _ _ _ hX hgen m γ N ℓ hγ hN hsw β₀ hβ₀ hβ₀n hw₀ hc₀ m' s h hcut hpos C hC K hK β hβ hβn
    hoff
  have hon := (GlobalTheory.T.starDepth_le_on_centre_cell E H q ψ w hψ hw X hX m γ hγ β₀ hβ₀ hβ₀n hw₀ hc₀ m' s h hcut hpos).1
  obtain ⟨n, u, hu, hun, hlψ, hlp, hub, hu1, t, ht, hsum⟩ := hgen β hβ hβn
  have hh₀ : (1 : ℝ) ≤ h β₀ := by exact_mod_cast hpos
  have hoffu : ∀ i, ¬ InRCone γ (u i) → (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i) <
      K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i)) := fun i hi => by
    obtain ⟨z, hz⟩ := (hψ X hX).integral (u i) (hu i) (hun i)
    have hle := hsw.2.1 (u i) (hu i) (hun i)
    have hne : (N : ℝ) * ψ.evalZ (u i) ≠ ℓ (u i) := fun e => by
      obtain ⟨k, c, hk, e'⟩ := hsw.2.2 (u i) (hu i) (hun i) e
      exact hi (inRCone_of_nsmul hk e')
    have hlt : (N : ℤ) * z < ℓ (u i) := by
      have := lt_of_le_of_ne hle hne
      rw [hz] at this
      exact_mod_cast this
    have hf : (1 : ℝ) ≤ ℓ (u i) - N * ψ.evalZ (u i) := by
      rw [hz]
      have : (1 : ℤ) ≤ ℓ (u i) - N * z := by omega
      exact_mod_cast this
    refine arith (C := C) (b := b) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hh₀ hf rfl (hub i) (hu1 i) ?_ ?_
    · exact_mod_cast hC (u i) (hu i) (hun i)
    · exact_mod_cast hK
  have hall : ∀ i, (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i) ≤
      K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i)) := fun i => by
    by_cases hi : InRCone γ (u i)
    · rw [ell_eq_of_inRCone hγ.linear hsw hi, sub_self, mul_zero, mul_assoc, ← mul_sub]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.2 (hon _ (hu i) (hun i) hi))
    · exact (hoffu i hi).le
  obtain ⟨i₀, hi₀, hi₀'⟩ : ∃ i, t i ≠ 0 ∧ ¬ InRCone γ (u i) := by
    by_contra hcon
    exact hoff (inRCone_of_sum ht hsum fun i hi => by_contra fun h' => hcon ⟨i, hi, h'⟩)
  have e1 : ψ.evalZ β = ∑ i, t i * ψ.evalZ (u i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff ψ u).1 hlψ t ht
  have e2 : (starDepth H.bar ψ w).evalZ β = ∑ i, t i * (starDepth H.bar ψ w).evalZ (u i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff _ u).1 hlp t ht
  have key : ∑ i, t i * ((N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i)) <
      ∑ i, t i * (K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i))) :=
    Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hall i) (ht i))
      ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hoffu i₀ hi₀') (lt_of_le_of_ne (ht i₀) hi₀.symm)⟩
  rw [e1, e2, lin_eq_sum hsum h, lin_eq_sum hsum ℓ]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  convert key using 2 with i _ i _ <;> ring

end GlobalTheory.PolFan.StarKey.OffCell
