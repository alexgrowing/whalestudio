import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.FaceCutCell

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {ψ : InvFun (𝓞 E)}
  {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]

omit [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] in

theorem apply_eq_sum_of_toReal {m : ℕ} {β : LinearMap.BilinForm ℤ X} {u : Fin m → LinearMap.BilinForm ℤ X}
    {c : Fin m → ℝ} (hβ : toReal β = ∑ i, c i • toReal (u i)) (F : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (F β : ℝ) = ∑ i, c i * (F (u i) : ℝ) := by
  have h := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) Function.injective_id F
    (β := Fin.cons β u) (c := Fin.cons (-1) c) (by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.id_apply, neg_smul, one_smul, hβ, neg_add_cancel])
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.cons_zero, Fin.cons_succ] at h
  linarith

theorem est_at {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hstr : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i)
    (hle : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β ≤ ℓ β)
    (hγ : ∀ j, 0 ≤ h (γ j)) {C : ℕ} (hC : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β)
    {u : LinearMap.BilinForm ℤ X} (hu : u ∈ balForms H.bar X) (hp : ∀ y, 0 ≤ u y y) (n : ℤ) (hn : ψ.evalZ u = n)
    {B0 L : ℝ} (hb : N * ψ.evalZ u ≤ B0) (hB0 : 0 ≤ B0) (hL : C * (B0 + 1) + C ≤ L) :
    L * (N * ψ.evalZ u) ≤ L * ℓ u + h u := by
  by_cases he : (N : ℝ) * ψ.evalZ u = ℓ u
  · obtain ⟨k, c, hk, hc⟩ := hstr u hu hp he
    have e3 : h (k • u) = ∑ i, (c i : ℤ) * h (γ i) := by
      rw [hc, map_sum]; simp only [map_nsmul, nsmul_eq_mul]
    have h2 : 0 ≤ ∑ i, (c i : ℤ) * h (γ i) := Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hγ i)
    rw [← e3, map_nsmul, nsmul_eq_mul] at h2
    have h3 : 0 ≤ h u := by
      by_contra hneg
      push_neg at hneg
      have : (k : ℤ) * h u < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hk) hneg
      linarith
    have h4 : (0 : ℝ) ≤ h u := by exact_mod_cast h3
    rw [he]
    linarith
  · have hlt : (N : ℝ) * ψ.evalZ u < ℓ u := lt_of_le_of_ne (hle u hu hp) he
    rw [hn] at hlt hb ⊢
    have h1 : (N : ℤ) * n < ℓ u := by exact_mod_cast hlt
    have h2 : ((N : ℤ) * n + 1 : ℤ) ≤ ℓ u := h1
    have h3 : (N : ℝ) * n + 1 ≤ ℓ u := by exact_mod_cast h2
    have h5 := hC u hu hp
    have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    have hLC : (0 : ℝ) ≤ L - C := by nlinarith [mul_nonneg hC0 hB0]
    nlinarith [mul_nonneg hLC (show (0 : ℝ) ≤ ℓ u - N * n - 1 by linarith),
      mul_nonneg hC0 (show (0 : ℝ) ≤ B0 - N * n by linarith), mul_nonneg hC0 hB0]

theorem isCell_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X], IsPolyFanOn H.bar ψ X → Dominates H.bar X →
    ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i)) := by
  intro E _ _ _ H ψ X _ _ _ hP hD m m' γ s h hγ hf
  refine ⟨fun i => hγ.mem _, fun i y => hγ.nonneg _ y, linearOn_comp hγ.linear s, ?_⟩
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have hpos : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have e3 : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos (by exact_mod_cast hN) e2) e1
    exact_mod_cast e3
  obtain ⟨C, hC⟩ := hD ℓ (-h) hpos
  have hC' : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β := fun β hβ hp => by
    have e1 := hC β hβ hp
    simp only [LinearMap.neg_apply] at e1
    exact_mod_cast e1
  obtain ⟨S, hS, hcov⟩ := hP.finite
  obtain ⟨B1, hB1⟩ := (hS.image fun τ => (N : ℝ) * ψ.evalZ τ).bddAbove
  set B0 := max B1 0 with hB0def
  have hB0nn : (0 : ℝ) ≤ B0 := le_max_right _ _
  have hB0 : ∀ τ ∈ S, (N : ℝ) * ψ.evalZ τ ≤ B0 := fun τ hτ => (hB1 ⟨τ, hτ, rfl⟩).trans (le_max_left _ _)
  have est : ∀ L : ℝ, C * (B0 + 1) + C ≤ L → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) →
      L * (N * ψ.evalZ β) ≤ L * ℓ β + h β := by
    intro L hL β hβ hp
    have hmem : toReal β ∈ psdCone H.bar X := by
      have e1 := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1]
        (fun i => by fin_cases i; simpa using hβ) (fun i y => by fin_cases i; simpa using hp y)
        (fun i => by fin_cases i; simp)
      simpa using e1
    obtain ⟨e, k, τ, c, hτ, hτS, hc, hdec⟩ := hcov _ hmem
    let u : Fin k → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (τ i)
    have hu : IsCell H.bar ψ u := isCell_pull_equiv hτ e.symm
    have hβu : toReal β = ∑ i, c i • toReal (u i) := LinearMap.ext₂ fun a b => by
      have e1 := LinearMap.congr_fun₂ hdec (e.symm a) (e.symm b)
      simpa [u, LinearMap.sum_apply] using e1
    have hψ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (u i) := by
      rw [← evalR_toReal, hβu]
      exact (linearOn_iff ψ u).1 hu.linear c hc
    have hℓ := apply_eq_sum_of_toReal hβu ℓ
    have hh := apply_eq_sum_of_toReal hβu h
    have hterm : ∀ i, L * (N * ψ.evalZ (u i)) ≤ L * ℓ (u i) + h (u i) := fun i => by
      obtain ⟨n, hn⟩ := hP.integral _ (hu.mem i) (hu.nonneg i)
      refine est_at h3 h2 hf.1 hC' (hu.mem i) (hu.nonneg i) n hn ?_ hB0nn hL
      rw [show ψ.evalZ (u i) = ψ.evalZ (τ i) from evalZ_pull ψ e.symm.surjective _]
      exact hB0 _ (hτS i)
    rw [hψ, hℓ, hh]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have e1 := mul_le_mul_of_nonneg_left (hterm i) (hc i)
    convert e1 using 1 <;> ring
  obtain ⟨K, hK⟩ := exists_nat_ge (C * (B0 + 1) + C + 1 : ℝ)
  have hK1 : C * (B0 + 1) + C ≤ (K : ℝ) - 1 := by linarith
  have hK0 : C * (B0 + 1) + C ≤ (K : ℝ) := by linarith
  have hCB : (0 : ℝ) ≤ C * (B0 + 1) + C :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Nat.cast_nonneg _)
  have hKpos : 0 < K := by exact_mod_cast (show (0 : ℝ) < K by linarith)
  refine ⟨K * N, (K : ℤ) • ℓ + h, Nat.mul_pos hKpos hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · have h0 : h (γ (s i)) = 0 := (hf.2 _).2 ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, h0, add_zero, smul_eq_mul]
    push_cast
    rw [h1]
    ring
  · have e1 := est K hK0 β hβ hp
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    linarith
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at he
    push_cast at he
    have e1 := est (K - 1) hK1 β hβ hp
    have e2 := h2 β hβ hp
    have heq : (N : ℝ) * ψ.evalZ β = ℓ β := by nlinarith
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp heq
    have hh0 : h β = 0 := by
      have e4 : (h β : ℝ) = 0 := by nlinarith
      exact_mod_cast e4
    have e3 : h (k • β) = ∑ i, (c i : ℤ) * h (γ i) := by
      rw [hc, map_sum]; simp only [map_nsmul, nsmul_eq_mul]
    have hsum : ∑ i, (c i : ℤ) * h (γ i) = 0 := by
      rw [← e3, map_nsmul, hh0, smul_zero]
    have hz : ∀ j, (c j : ℤ) * h (γ j) = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hf.1 i)).1 hsum j
        (Finset.mem_univ _)
    refine ⟨k, fun i => c (s i), hk, hc.trans ?_⟩
    refine (Fintype.sum_of_injective s s.injective _ _ (fun j hj => ?_) fun i => rfl).symm
    have hne : h (γ j) ≠ 0 := fun h0 => hj ((hf.2 j).1 h0)
    have hcj : c j = 0 := by
      rcases mul_eq_zero.1 (hz j) with h' | h'
      · exact_mod_cast h'
      · exact absurd h' hne
    simp [hcj]

example : IsCell id (InvFun.minVal ℤ) ![mulForm] := isCone_mulForm.isCell

end GlobalTheory.PolFan.FaceCutCell
