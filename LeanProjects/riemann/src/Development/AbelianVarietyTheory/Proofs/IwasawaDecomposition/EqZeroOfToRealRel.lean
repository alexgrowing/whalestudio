import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

section ConeFacts

variable {X : Type} [AddCommGroup X]

theorem apply_eq_of_toReal_eq {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {c : Fin m → ℝ}
    {β : LinearMap.BilinForm ℤ X} (h : toReal β = ∑ i, c i • toReal (γ i)) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by
  have h0 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.id_apply, neg_one_smul, ← h, neg_add_cancel]
  have key := sum_mul_eq_zero_of_sum_toReal (fun _ _ hab => hab) ℓ h0
  rw [Fin.sum_univ_succ] at key
  simp only [Fin.cons_zero, Fin.cons_succ] at key
  linarith

theorem InRCone.apply_nonneg {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X}
    (h : InRCone γ β) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hℓ : ∀ i, 0 ≤ ℓ (γ i)) : 0 ≤ ℓ β := by
  obtain ⟨c, hc, hβ⟩ := h
  have e := apply_eq_of_toReal_eq hβ ℓ
  have hr : (0 : ℝ) ≤ ℓ β := by
    rw [e]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hℓ i)
  exact_mod_cast hr

theorem inRCone_trans {m n : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {δ : Fin n → LinearMap.BilinForm ℤ X}
    (hδ : ∀ j, InRCone γ (δ j)) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone δ β) : InRCone γ β := by
  choose a ha hδe using hδ
  obtain ⟨b, hb, hβe⟩ := hβ
  refine ⟨fun i => ∑ j, b j * a j i, fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hb j) (ha j i), ?_⟩
  rw [hβe]
  simp only [hδe, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem eq_zero_of_toReal_rel {a b : ℕ} {u : Fin a → LinearMap.BilinForm ℤ X} {v : Fin b → LinearMap.BilinForm ℤ X}
    (hind : ∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0)
    {r : Fin a → ℝ} {s : Fin b → ℝ} (h : ∑ j, r j • toReal (u j) = ∑ k, s k • toReal (v k)) : r = 0 := by

  have hpt : ∀ x y : X, ∑ j, r j * (u j x y : ℝ) = ∑ k, s k * (v k x y : ℝ) := by
    intro x y
    have hxy := congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B x y) h
    simpa [LinearMap.sum_apply, toReal_apply] using hxy

  suffices hf : ∀ (f : Module.Dual ℚ ℝ) (j : Fin a), f (r j) = 0 by
    funext j
    exact (Module.forall_dual_apply_eq_zero_iff ℚ (r j)).mp fun f => hf f j
  intro f
  have e : ∀ (t : ℝ) (n : ℤ), f (t * n) = n * f t := by
    intro t n
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  have hq : ∀ x y : X, ∑ j, ((u j x y : ℤ) : ℚ) * f (r j) = ∑ k, ((v k x y : ℤ) : ℚ) * f (s k) := by
    intro x y
    have hxy := congrArg f (hpt x y)
    rw [map_sum, map_sum] at hxy
    simpa only [e] using hxy

  let N : ℕ := (∏ j, (f (r j)).den) * ∏ k, (f (s k)).den
  have hN : (N : ℚ) ≠ 0 := by
    have : N ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => (f (r j)).den_nz)
      (Finset.prod_ne_zero_iff.mpr fun k _ => (f (s k)).den_nz)
    exact_mod_cast this
  have key : ∀ q : ℚ, q.den ∣ N → ((((N / q.den : ℕ) : ℤ) * q.num : ℤ) : ℚ) = N * q := by
    intro q hq'
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hq' hd]
    rw [div_mul_eq_mul_div, mul_div_assoc, Rat.num_div_den]
  have hdr : ∀ j, (f (r j)).den ∣ N := fun j =>
    dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _
  have hds : ∀ k, (f (s k)).den ∣ N := fun k =>
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) _
  let c : Fin a → ℤ := fun j => ((N / (f (r j)).den : ℕ) : ℤ) * (f (r j)).num
  let d : Fin b → ℤ := fun k => ((N / (f (s k)).den : ℕ) : ℤ) * (f (s k)).num
  have hc : ∀ j, (c j : ℚ) = N * f (r j) := fun j => key _ (hdr j)
  have hd : ∀ k, (d k : ℚ) = N * f (s k) := fun k => key _ (hds k)
  have hrel : ∑ j, c j • u j = ∑ k, d k • v k := by
    ext x y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Int.cast_injective (α := ℚ)
    push_cast
    simp only [hc, hd]
    have := hq x y
    calc ∑ j, (N : ℚ) * f (r j) * (u j x y : ℚ) = N * ∑ j, ((u j x y : ℤ) : ℚ) * f (r j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = N * ∑ k, ((v k x y : ℤ) : ℚ) * f (s k) := by rw [this]
      _ = ∑ k, (N : ℚ) * f (s k) * (v k x y : ℚ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have h0 := hind d c hrel
  intro j
  have hcj : (c j : ℚ) = 0 := by rw [h0]; simp
  rw [hc j] at hcj
  have : (f (r j) : ℚ) = 0 := (mul_eq_zero.mp hcj).resolve_left hN
  exact_mod_cast this

end ConeFacts

section CellFacts

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem IsCell.reindex {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (h : IsCell bar φ γ) (e : Fin m' ≃ Fin m) :
    IsCell bar φ fun i => γ (e i) := by
  obtain ⟨hmem, hnn, hlin, hstr⟩ := h
  refine ⟨fun i => hmem (e i), fun i y => hnn (e i) y, ?_, ?_⟩
  · intro c hc
    convert hlin (fun i => c (e.symm i)) (fun i => hc _) using 1
    · congr 1
      funext x y
      exact Fintype.sum_equiv e _ _ (fun i => by simp)
    · exact Fintype.sum_equiv e _ _ (fun i => by simp)
  · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hstr
    refine ⟨N, ℓ, hN, fun i => h1 (e i), h2, ?_⟩
    intro β hβ hβn heq
    obtain ⟨k, c, hk, hkc⟩ := h3 β hβ hβn heq
    refine ⟨k, fun i => c (e i), hk, ?_⟩
    rw [hkc]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

end CellFacts

example : InRCone (fun i : Fin 2 => (![mulForm, mulForm] : Fin 2 → LinearMap.BilinForm ℤ ℤ) (Equiv.swap 0 1 i))
    ((2 : ℤ) • mulForm) :=
  inRCone_trans (δ := ![mulForm]) (fun j => by
    fin_cases j
    exact ⟨![1, 0], fun i => by fin_cases i <;> norm_num, LinearMap.ext₂ fun a b => by simp [Fin.sum_univ_two]⟩)
    ⟨![2], fun i => by fin_cases i; norm_num, LinearMap.ext₂ fun a b => by simp⟩

end GlobalTheory.PolFan
