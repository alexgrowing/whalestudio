import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem isCell_face_of_isFaceCut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ)
    (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell H.bar ψ (fun j => v (s j)) := by
  intro E _ _ _ H q ψ hψ X _ _ _ _ hX hD m v hv m' s h hcut
  have hP := hψ X hX
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hv.strict
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓpos : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos hNr e2) e1
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hD ℓ (-h) hℓpos
  obtain ⟨S, hS, hcov⟩ := hP.finite
  obtain ⟨b, hb⟩ : ∃ b : ℕ, ∀ γ ∈ S, ψ.evalZ γ ≤ b := by
    refine ⟨⌈∑ γ ∈ hS.toFinset, |ψ.evalZ γ|⌉₊, fun γ hγ => ?_⟩
    refine le_trans ?_ (Nat.le_ceil _)
    exact le_trans (le_abs_self _)
      (Finset.single_le_sum (f := fun γ => |ψ.evalZ γ|) (fun _ _ => abs_nonneg _) (hS.mem_toFinset.2 hγ))
  set K : ℕ := C * (1 + N * b) + 1 with hK
  have hKpos : 0 < K := Nat.succ_pos _

  have gen : ∀ u ∈ balForms H.bar X, (∀ y, 0 ≤ u y y) → ψ.evalZ u ≤ b →
      (0 ≤ h u ∧ (ℓ u : ℝ) = N * ψ.evalZ u) ∨
        (0 : ℝ) < K * (ℓ u : ℝ) + h u - K * N * ψ.evalZ u := by
    intro u hu hp hub
    by_cases heq : (ℓ u : ℝ) = N * ψ.evalZ u
    · left
      obtain ⟨k, c, hk, hc⟩ := h3 u hu hp heq.symm
      have e1 : (k : ℤ) * h u = ∑ i, (c i : ℤ) * h (v i) := by
        have := congrArg h hc
        simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
      have hnn : 0 ≤ (k : ℤ) * h u := e1 ▸ Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) (hcut.1 i)
      exact ⟨(mul_nonneg_iff_of_pos_left (by exact_mod_cast hk)).1 hnn, heq⟩
    · right
      obtain ⟨n, hn⟩ := hP.integral u hu hp
      have hle : (N : ℝ) * ψ.evalZ u ≤ ℓ u := h2 u hu hp
      have hlt : (N : ℝ) * ψ.evalZ u < ℓ u := lt_of_le_of_ne hle (Ne.symm heq)
      rw [hn] at hlt hub ⊢
      have hint : (N : ℤ) * n + 1 ≤ ℓ u := by
        have : (((N : ℤ) * n : ℤ) : ℝ) < ℓ u := by push_cast; exact hlt
        exact_mod_cast this
      have hint' : (N : ℝ) * n + 1 ≤ ℓ u := by exact_mod_cast hint
      have hCu : -h u ≤ C * ℓ u := by simpa using hC u hu hp
      have hCu' : -(h u : ℝ) ≤ C * ℓ u := by exact_mod_cast hCu
      have hKr : (K : ℝ) = C * (1 + N * b) + 1 := by rw [hK]; push_cast; ring
      have hCN : (0 : ℝ) ≤ C * N := by positivity
      have a1 : (K - C : ℝ) * 1 ≤ (K - C) * (ℓ u - N * n) :=
        mul_le_mul_of_nonneg_left (by linarith) (by rw [hKr]; have : (0 : ℝ) ≤ C * N * b := by positivity
                                                    nlinarith)
      have a2 : (C * N : ℝ) * n ≤ C * N * b := mul_le_mul_of_nonneg_left hub hCN
      rw [hKr] at a1 ⊢
      nlinarith

  have core : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) →
      ((K * N : ℕ) : ℝ) * ψ.evalZ β ≤ ((K • ℓ + h) β : ℤ) ∧
        (((K * N : ℕ) : ℝ) * ψ.evalZ β = ((K • ℓ + h) β : ℤ) → h β = 0) := by
    intro β hβ hp
    have hR : toReal β ∈ psdCone H.bar X := by
      simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (by simp [hβ])
        (by simp [hp]) (by simp)
    obtain ⟨e, mm, γ, c, hγ, hγS, hc, hsum⟩ := hcov (toReal β) hR
    set u : Fin mm → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hu
    have hβu : toReal β = ∑ i, c i • toReal (u i) := LinearMap.ext₂ fun a b => by
      have := LinearMap.congr_fun₂ hsum (e.symm a) (e.symm b)
      simpa [LinearMap.sum_apply, u] using this
    have hlin : ψ.LinearOn u := (linearOn_pull_iff e.symm.surjective).2 hγ.linear
    have hψβ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (u i) := by
      rw [← evalR_toReal, hβu, (linearOn_iff ψ u).1 hlin c hc]
    have hℓβ := apply_eq_of_toReal_eq hβu ℓ
    have hhβ := apply_eq_of_toReal_eq hβu h
    have hT : (((K • ℓ + h) β : ℤ) : ℝ) - ((K * N : ℕ) : ℝ) * ψ.evalZ β =
        ∑ i, c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, Int.cast_add, Int.cast_mul,
        Int.cast_natCast, Nat.cast_mul]
      rw [hℓβ, hhβ, hψβ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hg : ∀ i, (0 ≤ h (u i) ∧ (ℓ (u i) : ℝ) = N * ψ.evalZ (u i)) ∨
        (0 : ℝ) < K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i) := fun i =>
      gen (u i) (pull_mem _ (hγ.mem i)) (fun y => hγ.nonneg i _)
        (by rw [hu, evalZ_pull ψ e.symm.surjective]; exact hb _ (hγS i))
    have hterm : ∀ i, 0 ≤ c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) := fun i => by
      refine mul_nonneg (hc i) ?_
      rcases hg i with ⟨h0, he⟩ | hpos
      · rw [he]
        have : (0 : ℝ) ≤ h (u i) := by exact_mod_cast h0
        nlinarith
      · exact hpos.le
    refine ⟨?_, fun heq => ?_⟩
    · have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hterm i
      linarith
    · have h0 : ∑ i, c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) = 0 := by
        rw [← hT, heq, sub_self]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm i).1 h0
      have : (h β : ℝ) = 0 := by
        rw [hhβ]
        refine Finset.sum_eq_zero fun i hi => ?_
        rcases eq_or_ne (c i) 0 with hci | hci
        · rw [hci, zero_mul]
        · have hTi := (mul_eq_zero.1 (hz i hi)).resolve_left hci
          rcases hg i with ⟨-, he⟩ | hpos
          · rw [he] at hTi
            have : (h (u i) : ℝ) = 0 := by linarith
            rw [this, mul_zero]
          · exact absurd hTi hpos.ne'
      exact_mod_cast this
  refine ⟨fun j => hv.mem _, fun j => hv.nonneg _, linearOn_comp hv.linear s, K * N, K • ℓ + h,
    Nat.mul_pos hKpos hN, fun i => ?_, fun β hβ hp => (core β hβ hp).1, fun β hβ hp heq => ?_⟩
  · have hz : h (v (s i)) = 0 := (hcut.2 _).2 ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hz, add_zero, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul]
    rw [h1]; ring
  · have hh := (core β hβ hp).2 heq
    have hℓ : (N : ℝ) * ψ.evalZ β = ℓ β := by
      have e1 := heq
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hh, add_zero, Int.cast_mul,
        Int.cast_natCast, Nat.cast_mul] at e1
      have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
      have : (K : ℝ) * (N * ψ.evalZ β - ℓ β) = 0 := by linarith
      linarith [(mul_eq_zero.1 this).resolve_left hKr.ne']
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp hℓ
    have e1 : (k : ℤ) * h β = ∑ j, (c j : ℤ) * h (v j) := by
      have := congrArg h hc
      simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    rw [hh, mul_zero] at e1
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (Int.natCast_nonneg (c j)) (hcut.1 j)).1 e1.symm
    have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := fun j hj => by
      have hne : h (v j) ≠ 0 := fun h0 => hj ((hcut.2 j).1 h0)
      have := (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_right hne
      exact_mod_cast this
    refine ⟨k, fun i => c (s i), hk, ?_⟩
    rw [hc]
    classical
    rw [← Finset.sum_map Finset.univ s (fun j => c j • v j)]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
    rw [hc0 j fun ⟨i, hi⟩ => hj (by simp [← hi]), zero_smul]

end GlobalTheory.PolFan
