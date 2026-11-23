import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumMulEqOfSumToRealEq

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.FaceStrict

theorem exists_retract_balForms : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X], ∃ ρ : LinearMap.BilinForm ℤ X →ₗ[ℤ] balForms bar X, ∀ β : balForms bar X, ρ β = β := by
  intro O _ _ bar X _ _ _
  classical
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ X
  let P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ (Fin n → ℤ) :=
    { toFun := fun β => β.compl₁₂ π π, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hP : Function.Injective P := fun β β' h => by
    ext a b
    obtain ⟨a, rfl⟩ := hπ a
    obtain ⟨b, rfl⟩ := hπ b
    exact LinearMap.congr_fun₂ h a b
  haveI : Module.Finite ℤ (LinearMap.BilinForm ℤ X) := Module.Finite.of_injective P hP
  haveI : NoZeroSMulDivisors ℤ (LinearMap.BilinForm ℤ X ⧸ balForms bar X) := by
    refine ⟨fun {k x} hkx => ?_⟩
    obtain ⟨β, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hkx
    by_cases hk : k = 0
    · exact Or.inl hk
    right
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨h1, h2⟩ := hkx
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · have := h1 y z
      simp only [LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ hk this
    · have := h2 a y z
      simp only [LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ hk this
  haveI : Module.Free ℤ (LinearMap.BilinForm ℤ X ⧸ balForms bar X) := Module.free_of_finite_type_torsion_free'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (balForms bar X).mkQ LinearMap.id (Submodule.mkQ_surjective _)
  have hmem : ∀ x, (LinearMap.id - σ ∘ₗ (balForms bar X).mkQ :
      LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X) x ∈ balForms bar X := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hσ ((balForms bar X).mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.Quotient.mk_sub]
    rw [← Submodule.mkQ_apply (balForms bar X) (σ _), this]
    exact sub_self _
  refine ⟨(LinearMap.id - σ ∘ₗ (balForms bar X).mkQ).codRestrict (balForms bar X) hmem, fun β => ?_⟩
  · apply Subtype.ext
    simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 β.2, map_zero, sub_zero]

theorem exists_decomp_bounded : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar φ X →
    ∃ b : ℝ, ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X) (c : Fin n → ℝ),
      (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ (∀ i, φ.evalZ (u i) ≤ b) ∧ (∀ i, 0 ≤ c i) ∧
      toReal β = ∑ i, c i • toReal (u i) ∧ φ.evalZ β = ∑ i, c i * φ.evalZ (u i) := by
  intro O _ _ _ _ bar φ X _ _ _ hP
  classical
  obtain ⟨S, hS, hcov⟩ := hP.finite
  refine ⟨∑ x ∈ hS.toFinset, |φ.evalZ x|, fun β hβ hp => ?_⟩
  have hR : toReal β ∈ psdCone bar X := by
    simpa using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; simpa using hβ)
      (fun i y => by fin_cases i; simpa using hp y) (fun i => by fin_cases i; simp)
  obtain ⟨e, n, γ', c, hcell, hS', hc, he⟩ := hcov _ hR
  refine ⟨n, fun i => pull e.symm.toLinearMap (γ' i), c, fun i => pull_mem _ (hcell.mem i),
    fun i y => hcell.nonneg i _, fun i => ?_, hc, ?_, ?_⟩
  · rw [evalZ_pull φ e.symm.surjective]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |φ.evalZ x|) (fun x _ => abs_nonneg _)
      (hS.mem_toFinset.2 (hS' i)))
  · ext a b
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [LinearMap.sum_apply] using this
  · rw [← evalR_toReal, ← evalR_pullR φ (r := e.toLinearMap) e.surjective, he,
      (linearOn_iff φ γ').1 hcell.linear c hc]
    simp [evalZ_pull φ e.symm.surjective]

theorem isStrict_face_of_isCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar φ X → Dominates bar X →
    ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m), IsCone bar φ γ →
    IsStrict bar φ fun i => γ (s i) := by
  intro O _ _ _ _ bar φ X _ _ _ hP hD m m' γ s hγ
  classical
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨ρ, hρ⟩ := exists_retract_balForms O bar X
  obtain ⟨ψ, hψ⟩ := hγ.basis.exists_dual
  set T : Finset (Fin m) := Finset.univ.filter fun i => i ∉ Set.range s with hT
  set h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (∑ i ∈ T, ψ i) ∘ₗ ρ with hh
  have hγh : ∀ i, h (γ i) = if i ∈ T then 1 else 0 := fun i => by
    have e : ρ (γ i) = ⟨γ i, hγ.mem i⟩ := hρ ⟨γ i, hγ.mem i⟩
    simp only [hh, LinearMap.comp_apply, e, LinearMap.sum_apply, hψ]
    simp
  have hpos : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have e3 : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos e3 e2) e1
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hD ℓ (-h) hpos
  obtain ⟨b, hb⟩ := exists_decomp_bounded O bar φ X hP
  set B : ℕ := ⌈b⌉₊ with hB
  set K : ℕ := C + C * N * B + 1 with hK
  have cell : ∀ u ∈ balForms bar X, (∀ y, 0 ≤ u y y) → φ.evalZ u ≤ b →
      0 ≤ (K : ℝ) * ((ℓ u : ℝ) - N * φ.evalZ u) + h u ∧
      ((K : ℝ) * ((ℓ u : ℝ) - N * φ.evalZ u) + h u = 0 → (ℓ u : ℝ) = N * φ.evalZ u ∧ h u = 0) := by
    intro u hu hp hub
    obtain ⟨n, hn⟩ := hP.integral u hu hp
    have hle : (N : ℝ) * φ.evalZ u ≤ ℓ u := h2 u hu hp
    rw [hn] at hle hub ⊢
    have hle' : (N : ℤ) * n ≤ ℓ u := by exact_mod_cast hle
    have hnB : n ≤ (B : ℤ) := by
      have : (n : ℝ) ≤ B := hub.trans (Nat.le_ceil b)
      exact_mod_cast this
    have hCu := hC u hu hp
    rw [LinearMap.neg_apply] at hCu
    rcases (sub_nonneg.2 hle').eq_or_lt with ha | ha
    · have heq : (ℓ u : ℤ) = N * n := by linarith
      obtain ⟨k, c, hk, hc⟩ := h3 u hu hp (by rw [hn]; exact_mod_cast heq.symm)
      have hhu : 0 ≤ h u := by
        have e := congrArg h hc
        simp only [map_nsmul, map_sum, hγh] at e
        have hs : 0 ≤ ∑ i, c i • (if i ∈ T then (1 : ℤ) else 0) :=
          Finset.sum_nonneg fun i _ => by split_ifs <;> simp
        rw [← e, nsmul_eq_mul] at hs
        by_contra hneg
        push_neg at hneg
        have : (k : ℤ) * h u < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hk) hneg
        linarith
      have e1 : (ℓ u : ℝ) = N * n := by exact_mod_cast heq
      have e2 : (0 : ℝ) ≤ h u := by exact_mod_cast hhu
      refine ⟨by rw [e1]; linarith, fun h0 => ⟨e1, ?_⟩⟩
      rw [e1] at h0
      have : ((h u : ℤ) : ℝ) = 0 := by linarith
      exact_mod_cast this
    · have key : (1 : ℤ) ≤ K * (ℓ u - N * n) + h u := by
        have hK' : (K : ℤ) = C + C * N * B + 1 := by simp [hK]
        rw [hK']
        have a1 : (0 : ℤ) ≤ (C * N * B + 1) * (ℓ u - N * n - 1) := mul_nonneg (by positivity) (by linarith)
        have a2 : (0 : ℤ) ≤ C * N * (B - n) := mul_nonneg (by positivity) (by linarith)
        nlinarith
      have : (1 : ℝ) ≤ K * ((ℓ u : ℝ) - N * n) + h u := by exact_mod_cast key
      exact ⟨by linarith, fun h0 => by linarith⟩
  have dec : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      0 ≤ (K : ℝ) * ((ℓ β : ℝ) - N * φ.evalZ β) + h β ∧
      ((K : ℝ) * ((ℓ β : ℝ) - N * φ.evalZ β) + h β = 0 → (ℓ β : ℝ) = N * φ.evalZ β ∧ h β = 0) := by
    intro β hβ hp
    obtain ⟨n, u, c, hu, hup, hub, hc, hR, hφ⟩ := hb β hβ hp
    have lin : ∀ g : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (g β : ℝ) = ∑ i, c i * g (u i) := fun g => by
      have := sum_mul_eq_of_sum_toReal_eq (j := LinearMap.id) Function.injective_id g (u := u) (w := ![β]) (a := c)
        (b := ![1]) (by simpa using hR.symm)
      simpa using this.symm
    have hF : (K : ℝ) * ((ℓ β : ℝ) - N * φ.evalZ β) + h β =
        ∑ i, c i * ((K : ℝ) * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) + h (u i)) := by
      have e : ∀ i, c i * ((K : ℝ) * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) + h (u i)) =
          K * (c i * ℓ (u i)) - K * N * (c i * φ.evalZ (u i)) + c i * h (u i) := fun i => by ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← lin, ← hφ]
      ring
    have hF0 : ∀ i, 0 ≤ c i * ((K : ℝ) * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) + h (u i)) := fun i =>
      mul_nonneg (hc i) (cell (u i) (hu i) (hup i) (hub i)).1
    refine ⟨hF ▸ Finset.sum_nonneg fun i _ => hF0 i, fun h0 => ?_⟩
    rw [hF] at h0
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hF0 i).1 h0
    have hz' : ∀ i, c i * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) = 0 ∧ c i * (h (u i) : ℝ) = 0 := fun i => by
      rcases mul_eq_zero.1 (hz i (Finset.mem_univ _)) with h5 | h5
      · simp [h5]
      · obtain ⟨e1, e2⟩ := (cell (u i) (hu i) (hup i) (hub i)).2 h5
        simp [e1, e2]
    have e1 : (ℓ β : ℝ) - N * φ.evalZ β = ∑ i, c i * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) := by
      rw [lin ℓ, hφ, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 := lin h
    rw [Finset.sum_eq_zero fun i _ => (hz' i).1] at e1
    rw [Finset.sum_eq_zero fun i _ => (hz' i).2] at e2
    exact ⟨by linarith, by exact_mod_cast e2⟩
  refine ⟨K * N, K • ℓ + h, Nat.mul_pos (by omega) hN, fun j => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · have hs : s j ∉ T := by simp [hT]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hγh, if_neg hs, nsmul_eq_mul, add_zero]
    push_cast
    rw [h1]
    ring
  · have := (dec β hβ hp).1
    simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    push_cast
    linarith
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at he
    push_cast at he
    obtain ⟨e1, e2⟩ := (dec β hβ hp).2 (by linarith)
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp e1.symm
    have hzT : ∀ i ∈ T, c i = 0 := by
      have e := congrArg h hc
      simp only [map_nsmul, map_sum, hγh, e2, smul_zero] at e
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => by split_ifs <;> simp).1 e.symm
      intro i hi
      have := hz i (Finset.mem_univ _)
      rw [if_pos hi, nsmul_eq_mul, mul_one] at this
      exact_mod_cast this
    refine ⟨k, fun j => c (s j), hk, ?_⟩
    rw [hc]
    have e3 : ∑ i, c i • γ i = ∑ i ∈ Finset.univ.map s, c i • γ i :=
      (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        rw [hzT i (by simpa [hT, Finset.mem_map] using hi), zero_smul]).symm
    rw [e3, Finset.sum_map]

end GlobalTheory.PolFan.FaceStrict
