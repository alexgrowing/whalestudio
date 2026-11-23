import Mathlib

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def isoPart (π : K →* (H →L[ℂ] H)) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) :
    Submodule ℂ H :=
  ⨆ (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = π k (T w)), LinearMap.range T

theorem range_le_isoPart (π : K →* (H →L[ℂ] H)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) {T : W →ₗ[ℂ] H} (hT : ∀ k w, T (ρ k w) = π k (T w)) :
    LinearMap.range T ≤ isoPart π ρ := by
  unfold isoPart
  exact le_iSup₂_of_le (f := fun (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = π k (T w)) => LinearMap.range T)
    T hT le_rfl

theorem starProjection_comm {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖) (R : Submodule ℂ H)
    [FiniteDimensional ℂ R] (hR : ∀ k, ∀ w ∈ R, π k w ∈ R) (k : K) (x : H) :
    R.starProjection (π k x) = π k (R.starProjection x) := by
  have hinner : ∀ u v, ⟪π k u, π k v⟫_ℂ = ⟪u, v⟫_ℂ := fun u v =>
    (⟨(π k : H →ₗ[ℂ] H), hπ k⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v
  have hsurj : ∀ w ∈ R, ∃ w' ∈ R, π k w' = w := by
    intro w hw
    refine ⟨π k⁻¹ w, hR _ w hw, ?_⟩
    change (π k * π k⁻¹) w = w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hR k _ (R.starProjection_apply_mem x))
  intro w hw
  obtain ⟨w', hw', rfl⟩ := hsurj w hw
  rw [← map_sub, hinner]
  exact (Submodule.mem_orthogonal' _ _).1 (R.sub_starProjection_mem_orthogonal x) w' hw'

variable [CompleteSpace H]

theorem isoPart_le_sup {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖) {W : Type} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W) (W' : Submodule ℂ W)
    (hW : ∀ k, W' ≤ W'.comap (ρ k)) :
    isoPart π ρ ≤ isoPart π (ρ.subrepresentation W' hW) ⊔ isoPart π (ρ.quotient W' hW) := by
  refine iSup₂_le fun T hT => ?_
  let R : Submodule ℂ H := W'.map T
  have hRinv : ∀ k, ∀ w ∈ R, π k w ∈ R := by
    rintro k _ ⟨v, hv, rfl⟩
    exact ⟨ρ k v, hW k hv, hT k v⟩
  have hP : ∀ k x, R.starProjection (π k x) = π k (R.starProjection x) :=
    starProjection_comm hπ R hRinv
  have h1 : LinearMap.range (T ∘ₗ W'.subtype) ≤ isoPart π (ρ.subrepresentation W' hW) :=
    range_le_isoPart π _ (fun k w => by simp [hT])
  have hRle : R ≤ LinearMap.range (T ∘ₗ W'.subtype) := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  have hker : W' ≤ LinearMap.ker ((LinearMap.id - (R.starProjection : H →ₗ[ℂ] H)) ∘ₗ T) := by
    intro v hv
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      ContinuousLinearMap.coe_coe]
    rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]
    exact ⟨v, hv, rfl⟩
  let Q := W'.liftQ ((LinearMap.id - (R.starProjection : H →ₗ[ℂ] H)) ∘ₗ T) hker
  have hQmk : ∀ v, Q (Submodule.Quotient.mk v) = T v - R.starProjection (T v) := by
    intro v
    simp [Q]
  have hQ : ∀ k w, Q (ρ.quotient W' hW k w) = π k (Q w) := by
    intro k w
    induction w using Submodule.Quotient.induction_on with
    | H v =>
      rw [Representation.quotient_apply, Submodule.mapQ_apply, hQmk, hQmk, hT, hP, map_sub]
  have h2 := range_le_isoPart π (ρ.quotient W' hW) hQ
  rintro _ ⟨v, rfl⟩
  rw [show T v = R.starProjection (T v) + (T v - R.starProjection (T v)) by abel]
  exact Submodule.add_mem_sup (h1 (hRle (R.starProjection_apply_mem (T v))))
    (h2 ⟨Submodule.Quotient.mk v, hQmk v⟩)

theorem finiteDimensional_isoPart_of_simple {π : K →* (H →L[ℂ] H)}
    (hadm : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → (∀ k, ∀ w ∈ S, π k w ∈ S) →
      (∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', π k w ∈ S') → S' = ⊥ ∨ S' = S) →
      FiniteDimensional ℂ (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
        ∀ k, ∀ w ∈ S, T (π k w) = π k (T w)} : Submodule ℂ H))
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W)
    (hs : ∀ W' : Submodule ℂ W, (∀ k, W' ≤ W'.comap (ρ k)) → W' = ⊥ ∨ W' = ⊤) :
    FiniteDimensional ℂ (isoPart π ρ) := by
  classical
  by_cases h0 : ∀ T : W →ₗ[ℂ] H, (∀ k w, T (ρ k w) = π k (T w)) → T = 0
  · have hbot : isoPart π ρ = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun T hT => ?_)
      rw [h0 T hT, LinearMap.range_zero]
    rw [hbot]
    infer_instance
  push Not at h0
  obtain ⟨T₀, hT₀, hne⟩ := h0
  have hinj : Function.Injective T₀ := by
    rw [← LinearMap.ker_eq_bot]
    rcases hs (LinearMap.ker T₀) (fun k v hv => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hv ⊢
      rw [hT₀, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hne
  let S : Submodule ℂ H := LinearMap.range T₀
  have hSinv : ∀ k, ∀ w ∈ S, π k w ∈ S := by
    rintro k _ ⟨v, rfl⟩
    exact ⟨ρ k v, hT₀ k v⟩
  have hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', π k w ∈ S') → S' = ⊥ ∨ S' = S := by
    intro S' hle hinv
    rcases hs (S'.comap T₀) (fun k v hv => by
      simp only [Submodule.mem_comap] at hv ⊢
      rw [hT₀]
      exact hinv k _ hv) with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨v, rfl⟩ := hle hw
      have hv : v ∈ S'.comap T₀ := hw
      rw [h, Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ S'.comap T₀ := by rw [h]; trivial
      exact hv
  have hfin := hadm S inferInstance hSinv hSirr
  let e : W ≃ₗ[ℂ] S := LinearEquiv.ofInjective T₀ hinj
  refine Submodule.finiteDimensional_of_le
    (S₂ := sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k, ∀ w ∈ S, T (π k w) = π k (T w)})
    (iSup₂_le fun T hT => ?_)
  let T' : H →ₗ[ℂ] H := T ∘ₗ (e.symm : S →ₗ[ℂ] W) ∘ₗ (S.orthogonalProjectionOnto : H →ₗ[ℂ] S)
  have hT' : ∀ v, T' (T₀ v) = T v := by
    intro v
    have he : ((e v : S) : H) = T₀ v := LinearEquiv.ofInjective_apply _ v
    simp only [T', LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [← he, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  refine le_sSup ⟨T', ?_, ?_⟩
  · have hc : T' ∘ₗ T₀ = T := LinearMap.ext hT'
    rw [← hc, LinearMap.range_comp]
  · rintro k _ ⟨v, rfl⟩
    rw [← hT₀, hT', hT', hT]

theorem finiteDimensional_isoPart {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖)
    (hadm : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → (∀ k, ∀ w ∈ S, π k w ∈ S) →
      (∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', π k w ∈ S') → S' = ⊥ ∨ S' = S) →
      FiniteDimensional ℂ (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
        ∀ k, ∀ w ∈ S, T (π k w) = π k (T w)} : Submodule ℂ H))
    (d : ℕ) : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W),
      Module.finrank ℂ W = d → FiniteDimensional ℂ (isoPart π ρ) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W _ _ _ ρ hd
  by_cases hs : ∀ W' : Submodule ℂ W, (∀ k, W' ≤ W'.comap (ρ k)) → W' = ⊥ ∨ W' = ⊤
  · exact finiteDimensional_isoPart_of_simple hadm ρ hs
  push Not at hs
  obtain ⟨W', hW, hbot, htop⟩ := hs
  have h1 : Module.finrank ℂ W' < d := hd ▸ Submodule.finrank_lt htop
  have h2 : Module.finrank ℂ (W ⧸ W') < d := by
    have hsum := Submodule.finrank_quotient_add_finrank W'
    have hpos : 0 < Module.finrank ℂ W' :=
      Nat.pos_of_ne_zero fun h => hbot (Submodule.finrank_eq_zero.1 h)
    omega
  have := ih _ h1 W' (ρ.subrepresentation W' hW) rfl
  have := ih _ h2 (W ⧸ W') (ρ.quotient W' hW) rfl
  exact Submodule.finiteDimensional_of_le (isoPart_le_sup hπ ρ W' hW)

end GlobalTheory.CompanionTheory.AdmGL

end
