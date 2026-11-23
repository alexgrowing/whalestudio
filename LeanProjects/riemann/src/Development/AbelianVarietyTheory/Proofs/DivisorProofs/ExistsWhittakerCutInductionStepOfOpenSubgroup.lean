import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqvCorMulCol

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

theorem exists_mul_lr {F : Type} [NormedField F] [ProperSpace F] {ψ : AddChar F ℂ} (hψ : IsLocallyConstant ψ)
    (hψ1 : ψ ≠ 1) {m : ℕ} {L : Set (Fin (m + 1) → F)} (hL : L ∈ nhds (0 : Fin (m + 1) → F))
    (T' : GL (Fin (m + 1)) F →₀ ℂ) (κ : GL (Fin (m + 1)) F → GL (Fin (m + 1)) F) (Φ : (Fin (m + 1) → F) → ℂ)
    (hΦ : IsLocallyConstant Φ) :
    ∃ M₂ : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f →
      (∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F,
      act (comp M₂ (T'.sum fun k c => Finsupp.single (cor (κ k)) c)) f (cor h) =
        Φ (lr h) * act (T'.sum fun k c => Finsupp.single (cor (κ k)) c) f (cor h) := by
  classical
  have hK := GlobalTheory.JSW.isCompact_charAnnihilator_of_mem_nhds_zero ψ hψ hψ1 L hL
  set K := {r : Fin (m + 1) → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} with hKdef
  let K' : Set (Fin (m + 1) → F) := ⋃ k ∈ T'.support, (fun r => r ᵥ* ((κ k)⁻¹).val) '' K
  have hK' : IsCompact K' := T'.support.isCompact_biUnion fun k _ =>
    hK.image (continuous_id.matrix_vecMul continuous_const)
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_finite_characterSum_eq_locallyConstant_on_compact ψ hψ hψ1 K' hK' Φ hΦ
  set T₂ : GL (Fin (m + 2)) F →₀ ℂ := T'.sum fun k c => Finsupp.single (cor (κ k)) c with hT₂def
  let M₂ : GL (Fin (m + 2)) F →₀ ℂ := M.sum fun v c => Finsupp.single (mir 1 v) c
  refine ⟨M₂, fun f hf hfL h => ?_⟩
  have hT₂ : act T₂ f (cor h) = T'.sum fun k c => c * f (cor (h * κ k)) := by
    simp only [T₂, act_finsupp_sum, act_single, map_mul]
  rw [act_comp]
  simp only [M₂, act_finsupp_sum, act_single, eqv_cor_mul_col (eqv_act hf T₂), ← mul_assoc]
  rw [← Finsupp.sum_mul]
  by_cases h0 : act T₂ f (cor h) = 0
  · rw [h0, mul_zero, mul_zero]
  · rw [hM]
    rw [hT₂] at h0
    obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    have hk1 := right_ne_zero_of_mul hk0
    refine Set.mem_iUnion₂.2 ⟨k, hk, lr (h * κ k), fun y hy => ?_, ?_⟩
    · have := hfL y hy (cor (h * κ k))
      rw [eqv_cor_mul_col hf] at this
      exact (mul_eq_right₀ hk1).1 this
    · simp only
      rw [← lr_mul, mul_inv_cancel_right]

theorem exists_cut_cor_of_sub : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ U : Subgroup (GL (Fin (m + 1)) F), IsCompact (U : Set (GL (Fin (m + 1)) F)) → IsOpen (U : Set (GL (Fin (m + 1)) F)) → ∀ z : GL (Fin (m + 1)) F, ∃ U₁ : Subgroup (GL (Fin (m + 1)) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin (m + 1)) F)) ∧ GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 1)) F))) {g | ∃ p : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1 ∧ ∃ u ∈ U₁, g = p * u}) → ∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h := by
  intro F _ _ _ ψ hψ hψ1 m H B hBc hBo L hL h₀
  classical
  let U : Subgroup (GL (Fin (m + 1)) F) := B.map (MulAut.conj h₀).toMonoidHom
  have hUe : (U : Set (GL (Fin (m + 1)) F)) = (fun b => h₀ * b * h₀⁻¹) '' B := by
    ext x; simp [U]
  have hUm : ∀ b ∈ B, h₀ * b * h₀⁻¹ ∈ U := fun b hb => ⟨b, hb, rfl⟩
  have hUB : ∀ u ∈ U, h₀⁻¹ * u * h₀ ∈ B := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [mul_assoc] using hb
  have hUc : IsCompact (U : Set (GL (Fin (m + 1)) F)) := by
    rw [hUe]; exact hBc.image (by fun_prop)
  have hUo : IsOpen (U : Set (GL (Fin (m + 1)) F)) := by
    rw [hUe]; exact ((isOpenMap_mul_right h₀⁻¹).comp (isOpenMap_mul_left h₀)) _ hBo
  obtain ⟨U₁, hU₁U, hU₁o, T', hT'⟩ := H U hUc hUo 1
  have hU₁c : IsCompact (U₁ : Set (GL (Fin (m + 1)) F)) :=
    hUc.of_isClosed_subset (U₁.isClosed_of_isOpen hU₁o) hU₁U
  have hOe := GlobalTheory.T.isClopen_rowVector_orbit_compactOpen_GL U₁ hU₁c hU₁o (lr 1) (lr_ne_zero 1)
  let R : GL (Fin (m + 1)) F → Set (Fin (m + 1) → F) := fun a =>
    (fun r => r ᵥ* ((a * h₀)⁻¹).val) ⁻¹' {r | ∃ b ∈ U₁, r = lr 1 ᵥ* (b : Matrix (Fin (m + 1)) (Fin (m + 1)) F)}
  have hR : ∀ a, IsClopen (R a) := fun a => hOe.preimage (continuous_id.matrix_vecMul continuous_const)

  have hC : ∀ a ∈ U, ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * cor b) = f g) →
      ∀ h, lr h ∈ R a → act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        (cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (cor h)) h := by
    intro a ha f hf hfB h hRa
    obtain ⟨v, hv, e⟩ := hRa
    have e' : lr (h * h₀⁻¹ * a⁻¹) = lr (1 * v) := by
      rw [show h * h₀⁻¹ * a⁻¹ = h * (a * h₀)⁻¹ by group]
      exact e
    have hmem : h * h₀⁻¹ * a⁻¹ ∈ {g | ∃ p : GL (Fin (m + 1)) F, lr p = lr 1 ∧ ∃ u ∈ U₁, g = p * u} :=
      ⟨h * h₀⁻¹ * a⁻¹ * v⁻¹, by rw [lr_mul_congr e' v⁻¹, one_mul, mul_inv_cancel], v, hv, by group⟩
    have h2 := hT' (fun g => f (cor (g * h₀)))
      (fun u hu g => by simp only [mul_assoc]; exact hf.res u hu _)
      (fun u hu g => by
        rw [show g * u * h₀ = g * h₀ * (h₀⁻¹ * u * h₀) by group, map_mul]
        exact hfB _ (hUB u hu) _)
      (h * h₀⁻¹ * a⁻¹) hmem
    have hT₂ : act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        T'.sum fun k c => c * f (cor (h * (h₀⁻¹ * a⁻¹ * k * h₀))) := by
      simp only [act_finsupp_sum, act_single, map_mul]
    have h3 : act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        act T' (fun g => f (cor (g * h₀))) (h * h₀⁻¹ * a⁻¹) := by
      rw [hT₂]
      simp only [act, mul_assoc]
    rw [h3, h2]
    have h4 : h * h₀⁻¹ * a⁻¹ ∈ cell 1 (U : Set (GL (Fin (m + 1)) F)) ↔
        h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
      constructor
      · rintro ⟨u, hu, c, hc, e⟩
        refine ⟨u, hu, h₀⁻¹ * (c * a) * h₀, hUB _ (U.mul_mem hc ha), ?_⟩
        rw [show h = h * h₀⁻¹ * a⁻¹ * (a * h₀) by group, e]
        group
      · rintro ⟨u, hu, c, hc, rfl⟩
        exact ⟨u, hu, h₀ * c * h₀⁻¹ * a⁻¹, U.mul_mem (hUm c hc) (U.inv_mem ha), by group⟩
    by_cases h5 : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
    · rw [Set.indicator_of_mem h5, Set.indicator_of_mem (h4.2 h5)]
      rw [show h * h₀⁻¹ * a⁻¹ * h₀ = h * (h₀⁻¹ * a⁻¹ * h₀) by group, map_mul]
      exact hfB _ (by simpa using hUB _ (U.inv_mem ha)) _
    · rw [Set.indicator_of_notMem h5, Set.indicator_of_notMem (fun h6 => h5 (h4.1 h6))]

  have key : ∀ A : Finset (GL (Fin (m + 1)) F), (∀ a ∈ A, a ∈ U) → ∃ S : GL (Fin (m + 2)) F →₀ ℂ,
      ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * cor b) = f g) →
      (∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F,
      act S f (cor h) = (⋃ a ∈ A, R a).indicator 1 (lr h) *
        (cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (cor h)) h := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro _; exact ⟨0, fun f _ _ _ h => by simp⟩
    | insert a A haA ih =>
      intro hA
      obtain ⟨S, hS⟩ := ih (fun b hb => hA b (Finset.mem_insert_of_mem hb))
      have ha : a ∈ U := hA a (Finset.mem_insert_self a A)
      have hcl : IsClopen (R a \ ⋃ b ∈ A, R b) := (hR a).diff (isClopen_biUnion_finset fun b _ => hR b)
      obtain ⟨M₂, hM₂⟩ := exists_mul_lr hψ hψ1 hL T' (fun k => h₀⁻¹ * a⁻¹ * k * h₀)
        ((R a \ ⋃ b ∈ A, R b).indicator 1) (LocallyConstant.charFn ℂ hcl).isLocallyConstant
      refine ⟨S + comp M₂ (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c),
        fun f hf hfB hfL h => ?_⟩
      rw [act_add, hS f hf hfB hfL h, hM₂ f hf hfL h]
      by_cases h1 : lr h ∈ ⋃ b ∈ A, R b
      · have h2 : lr h ∈ ⋃ b ∈ insert a A, R b := by
          rw [Finset.set_biUnion_insert]; exact Or.inr h1
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          Set.indicator_of_notMem (s := R a \ ⋃ b ∈ A, R b) (fun h3 => h3.2 h1)]
        simp
      · by_cases h3 : lr h ∈ R a
        · have h2 : lr h ∈ ⋃ b ∈ insert a A, R b := by
            rw [Finset.set_biUnion_insert]; exact Or.inl h3
          rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, Set.indicator_of_mem (s := R a \ ⋃ b ∈ A, R b) ⟨h3, h1⟩,
            hC a ha f hf hfB h h3]
          simp
        · have h2 : lr h ∉ ⋃ b ∈ insert a A, R b := by
            rw [Finset.set_biUnion_insert]; exact fun h4 => h4.elim h3 h1
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
            Set.indicator_of_notMem (s := R a \ ⋃ b ∈ A, R b) (fun h4 => h3 h4.1)]
          simp
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover
    (fun a : U => (fun x => x * (a : GL (Fin (m + 1)) F)⁻¹) ⁻¹' (U₁ : Set (GL (Fin (m + 1)) F)))
    (fun a => hU₁o.preimage (continuous_mul_right _))
    (fun u hu => Set.mem_iUnion.2 ⟨⟨u, hu⟩, by simp [U₁.one_mem]⟩)
  obtain ⟨S, hS⟩ := key (t.image Subtype.val) (fun a ha => by
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 ha
    exact b.2)
  refine ⟨S, fun f hf hfB hfL h => ?_⟩
  rw [hS f hf hfB hfL h]
  by_cases hh : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
  · have hmem : lr h ∈ ⋃ a ∈ t.image Subtype.val, R a := by
      obtain ⟨u, hu, c, hc, rfl⟩ := hh
      obtain ⟨i, hi, hw⟩ := Set.mem_iUnion₂.1 (ht (hUm c hc))
      refine Set.mem_iUnion₂.2 ⟨i.1, Finset.mem_image_of_mem _ hi, h₀ * c * h₀⁻¹ * (i : GL (Fin (m + 1)) F)⁻¹, hw, ?_⟩
      show lr (u * h₀ * c) ᵥ* _ = _
      rw [← lr_mul, show u * h₀ * c * ((i : GL (Fin (m + 1)) F) * h₀)⁻¹ =
        u * (h₀ * c * h₀⁻¹ * (i : GL (Fin (m + 1)) F)⁻¹) by group, lr_mul_congr (lr_of_mem hu), one_mul, ← lr_mul, one_mul]
    rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem hh, mul_zero]

end GlobalTheory.JSW.Cut
