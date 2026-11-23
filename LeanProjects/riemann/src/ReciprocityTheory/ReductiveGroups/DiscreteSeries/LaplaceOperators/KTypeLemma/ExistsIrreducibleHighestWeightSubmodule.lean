import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerOrth

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem tensor_dual_action_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (g : Fin n → M) (c : Fin n) :
    tensVd E a b g c = E a b (g c) - (if c = b then g a else 0) := by
  unfold tensVd
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

section Unit

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

theorem highest_weight_dominant_of_unitary (hA : IsGlRep A) (hU : IsKUnitary ε A) {ν : Fin n → ℝ} {y : X}
    (hy : IsKHWVec ε A ν y) (hy0 : y ≠ 0) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    ν b ≤ ν a := by
  have hc := hA a b b a
  rw [if_pos rfl, if_pos rfl] at hc
  have h1 : A a b (A b a y) = ((ν a - ν b : ℝ) : ℂ) • y := by
    have := congrArg (fun T : Module.End ℂ X => T y) hc
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hy.2 a b hab he, map_zero, sub_zero] at this
    rw [this, hy.1 a, hy.1 b]; push_cast; rw [sub_smul]
  have h2 : inner ℂ (A b a y) (A b a y) = inner ℂ y (A a b (A b a y)) := hU b a he.symm y _
  rw [h1, inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ‖A b a y‖ ^ 2 = (ν a - ν b) * ‖y‖ ^ 2 := by
    have := congrArg Complex.re h2
    simpa [← Complex.ofReal_pow, Complex.mul_re] using this
  have hpos : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.2 hy0) 2
  by_contra hlt
  push Not at hlt
  have : (ν a - ν b) * ‖y‖ ^ 2 < 0 := mul_neg_of_neg_of_pos (by linarith) hpos
  nlinarith [sq_nonneg ‖A b a y‖]

theorem exists_irreducible_highest_weight_submodule (hU : IsKUnitary ε A) {ν : Fin n → ℝ} :
    ∀ (d : ℕ) (T : Submodule ℂ X), Module.finrank ℂ T = d → FiniteDimensional ℂ T →
      IsKStableSub ε A T → ∀ w ∈ T, w ≠ 0 → IsKHWVec ε A ν w →
      ∃ W : Submodule ℂ X, W ≤ T ∧ IsKIrrHW ε A ν W := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro T hd hfd hT w hwT hw0 hw
  by_cases hirr : ∀ S' : Submodule ℂ X, S' ≤ T → IsKStableSub ε A S' → S' = ⊥ ∨ S' = T
  · exact ⟨T, le_rfl, hfd, hT, hirr, w, hwT, hw0, hw⟩
  push Not at hirr
  obtain ⟨S', hS'T, hS', hS'0, hS'ne⟩ := hirr
  have hlt : S' < T := lt_of_le_of_ne hS'T hS'ne
  have hfdS : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'T
  have : CompleteSpace S' := FiniteDimensional.complete ℂ S'
  have hw1 : IsKHWVec ε A ν (S'.starProjection w) := isKHWVec_starProjection hU hS' hw
  by_cases h1 : S'.starProjection w = 0
  · set T2 : Submodule ℂ X := T ⊓ S'ᗮ
    have hT2 : IsKStableSub ε A T2 := fun a b he v hv =>
      ⟨hT a b he v hv.1, orthogonal_kStable hU hS' a b he v hv.2⟩
    have hwT2 : w ∈ T2 := by
      refine ⟨hwT, ?_⟩
      have := Submodule.sub_starProjection_mem_orthogonal (K := S') w
      rwa [h1, sub_zero] at this
    have hlt2 : T2 < T := by
      refine lt_of_le_of_ne inf_le_left (fun heq => ?_)
      obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS'0
      have hsT2 : s ∈ T2 := heq ▸ hS'T hs
      have h0 : inner ℂ s s = (0 : ℂ) := Submodule.inner_right_of_mem_orthogonal hs hsT2.2
      exact hs0 (inner_self_eq_zero.1 h0)
    have hfd2 : FiniteDimensional ℂ T2 := Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨W, hW, hWi⟩ := ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt2) T2 rfl hfd2 hT2 w hwT2 hw0 hw
    exact ⟨W, hW.trans inf_le_left, hWi⟩
  · obtain ⟨W, hW, hWi⟩ := ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) S' rfl hfdS hS'
      _ (S'.starProjection_apply_mem w) h1 hw1
    exact ⟨W, hW.trans hS'T, hWi⟩

end Unit

section Lift

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ D}

def coordinateTensorEndAction (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) : Module.End ℂ (WithLp 2 (Fin n → D)) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm.toLinearMap ∘ₗ tensVd E a b ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin n → D)).toLinearMap

theorem k3vdTA_isKUnitary (hU : IsKUnitary ε E) : IsKUnitary ε (coordinateTensorEndAction E) := by
  intro a b he x y
  have key : ∀ g h : Fin n → D, ∑ i, inner ℂ (tensVd E a b g i) (h i) =
      ∑ i, inner ℂ (g i) (tensVd E b a h i) := by
    intro g h
    simp only [tensor_dual_action_apply, inner_sub_left, inner_sub_right, sum_sub_distrib, hU a b he]
    congr 1
    rw [Finset.sum_eq_single b (fun c _ hc => by simp [hc]) (by simp),
      Finset.sum_eq_single a (fun c _ hc => by simp [hc]) (by simp)]
    simp
  simp only [coordinateTensorEndAction, LinearMap.comp_apply, LinearEquiv.coe_coe, PiLp.inner_apply,
    WithLp.linearEquiv_apply, WithLp.linearEquiv_symm_apply, WithLp.ofLp_toLp]
  exact key _ _

theorem k3vdTA_e (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (z : WithLp 2 (Fin n → D)) :
    WithLp.linearEquiv 2 ℂ (Fin n → D) (coordinateTensorEndAction E a b z) =
      tensVd E a b (WithLp.linearEquiv 2 ℂ (Fin n → D) z) := by
  simp only [coordinateTensorEndAction, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem exists_highest_weight_lift_pi (hU : IsKUnitary ε E) {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {B : Fin n → Fin n → Module.End ℂ Y} (f : (Fin n → D) →ₗ[ℂ] Y) {S : Submodule ℂ (Fin n → D)}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε (tensVd E) S)
    (hf : ∀ a b, ε a = ε b → ∀ x ∈ S, f (tensVd E a b x) = B a b (f x)) {x₀ : Fin n → D} (hx₀ : x₀ ∈ S)
    {μ : Fin n → ℝ} (hy : IsKHWVec ε B μ (f x₀)) :
    ∃ x ∈ S, IsKHWVec ε (tensVd E) μ x ∧ f x = f x₀ := by
  classical
  set e := WithLp.linearEquiv 2 ℂ (Fin n → D) with he_def
  set S' : Submodule ℂ (WithLp 2 (Fin n → D)) := S.comap e.toLinearMap with hS'_def
  have hmem : ∀ z, z ∈ S' ↔ e z ∈ S := fun z => Iff.rfl
  have hfd' : FiniteDimensional ℂ S' := by
    have hinj : Function.Injective (e.toLinearMap.domRestrict S') := by
      intro u v huv
      apply Subtype.ext
      exact e.injective (by simpa using huv)
    exact Module.Finite.of_injective
      ((e.toLinearMap.domRestrict S').codRestrict S (fun z => (hmem z).1 z.2)) (by
        intro u v huv; apply hinj; simpa [LinearMap.codRestrict] using congrArg Subtype.val huv)
  haveI : CompleteSpace S' := FiniteDimensional.complete ℂ S'
  have hU' := k3vdTA_isKUnitary (ε := ε) hU
  have hS' : IsKStableSub ε (coordinateTensorEndAction E) S' := by
    intro a b hab z hz
    rw [hmem] at hz ⊢
    rw [he_def, k3vdTA_e, ← he_def]
    exact hS a b hab _ hz
  set P := S'.starProjection with hP
  set f' : WithLp 2 (Fin n → D) →ₗ[ℂ] Y := f ∘ₗ e.toLinearMap ∘ₗ (P : WithLp 2 (Fin n → D) →ₗ[ℂ] _)
  have hPS : ∀ z, e (P z) ∈ S := fun z => (hmem _).1 (S'.starProjection_apply_mem z)
  have hf' : ∀ a b, ε a = ε b → ∀ x, f' (coordinateTensorEndAction E a b x) = B a b (f' x) := by
    intro a b hab x
    have h1 : P (coordinateTensorEndAction E a b x) = coordinateTensorEndAction E a b (P x) := starProjection_comm hU' hS' hab x
    simp only [f', LinearMap.comp_apply, ContinuousLinearMap.coe_coe, h1]
    change f (e (coordinateTensorEndAction E a b (P x))) = B a b (f (e (P x)))
    rw [he_def, k3vdTA_e, ← he_def]
    exact hf a b hab _ (hPS x)
  have hx₀' : e.symm x₀ ∈ S' := by rw [hmem]; simpa using hx₀
  have hPx₀ : P (e.symm x₀) = e.symm x₀ := Submodule.starProjection_eq_self_iff.2 hx₀'
  have hfx₀ : f' (e.symm x₀) = f x₀ := by simp [f', hPx₀]
  obtain ⟨x, hxS, -, hkhw, hfx⟩ := lift_khw hU' f' hf' hfd' hS' hx₀' (μ := μ) (by rwa [hfx₀])
  have hPx : P x = x := Submodule.starProjection_eq_self_iff.2 hxS
  refine ⟨e x, (hmem x).1 hxS, ⟨fun a => ?_, fun a b hab hε => ?_⟩, ?_⟩
  · have := congrArg e (hkhw.1 a)
    rw [he_def, k3vdTA_e, ← he_def, map_smul] at this
    exact this
  · have := congrArg e (hkhw.2 a b hab hε)
    rw [he_def, k3vdTA_e, ← he_def, map_zero] at this
    exact this
  · rw [← hfx₀, ← hfx]; simp [f', hPx]

end Lift

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
