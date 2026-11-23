import Mathlib

namespace GlobalTheory

theorem isotropic_summand_lift : ∀ (R : Type) [CommRing R] (I : Ideal R) (D : Type) [AddCommGroup D] [Module R D] [Module.Finite R D] [Module.Projective R D] (φ : D →ₗ[R] D →ₗ[R] R), I ^ 2 = ⊥ → IsUnit (2 : R) → (∀ x y, φ x y = -φ y x) → (∀ l : D →ₗ[R] R, ∃ z, ∀ x, l x - φ x z ∈ I) → ∀ F N : Submodule R D, IsCompl F N → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → ∃ E N' : Submodule R D, IsCompl E N' ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ E ⊔ I • (⊤ : Submodule R D) = F ⊔ I • (⊤ : Submodule R D) := by
  intro R _ I D _ _ _ _ φ hI2 h2 hskew hsurj F N hFN hF
  have hII : ∀ a ∈ I, ∀ b ∈ I, a * b = 0 := by
    intro a ha b hb
    have h : a * b ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hI2] at h; exact (Submodule.mem_bot R).1 h
  have hφI : ∀ a ∈ I • (⊤ : Submodule R D), ∀ y, φ a y ∈ I := by
    intro a ha y
    refine Submodule.smul_induction_on (p := fun a => φ a y ∈ I) ha ?_ ?_
    · intro r hr m _
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · intro x z hx hz
      simp only [map_add, LinearMap.add_apply]
      exact I.add_mem hx hz
  have hφII : ∀ a ∈ I • (⊤ : Submodule R D), ∀ b ∈ I • (⊤ : Submodule R D), φ a b = 0 := by
    intro a ha b hb
    refine Submodule.smul_induction_on (p := fun a => φ a b = 0) ha ?_ ?_
    · intro r hr m _
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      have : φ m b ∈ I := by rw [hskew]; exact I.neg_mem (hφI b hb m)
      exact hII r hr _ this
    · intro x z hx hz
      simp only [map_add, LinearMap.add_apply, hx, hz, add_zero]
  have hsmul0 : ∀ r ∈ I, ∀ w ∈ I • (⊤ : Submodule R D), r • w = 0 := by
    intro r hr w hw
    refine Submodule.smul_induction_on (p := fun w => r • w = 0) hw ?_ ?_
    · intro r' hr' m _
      rw [smul_smul, hII r hr r' hr', zero_smul]
    · intro x z hx hz
      rw [smul_add, hx, hz, add_zero]

  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R D
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfs : ∀ x, f (s x) = x := fun x => by simpa using LinearMap.congr_fun hs x
  let e : Fin n → D := fun i => f (fun j => if i = j then 1 else 0)
  have hexp : ∀ x, x = ∑ i, s x i • e i := fun x => by
    conv_lhs => rw [← hfs x]
    exact LinearMap.pi_apply_eq_sum_univ f (s x)
  choose z hz using fun i : Fin n => hsurj ((LinearMap.proj i).comp s)
  have hz' : ∀ i x, s x i - φ x (z i) ∈ I := fun i x => by simpa using hz i x

  let P : D →ₗ[R] D := F.subtype ∘ₗ Submodule.linearProjOfIsCompl F N hFN
  have hPF : ∀ x, P x ∈ F := fun x => (Submodule.linearProjOfIsCompl F N hFN x).2
  have hPx : ∀ x ∈ F, P x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hFN ⟨x, hx⟩)
  let B : D →ₗ[R] D →ₗ[R] R := φ.compl₁₂ P P
  have hB : ∀ x y, B x y = φ (P x) (P y) := fun x y => rfl
  have hBI : ∀ x y, B x y ∈ I := fun x y => hF _ (hPF x) _ (hPF y)
  let c : R := ↑(h2.unit⁻¹)
  have hc : c * 2 = 1 := h2.val_inv_mul
  let T : D →ₗ[R] D := ∑ i, (-c) • (LinearMap.smulRight (B (e i)) (z i))
  have hT : ∀ y, T y = ∑ i, (-c) • (B (e i) y • z i) := fun y => by
    simp [T]
  have hTr : ∀ y, T y ∈ I • (⊤ : Submodule R D) := fun y => by
    rw [hT]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.smul_mem_smul (hBI _ _) Submodule.mem_top)
  have hTI : ∀ a ∈ I • (⊤ : Submodule R D), T a = 0 := by
    intro a ha
    refine Submodule.smul_induction_on (p := fun a => T a = 0) ha ?_ ?_
    · intro r hr m _
      rw [map_smul]; exact hsmul0 r hr _ (hTr m)
    · intro x w hx hw
      rw [map_add, hx, hw, add_zero]
  have hTT : ∀ y, T (T y) = 0 := fun y => hTI _ (hTr y)
  have hkey0 : ∀ x y, φ x (T y) = -c * B x y := by
    intro x y
    have hBx : B x y = ∑ i, s x i * B (e i) y := by
      conv_lhs => rw [hexp x]
      simp [map_sum, LinearMap.sum_apply, smul_eq_mul]
    have h0 : ∑ i, B (e i) y * (s x i - φ x (z i)) = 0 :=
      Finset.sum_eq_zero fun i _ => hII _ (hBI _ _) _ (hz' i x)
    rw [hT, map_sum, hBx]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    have h1 : ∑ i, -c * (s x i * B (e i) y) - ∑ i, -c * (B (e i) y * φ x (z i)) = 0 := by
      rw [← Finset.sum_sub_distrib]
      have : ∀ i, -c * (s x i * B (e i) y) - -c * (B (e i) y * φ x (z i))
          = -c * (B (e i) y * (s x i - φ x (z i))) := fun i => by ring
      simp only [this]
      rw [← Finset.mul_sum, h0, mul_zero]
    exact (sub_eq_zero.1 h1).symm
  have hkey : ∀ x ∈ F, ∀ y ∈ F, φ x (T y) = -c * φ x y := by
    intro x hx y hy
    rw [hkey0, hB, hPx x hx, hPx y hy]
  let u : D ≃ₗ[R] D := LinearEquiv.ofLinear (LinearMap.id + T) (LinearMap.id - T)
    (LinearMap.ext fun y => by simp [hTT]) (LinearMap.ext fun y => by simp [hTT])
  have hu : ∀ x, u x = x + T x := fun x => rfl
  refine ⟨F.map (u : D →ₗ[R] D), N.map (u : D →ₗ[R] D), ?_, ?_, ?_⟩
  · exact (Submodule.orderIsoMapComap u).isCompl hFN
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show φ (u x) (u y) = 0
    rw [hu, hu, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
    have h1 := hkey x hx y hy
    have h2' := hkey y hy x hx
    have h3 := hskew (T x) y
    have h4 := hskew y x
    have h5 := hφII (T x) (hTr x) (T y) (hTr y)
    linear_combination h1 + h3 - h2' + h5 + c * h4 - (φ x y) * hc
  · apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rintro _ ⟨x, hx, rfl⟩
      show u x ∈ _
      rw [hu]
      exact Submodule.add_mem_sup hx (hTr x)
    · refine sup_le ?_ le_sup_right
      intro x hx
      refine Submodule.mem_sup.2 ⟨u x, ⟨x, hx, rfl⟩, -T x, Submodule.neg_mem _ (hTr x), ?_⟩
      rw [hu]; abel

end GlobalTheory
