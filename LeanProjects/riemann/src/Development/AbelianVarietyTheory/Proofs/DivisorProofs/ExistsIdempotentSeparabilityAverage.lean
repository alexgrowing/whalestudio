import Mathlib
open scoped TensorProduct

namespace GlobalTheory.SepAverage

variable {C : Type} [CommRing C] {H : Type*} [AddCommGroup H] [Module C H]

theorem exists_proj (E' M : Submodule C H) (h : IsCompl E' M) :
    ∃ σ : Module.End C H, (∀ e ∈ E', σ e = 0) ∧ ∀ u, u - σ u ∈ E' := by
  refine ⟨M.projection E' h.symm, fun e he => Submodule.projection_apply_of_mem_right h.symm he, ?_⟩
  intro u
  have := Submodule.projection_add_projection_eq_self h u
  have e : u - M.projection E' h.symm u = E'.projection M h u := by
    exact (eq_sub_of_add_eq this).symm
  rw [e]; exact Submodule.projection_apply_mem _ _

theorem map_smul_top_le (I : Ideal C) (f : Module.End C H) (P : Submodule C H)
    (hf : ∀ w, f w ∈ P) : ∀ w ∈ I • (⊤ : Submodule C H), f w ∈ I • P := by
  intro w hw
  have : Submodule.map f (I • (⊤ : Submodule C H)) ≤ I • P := by
    rw [Submodule.map_smul'']
    apply Submodule.smul_mono le_rfl
    rintro _ ⟨v, -, rfl⟩; exact hf v
  exact this ⟨w, hw, rfl⟩

end GlobalTheory.SepAverage

namespace GlobalTheory.SepAverage

theorem avg_comm {C : Type} [CommRing C] {H : Type*} [AddCommGroup H] [Module C H]
    {O : Type} [Ring O] (ρ : O →+* Module.End C H) {k : ℕ} (x y : Fin k → O)
    (hsep : ∀ c : O, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c))
    (g : Module.End C H) (c : O) :
    ρ c * ∑ j, ρ (x j) * g * ρ (y j) = (∑ j, ρ (x j) * g * ρ (y j)) * ρ c := by
  let B : O →ₗ[ℤ] O →ₗ[ℤ] Module.End C H :=
    LinearMap.mk₂ ℤ (fun a b => ρ a * g * ρ b)
      (by intros; simp [add_mul]) (by intros; simp only [map_zsmul, smul_mul_assoc])
      (by intros; simp [mul_add]) (by intros; simp only [map_zsmul, mul_smul_comm])
  have h := congrArg (TensorProduct.lift B) (hsep c)
  simp only [map_sum, TensorProduct.lift.tmul, B, LinearMap.mk₂_apply] at h
  calc ρ c * ∑ j, ρ (x j) * g * ρ (y j) = ∑ j, ρ (c * x j) * g * ρ (y j) := by
        simp [Finset.mul_sum, map_mul, mul_assoc]
    _ = ∑ j, ρ (x j) * g * ρ (y j * c) := h
    _ = _ := by simp [Finset.sum_mul, map_mul, mul_assoc]

theorem comm_poly {C : Type} [CommRing C] {H : Type*} [AddCommGroup H] [Module C H]
    (a p : Module.End C H) (h : a * p = p * a) :
    a * (p * p * 3 - p * p * p * 2) = (p * p * 3 - p * p * p * 2) * a := by
  have hc : Commute a p := h
  exact (((hc.mul_right hc).mul_right (Commute.ofNat_right a 3)).sub_right
    (((hc.mul_right hc).mul_right hc).mul_right (Commute.ofNat_right a 2))).eq

theorem exists_idempotent_average : ∀ (C O : Type) [CommRing C] [Ring O] (I : Ideal C), I ^ 2 = ⊥ → ∀ (N : ℤ) (k : ℕ) (x y : Fin k → O), ∑ j, x j * y j = (N : O) → (∀ c : O, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρ : O →+* Module.End C H) (ε : Module.End C H), ε * ε = ε → (∀ c, ρ c * ε = ε * ρ c) → ∀ F : Submodule C H, I • ⊤ ≤ F → (∀ c, ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ε x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → ∃ π : Module.End C H, π * π = π ∧ (∀ c, ρ c * π = π * ρ c) ∧ π * ε = π ∧ ε * π = π ∧ (∀ z, ε z = z → z - π z ∈ F) ∧ (∀ z ∈ F, ε z = z → π z ∈ I • (⊤ : Submodule C H)) := by
  intro C O _ _ I hI N k x y hxy hsep hN H _ _ ρ ε hε hρε F hIF hρF hεF hEM
  obtain ⟨E', M, hc, hEF⟩ := hEM
  obtain ⟨σ, hσE, hσ⟩ := exists_proj E' M hc
  obtain ⟨n, hn⟩ := hN.exists_left_inv
  have hE'F : E' ≤ F := hEF ▸ le_sup_left
  have hpres : ∀ f : Module.End C H, ∀ w ∈ I • (⊤ : Submodule C H), f w ∈ I • (⊤ : Submodule C H) :=
    fun f => map_smul_top_le I f ⊤ (fun _ => trivial)
  have hερ : ∀ c v, ε (ρ c v) = ρ c (ε v) := fun c v => (LinearMap.congr_fun (hρε c) v).symm
  set q : Module.End C H := ε * σ * ε with hq
  have hεq : ε * q = q := by simp only [hq, ← mul_assoc, hε]
  have hqε : q * ε = q := by simp only [hq, mul_assoc, hε]
  set p : Module.End C H := n • ∑ j, ρ (x j) * q * ρ (y j) with hp
  have hpc : ∀ c, ρ c * p = p * ρ c := by
    intro c; rw [hp, mul_smul_comm, smul_mul_assoc, avg_comm ρ x y hsep]
  have hεp : ε * p = p := by
    rw [hp, mul_smul_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← mul_assoc, ← hρε, mul_assoc (ρ (x j)) ε q, hεq]
  have hpε : p * ε = p := by
    rw [hp, smul_mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (ρ (x j) * q), hρε, ← mul_assoc, mul_assoc (ρ (x j)) q ε, hqε]
  have hsum : ∀ z, ∑ j, ρ (x j) (ρ (y j) z) = (N : C) • z := by
    intro z
    have := LinearMap.congr_fun (congrArg ρ hxy) z
    simp only [map_sum, map_mul, map_intCast, LinearMap.sum_apply, Module.End.mul_apply,
      Module.End.intCast_apply] at this
    rw [this, Int.cast_smul_eq_zsmul]
  have hpz : ∀ z, p z = n • ∑ j, ρ (x j) (ε (σ (ε (ρ (y j) z)))) := by
    intro z
    simp [hp, hq, LinearMap.sum_apply, Module.End.mul_apply]
  have ha : ∀ z, ε z = z → z - p z ∈ F := by
    intro z hz
    have key : z - p z = n • ∑ j, ρ (x j) (ε (ρ (y j) z - σ (ρ (y j) z))) := by
      have hw : ∀ j, ε (ρ (y j) z) = ρ (y j) z := fun j => by rw [hερ, hz]
      rw [hpz]
      simp only [hw, map_sub, Finset.sum_sub_distrib, hsum, smul_sub, smul_smul, hn, one_smul]
    rw [key]
    refine F.smul_mem _ (F.sum_mem fun j _ => hρF _ _ (hεF _ (hE'F (hσ _))))
  have hb : ∀ z ∈ F, p z ∈ I • (⊤ : Submodule C H) := by
    intro z hzF
    rw [hpz]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => hpres _ _ (hpres _ _ ?_))
    have hv : ε (ρ (y j) z) ∈ F := hεF _ (hρF _ _ hzF)
    rw [← hEF] at hv
    obtain ⟨e, he, t, ht, het⟩ := Submodule.mem_sup.mp hv
    rw [← het, map_add, hσE e he, zero_add]
    exact hpres σ t ht
  set u : Module.End C H := p * p - p with hu_def
  have hu : ∀ z, u z ∈ I • (⊤ : Submodule C H) := by
    intro z
    have h1 : p z = p (ε z) := by rw [← Module.End.mul_apply, hpε]
    have h2 : ε (ε z - p (ε z)) = ε z - p (ε z) := by
      rw [map_sub, ← Module.End.mul_apply ε ε, hε, ← Module.End.mul_apply ε p, hεp]
    have h3 := hb _ (ha (ε z) (by rw [← Module.End.mul_apply, hε]))
    have e : u z = -(p (ε z - p (ε z))) := by
      simp only [hu_def, LinearMap.sub_apply, Module.End.mul_apply, map_sub, h1]
      rw [← h1]; abel
    rw [e]; exact Submodule.neg_mem _ h3
  have huu : u * u = 0 := by
    ext z
    have h := map_smul_top_le I u (I • ⊤) hu _ (hu z)
    rw [← Submodule.mul_smul, ← pow_two, hI, Submodule.bot_smul, Submodule.mem_bot] at h
    simpa using h
  refine ⟨p * p * 3 - p * p * p * 2, ?_, fun c => comm_poly _ _ (hpc c), ?_, ?_, ?_, ?_⟩
  · have e : (p * p * 3 - p * p * p * 2) * (p * p * 3 - p * p * p * 2)
        - (p * p * 3 - p * p * p * 2) = (p * p - p) * (p * p - p) * (4 * (p * p) - 4 * p - 3) := by
      noncomm_ring
    rw [← hu_def, huu, zero_mul] at e
    exact sub_eq_zero.mp e
  · simp only [sub_mul, mul_assoc, hpε]
    simp only [← mul_assoc, Commute.ofNat_left 3 ε |>.eq, Commute.ofNat_left 2 ε |>.eq]
    simp only [mul_assoc, hpε]
  · simp only [mul_sub, ← mul_assoc, hεp]
  all_goals
    have hd : ∀ z, (p * p * 3 - p * p * p * 2) z - p z ∈ I • (⊤ : Submodule C H) := by
      intro z
      have e : p * p * 3 - p * p * p * 2 - p = -((p * p - p) * (2 * p - 1)) := by noncomm_ring
      rw [← LinearMap.sub_apply, e, LinearMap.neg_apply, ← hu_def, Module.End.mul_apply]
      exact Submodule.neg_mem _ (hu _)
  · intro z hz
    have := F.sub_mem (ha z hz) (hIF (hd z))
    convert this using 1; abel
  · intro z hzF _
    have := Submodule.add_mem _ (hb z hzF) (hd z)
    convert this using 1; abel

end GlobalTheory.SepAverage
