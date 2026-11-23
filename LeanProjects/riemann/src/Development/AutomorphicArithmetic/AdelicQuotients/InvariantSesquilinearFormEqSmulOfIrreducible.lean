import Mathlib

theorem UpperTheory.invariant_sesquilinearForm_eq_smul_of_irreducible :
    ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (ρ : G →* Module.End ℂ V)
      (_hI : ∀ W : Submodule ℂ V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
      (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (_hh : ∀ a b, B b a = star (B a b)) (_hp : ∀ a, a ≠ 0 → 0 < (B a a).re)
      (_hinv : ∀ g a b, B (ρ g a) (ρ g b) = B a b) (B₁ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ g a b, B₁ (ρ g a) (ρ g b) = B₁ a b) → ∃ c : ℂ, ∀ a b, B₁ a b = c * B a b := by
  intro G V _ _ _ _ _ ρ hI B hh hp hinv B₁ h₁
  classical
  let n := Module.finrank ℂ V
  let e := Module.finBasis ℂ V
  let φB : V →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun j => B.flip (e j))
  let φ₁ : V →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun j => B₁.flip (e j))
  have hinj : Function.Injective φB := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h0 : B a = 0 := e.ext (fun j => by
      have := congrFun ha j
      simpa [φB] using this)
    by_contra hne
    have := hp a hne
    rw [h0] at this
    simp at this
  have hsurj : Function.Surjective φB :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Module.finrank_fin_fun])).mp hinj
  let E := LinearEquiv.ofBijective φB ⟨hinj, hsurj⟩
  let T : Module.End ℂ V := E.symm.toLinearMap ∘ₗ φ₁
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hTv : T v = c • v := hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  have key : B₁ v = c • B v := by
    apply e.ext
    intro j
    have h1 : φB (T v) = φ₁ v := E.apply_symm_apply (φ₁ v)
    rw [hTv] at h1
    have h2 := congrFun h1 j
    simp [φB, φ₁] at h2
    simpa [LinearMap.smul_apply] using h2.symm
  let W := LinearMap.ker (B₁ - c • B)
  have hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W := by
    intro g w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have hw' : ∀ b, B₁ w b = c * B w b := by
      intro b
      have := LinearMap.congr_fun hw b
      simp at this
      linear_combination this
    ext b
    have hb : ρ g (ρ g⁻¹ b) = b := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    obtain ⟨b', rfl⟩ : ∃ b', ρ g b' = b := ⟨_, hb⟩
    simp [h₁, hinv, hw']
  rcases hI W hW with h | h
  · have hvW : v ∈ W := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, key, sub_self]
    rw [h] at hvW
    exact absurd ((Submodule.mem_bot ℂ).mp hvW) hv0
  · refine ⟨c, fun a b => ?_⟩
    have ha : a ∈ W := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at ha
    have := LinearMap.congr_fun ha b
    simp at this
    linear_combination this
