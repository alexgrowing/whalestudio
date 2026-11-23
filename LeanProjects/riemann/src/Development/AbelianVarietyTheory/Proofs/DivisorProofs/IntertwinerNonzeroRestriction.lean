import Mathlib

namespace GlobalTheory

open Representation

theorem intertwining_peel_factor {H V U Y : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup U]
    [Module ℂ U] [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ H V)
    (σ : Representation ℂ H U) (θ : Representation ℂ H Y) (F : ρ.IntertwiningMap σ)
    (R S : Subrepresentation ρ) (φ : S.toRepresentation.IntertwiningMap θ) (s : S.toSubmodule)
    (hsR : (s : V) ∈ R.toSubmodule) (hs : φ s ≠ 0)
    (h : ∀ t : S.toSubmodule, (t : V) ∈ R.toSubmodule → F t = 0 → φ t = 0) :
    ∃ (S' : Subrepresentation σ) (φ' : S'.toRepresentation.IntertwiningMap θ), φ' ≠ 0 := by
  classical
  let M : Submodule ℂ S.toSubmodule := R.toSubmodule.comap S.toSubmodule.subtype
  let f : M →ₗ[ℂ] U := F.toLinearMap ∘ₗ S.toSubmodule.subtype ∘ₗ M.subtype
  let ψ : M →ₗ[ℂ] Y := φ.toLinearMap ∘ₗ M.subtype
  have hker : LinearMap.ker f ≤ LinearMap.ker ψ := by
    intro m hm
    simp only [LinearMap.mem_ker] at hm ⊢
    exact h (m : S.toSubmodule) m.2 hm
  let φ0 : LinearMap.range f →ₗ[ℂ] Y :=
    (LinearMap.ker f).liftQ ψ hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  have hφ0 : ∀ m : M, φ0 ⟨f m, m, rfl⟩ = ψ m := by
    intro m
    simp only [φ0, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [f.quotKerEquivRange_symm_apply_image m ⟨m, rfl⟩]
    rfl
  let S' : Subrepresentation σ :=
    { toSubmodule := LinearMap.range f
      apply_mem_toSubmodule := by
        rintro g _ ⟨m, rfl⟩
        let t : S.toSubmodule := S.toRepresentation g (m : S.toSubmodule)
        have htM : t ∈ M := by
          show (t : V) ∈ R.toSubmodule
          exact R.apply_mem_toSubmodule g m.2
        refine ⟨⟨t, htM⟩, ?_⟩
        simp only [f, LinearMap.comp_apply, Submodule.subtype_apply]
        show F (ρ g _) = _
        rw [F.isIntertwining]; rfl }
  have hint : ∀ (g : H) (u : S'.toSubmodule),
      φ0 (S'.toRepresentation g u) = θ g (φ0 u) := by
    rintro g ⟨_, m, rfl⟩
    let t : S.toSubmodule := S.toRepresentation g (m : S.toSubmodule)
    have htM : t ∈ M := by
      show (t : V) ∈ R.toSubmodule
      exact R.apply_mem_toSubmodule g m.2
    have e1 : (S'.toRepresentation g ⟨f m, m, rfl⟩ : LinearMap.range f) = ⟨f ⟨t, htM⟩, ⟨t, htM⟩, rfl⟩ := by
      apply Subtype.ext
      show σ g (F _) = F (ρ g _)
      rw [F.isIntertwining]; rfl
    rw [e1, hφ0, hφ0]
    show φ (S.toRepresentation g _) = θ g (φ _)
    exact IntertwiningMap.isIntertwining _ _ φ g _
  refine ⟨S', ⟨φ0, fun g => by ext u; exact hint g u⟩, ?_⟩
  intro h0
  have := congrArg (fun q : S'.toRepresentation.IntertwiningMap θ => q ⟨f ⟨s, hsR⟩, ⟨s, hsR⟩, rfl⟩) h0
  simp only [IntertwiningMap.coe_zero, Pi.zero_apply] at this
  apply hs
  have e2 := hφ0 ⟨s, hsR⟩
  exact e2.symm.trans this

theorem intertwining_peel_finset {H V U Y : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup U]
    [Module ℂ U] [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ H V)
    (σ : Representation ℂ H U) (θ : Representation ℂ H Y) {ι : Type}
    (E : ι → ρ.IntertwiningMap σ) (S : Subrepresentation ρ)
    (φ : S.toRepresentation.IntertwiningMap θ) (T : Finset ι) :
    ∀ (R : Subrepresentation ρ) (s : S.toSubmodule), (s : V) ∈ R.toSubmodule → φ s ≠ 0 →
      (∀ v ∈ R.toSubmodule, (∀ i ∈ T, E i v = 0) → v = 0) →
      ∃ (S' : Subrepresentation σ) (φ' : S'.toRepresentation.IntertwiningMap θ), φ' ≠ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro R s hsR hs hinj
    exfalso
    have h0 : (s : V) = 0 := hinj _ hsR (by simp)
    have : s = 0 := Subtype.ext h0
    exact hs (by rw [this, map_zero])
  | insert j T hj ih =>
    intro R s hsR hs hinj
    by_cases hA : ∃ t : S.toSubmodule, (t : V) ∈ R.toSubmodule ∧ E j t = 0 ∧ φ t ≠ 0
    · obtain ⟨t, htR, htE, htφ⟩ := hA
      refine ih (R ⊓ (E j).ker) t ⟨htR, htE⟩ htφ ?_
      rintro v ⟨hvR, hvE⟩ hv
      refine hinj v hvR ?_
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hvE
      · exact hv i hi
    · push_neg at hA
      exact intertwining_peel_factor ρ σ θ (E j) R S φ s hsR hs (fun t htR htE => hA t htR htE)

theorem intertwining_peel {H V U Y : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ H V) (σ : Representation ℂ H U)
    (θ : Representation ℂ H Y) {ι : Type} [Fintype ι] (E : ι → ρ.IntertwiningMap σ)
    (R S : Subrepresentation ρ) (φ : S.toRepresentation.IntertwiningMap θ) (s : S.toSubmodule) :
    (s : V) ∈ R.toSubmodule → φ s ≠ 0 → (∀ v ∈ R.toSubmodule, (∀ i, E i v = 0) → v = 0) →
    ∃ (S' : Subrepresentation σ) (φ' : S'.toRepresentation.IntertwiningMap θ), φ' ≠ 0 := by
  intro hsR hs hinj
  exact intertwining_peel_finset ρ σ θ E S φ Finset.univ R s hsR hs
    (fun v hv h => hinj v hv (fun i => h i (Finset.mem_univ i)))

end GlobalTheory
