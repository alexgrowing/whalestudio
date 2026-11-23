import Mathlib

namespace GlobalTheory.PiIsotypic

open Representation

theorem nontrivial_of_isIrreducible {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  haveI := h
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.ext (Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule K V))).symm)

theorem exists_irreducible_subrep {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧
      Module.finrank K S.toSubmodule = m :=
    ⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, T.toSubmodule ≠ ⊥ →
      Module.finrank K S.toSubmodule ≤ Module.finrank K T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  refine ⟨S, ?_⟩
  have : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule K S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'⟩
  refine ⟨fun T => ?_⟩
  by_cases hT : T.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hT)
  · right
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hT' : T'.toSubmodule ≠ ⊥ := by
      intro h
      apply hT
      have h2 : T.toSubmodule.map S.toSubmodule.subtype = ⊥ := h
      rwa [← Submodule.map_bot S.toSubmodule.subtype,
        (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff] at h2
    have h1 := hmin T' hT'
    have h2 : Module.finrank K T'.toSubmodule = Module.finrank K T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 : T.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h2 ▸ h1))
    exact Subrepresentation.toSubmodule_injective h3

def subrepOrderIso {K G V V' : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (σ : Representation K G V) (τ : Representation K G V')
    (e : V ≃ₗ[K] V') (he : ∀ g v, τ g (e v) = e (σ g v)) :
    Subrepresentation σ ≃o Subrepresentation τ where
  toFun T := ⟨T.toSubmodule.map (e : V →ₗ[K] V'), by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨σ g v, T.apply_mem_toSubmodule g hv, (he g v).symm⟩⟩
  invFun U := ⟨U.toSubmodule.comap (e : V →ₗ[K] V'), by
    intro g v hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
    rw [← he]
    exact U.apply_mem_toSubmodule g hv⟩
  left_inv T := Subrepresentation.ext (Submodule.comap_map_eq_of_injective e.injective _)
  right_inv U := Subrepresentation.ext (Submodule.map_comap_eq_of_surjective e.surjective _)
  map_rel_iff' {a b} := by
    show a.toSubmodule.map (e : V →ₗ[K] V') ≤ b.toSubmodule.map (e : V →ₗ[K] V') ↔
      a.toSubmodule ≤ b.toSubmodule
    exact Submodule.map_le_map_iff_of_injective e.injective _ _

theorem isIrreducible_of_linearEquiv {K G V V' : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [AddCommGroup V'] [Module K V'] (σ : Representation K G V)
    (τ : Representation K G V') (e : V ≃ₗ[K] V') (he : ∀ g v, τ g (e v) = e (σ g v))
    (h : σ.IsIrreducible) : τ.IsIrreducible := by
  haveI := h
  exact (subrepOrderIso σ τ e he).symm.isSimpleOrder

end GlobalTheory.PiIsotypic

namespace GlobalTheory.PiIsotypic

open Representation

theorem isotypic_factor_of_isIrreducible_pi : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (∀ i, G i) W), ρ.IsIrreducible → ∀ i, ∃ (n : ℕ) (τ : Representation ℂ (G i) (Fin n → ℂ)), τ.IsIrreducible ∧ (∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, Function.Injective φ ∧ ∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ Submodule.span ℂ {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} = ⊤ := by
  intro ι _ _ G _ _ W _ _ _ ρ hρ i
  classical
  haveI : Nontrivial W := nontrivial_of_isIrreducible ρ hρ
  let ρi : Representation ℂ (G i) W := ρ.comp (MonoidHom.mulSingle G i)
  obtain ⟨S, hS⟩ := exists_irreducible_subrep ρi
  let n := Module.finrank ℂ S.toSubmodule
  let e : S.toSubmodule ≃ₗ[ℂ] (Fin n → ℂ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [n])
  let τ : Representation ℂ (G i) (Fin n → ℂ) :=
    { toFun := fun g => e.toLinearMap ∘ₗ S.toRepresentation g ∘ₗ e.symm.toLinearMap
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hτe : ∀ g v, τ g (e v) = e (S.toRepresentation g v) := by
    intro g v; simp [τ]
  have hτ : τ.IsIrreducible := isIrreducible_of_linearEquiv S.toRepresentation τ e hτe hS
  let φ0 : (Fin n → ℂ) →ₗ[ℂ] W := S.toSubmodule.subtype ∘ₗ e.symm.toLinearMap
  have hφ0 : ∀ g z, φ0 (τ g z) = ρ (Pi.mulSingle i g) (φ0 z) := by
    intro g z
    simp [φ0, τ]
    rfl
  have hinj : Function.Injective φ0 :=
    Subtype.val_injective.comp e.symm.injective
  refine ⟨n, τ, hτ, ⟨φ0, hinj, hφ0⟩, ?_⟩
  set T : Set W := {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W,
    (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} with hTdef
  have hstab : ∀ g y, y ∈ T → ρ g y ∈ T := by
    rintro g y ⟨φ, hφ, hy⟩
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
    let g' : ∀ j, G j := g * Pi.mulSingle i (g i)⁻¹
    have hcomm : ∀ h : G i, g' * Pi.mulSingle i h = Pi.mulSingle i h * g' := by
      intro h
      funext j
      by_cases hj : j = i
      · subst hj
        simp [g']
      · simp [g', Pi.mulSingle_eq_of_ne hj]
    have hg : g = g' * Pi.mulSingle i (g i) := by
      simp only [g', mul_assoc, ← Pi.mulSingle_mul, inv_mul_cancel, Pi.mulSingle_one, mul_one]
    refine ⟨ρ g' ∘ₗ φ, ?_, LinearMap.mem_range.2 ⟨τ (g i) z, ?_⟩⟩
    · intro h z'
      simp only [LinearMap.comp_apply]
      rw [hφ, ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    · simp only [LinearMap.comp_apply]
      rw [hφ, ← Module.End.mul_apply, ← map_mul, ← hg]
  let U : Subrepresentation ρ := ⟨Submodule.span ℂ T, fun g v hv => by
    have hle : Submodule.span ℂ T ≤ (Submodule.span ℂ T).comap (ρ g) :=
      Submodule.span_le.2 (fun y hy => Submodule.subset_span (hstab g y hy))
    exact hle hv⟩
  haveI := hρ
  rcases eq_bot_or_eq_top U with h | h
  · exfalso
    have hspan : Submodule.span ℂ T = ⊥ := congrArg Subrepresentation.toSubmodule h
    haveI : Nontrivial (Fin n → ℂ) := nontrivial_of_isIrreducible τ hτ
    obtain ⟨z, hz⟩ := exists_ne (0 : Fin n → ℂ)
    have hmem : φ0 z ∈ Submodule.span ℂ T :=
      Submodule.subset_span ⟨φ0, hφ0, LinearMap.mem_range.2 ⟨z, rfl⟩⟩
    rw [hspan, Submodule.mem_bot] at hmem
    exact hz (hinj (by rw [hmem, map_zero]))
  · exact congrArg Subrepresentation.toSubmodule h

end GlobalTheory.PiIsotypic
