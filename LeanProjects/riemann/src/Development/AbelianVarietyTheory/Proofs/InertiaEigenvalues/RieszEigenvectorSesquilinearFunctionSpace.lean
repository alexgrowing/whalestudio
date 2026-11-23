import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointExistsUniqueOfPosDef

open scoped ComplexConjugate

namespace GlobalTheory

lemma sesq_rules_of_combination {X : Type} (C : Submodule ℂ (X → ℂ)) (F : (X → ℂ) → (X → ℂ) → ℂ)
    (hl : ∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → F (a • f + f') g = star a * F f g + F f' g)
    (hr : ∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → F f (a • g + g') = a * F f g + F f g') :
    (∀ f f' g, f ∈ C → f' ∈ C → g ∈ C → F (f + f') g = F f g + F f' g) ∧
    (∀ (a : ℂ) f g, f ∈ C → g ∈ C → F (a • f) g = star a * F f g) ∧
    (∀ f g g', f ∈ C → g ∈ C → g' ∈ C → F f (g + g') = F f g + F f g') ∧
    (∀ (a : ℂ) f g, f ∈ C → g ∈ C → F f (a • g) = a * F f g) := by
  have l0 : ∀ g, g ∈ C → F 0 g = 0 := by
    intro g hg
    have := hl 1 0 0 g C.zero_mem C.zero_mem hg
    simp only [one_smul, add_zero, star_one, one_mul] at this
    linear_combination -this
  have r0 : ∀ f, f ∈ C → F f 0 = 0 := by
    intro f hf
    have := hr 1 f 0 0 hf C.zero_mem C.zero_mem
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f f' g hf hf' hg
    simpa using hl 1 f f' g hf hf' hg
  · intro a f g hf hg
    have := hl a f 0 g hf C.zero_mem hg
    rwa [add_zero, l0 g hg, add_zero] at this
  · intro f g g' hf hg hg'
    simpa using hr 1 f g g' hf hg hg'
  · intro a f g hf hg
    have := hr a f g 0 hf hg C.zero_mem
    rwa [add_zero, r0 f hf, add_zero] at this

theorem riesz_and_eigenvector_of_sesq_on_fun_space : ∀ (X : Type) (C : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ C →
    ∀ (ip Φ : (X → ℂ) → (X → ℂ) → ℂ),
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → ip (a • f + f') g = star a * ip f g + ip f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → ip f (a • g + g') = a * ip f g + ip f g') →
    (∀ f g : X → ℂ, f ∈ C → g ∈ C → ip g f = star (ip f g)) →
    (∀ f : X → ℂ, f ∈ C → f ≠ 0 → 0 < (ip f f).re) →
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g') →
    (∀ f : X → ℂ, f ∈ C → ∃ h : X → ℂ, h ∈ C ∧ ∀ g : X → ℂ, g ∈ C → ip h g = Φ f g) ∧
    (C ≠ ⊥ → ∃ c : ℂ, ∃ e : X → ℂ, e ∈ C ∧ e ≠ 0 ∧ ∀ f : X → ℂ, f ∈ C → Φ f e = c * ip f e) := by
  intro X C hfin ip Φ hl hr hs hp Φl Φr
  haveI := hfin
  obtain ⟨ipa, ips, ipa', ips'⟩ := sesq_rules_of_combination C ip hl hr
  obtain ⟨Φa, Φs, Φa', Φs'⟩ := sesq_rules_of_combination C Φ Φl Φr
  let B : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun x y => ip (y : X → ℂ) x)
    (fun m₁ m₂ n => by simp only [Submodule.coe_add]; exact ipa' _ _ _ n.2 m₁.2 m₂.2)
    (fun c m n => by
      simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]; exact ips' c _ _ n.2 m.2)
    (fun m n₁ n₂ => by simp only [Submodule.coe_add]; exact ipa _ _ _ n₁.2 n₂.2 m.2)
    (fun c m n => by
      simp only [Submodule.coe_smul, smul_eq_mul, starRingEnd_apply]; exact ips c _ _ n.2 m.2)
  have Bsym : ∀ x y, B x y = conj (B y x) := by
    intro x y
    simp only [B, LinearMap.mk₂'ₛₗ_apply, starRingEnd_apply]
    exact hs _ _ x.2 y.2
  have Bpos : ∀ x, x ≠ 0 → 0 < (B x x).re := by
    intro x hx
    simp only [B, LinearMap.mk₂'ₛₗ_apply]
    exact hp _ x.2 (by rwa [ne_eq, Submodule.coe_eq_zero])
  let ipA : ℂ →ₗ[ℂ] ℂ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun a b => conj b * a) (by intros; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)
  have riesz : ∀ L : C →ₗ[ℂ] ℂ, ∃ x : C, ∀ y : C, ip (x : X → ℂ) y = L y := by
    intro L
    obtain ⟨x, hx, -⟩ := hermitian_adjoint_exists_unique ℂ C ipA B Bsym Bpos L 1
    exact ⟨x, fun y => by have := hx y; simpa [B, ipA] using this⟩
  refine ⟨?_, ?_⟩
  · intro f hf
    let L : C →ₗ[ℂ] ℂ :=
      { toFun := fun g => Φ f g
        map_add' := fun g g' => Φa' _ _ _ hf g.2 g'.2
        map_smul' := fun c g => Φs' c _ _ hf g.2 }
    obtain ⟨x, hx⟩ := riesz L
    exact ⟨x, x.2, fun g hg => hx ⟨g, hg⟩⟩
  · intro hC
    let large₂ : C → (C →ₗ[ℂ] ℂ) := fun g =>
      { toFun := fun f => star (Φ f g)
        map_add' := fun f f' => by
          simp only [Submodule.coe_add]; rw [Φa _ _ _ f.2 f'.2 g.2, star_add]
        map_smul' := fun c f => by
          simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
          rw [Φs c _ _ f.2 g.2, star_mul, star_star, mul_comm] }
    have hex : ∀ g : C, ∃ x : C, ∀ f : C, ip (f : X → ℂ) x = Φ f g := by
      intro g
      obtain ⟨x, hx⟩ := riesz (large₂ g)
      refine ⟨x, fun f => ?_⟩
      rw [hs _ _ x.2 f.2, hx f]
      simp [large₂]
    choose R hR using hex
    have inj : ∀ x y : C, (∀ f : C, ip (f : X → ℂ) x = ip f y) → x = y := by
      intro x y h
      by_contra hne
      have hd : ((x - y : C) : X → ℂ) = (-1 : ℂ) • (y : X → ℂ) + x := by
        rw [Submodule.coe_sub]; ext t; simp; ring
      have h1 := hr (-1) ((x - y : C) : X → ℂ) y x (x - y).2 y.2 x.2
      rw [← hd, h (x - y)] at h1
      have h2 := hp _ (x - y).2 (by rwa [ne_eq, Submodule.coe_eq_zero, sub_eq_zero])
      have h3 : ip ((x - y : C) : X → ℂ) ((x - y : C) : X → ℂ) = 0 := by rw [h1]; ring
      rw [h3] at h2
      simp at h2
    let Rl : Module.End ℂ C :=
      { toFun := R
        map_add' := fun g g' => inj _ _ (fun f => by
          rw [hR, Submodule.coe_add, Submodule.coe_add, ipa' _ _ _ f.2 (R g).2 (R g').2, hR, hR,
            Φa' _ _ _ f.2 g.2 g'.2])
        map_smul' := fun c g => inj _ _ (fun f => by
          rw [hR, Submodule.coe_smul, RingHom.id_apply, Submodule.coe_smul, ips' c _ _ f.2 (R g).2, hR,
            Φs' c _ _ f.2 g.2]) }
    haveI : Nontrivial C := Submodule.nontrivial_iff_ne_bot.mpr hC
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue Rl
    obtain ⟨e, he⟩ := hc.exists_hasEigenvector
    refine ⟨c, e, e.2, by rw [ne_eq, Submodule.coe_eq_zero]; exact he.2, fun f hf => ?_⟩
    rw [← hR e ⟨f, hf⟩]
    show ip f ((Rl e : C) : X → ℂ) = _
    rw [he.apply_eq_smul, Submodule.coe_smul, ips' c _ _ hf e.2]

end GlobalTheory
