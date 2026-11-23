import Mathlib

open KaehlerDifferential

theorem UpperTheory.kaehler_functional_vanishing_of_localization_at_prime :
    ∀ {B S : Type} [CommRing B] [CommRing S] [Algebra ℂ B] [Algebra ℂ S] [Algebra B S] [IsScalarTower ℂ B S] (p : Ideal B) [p.IsPrime] [IsLocalization.AtPrime S p] (ev : S →ₐ[ℂ] ℂ), (∀ b : B, b ∈ p ↔ ev (algebraMap B S b) = 0) → ∀ (d : ℕ) (φ : Ω[B⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)), (∀ (b : B) (ω : Ω[B⁄ℂ]), φ (b • ω) = ev (algebraMap B S b) • φ ω) → (∀ ω : Ω[B⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → B) (ω' : Fin m → Ω[B⁄ℂ]), (∀ i, ev (algebraMap B S (b i)) = 0) ∧ ω = ∑ i, b i • ω' i) → ∃ δ : S →ₗ[ℂ] (Fin d → ℂ), (∀ a b : S, δ (a * b) = ev a • δ b + ev b • δ a) ∧ (∀ b : B, δ (algebraMap B S b) = φ (KaehlerDifferential.D ℂ B b)) ∧ ∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) → ∃ r : (Fin d → ℂ) →ₗ[ℂ] ℂ, ∀ a, η a = r (δ a) := by
  intro B S _ _ _ _ _ _ p _ _ ev hp d φ hφ hker
  haveI : Algebra.FormallyEtale B S := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) p.primeCompl
  have hL : ∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) →
      ∃ L : Ω[B⁄ℂ] →ₗ[ℂ] ℂ, (∀ b : B, L (KaehlerDifferential.D ℂ B b) = η (algebraMap B S b)) ∧
        ∀ (b : B) (ω : Ω[B⁄ℂ]), L (b • ω) = ev (algebraMap B S b) * L ω := by
    intro η hη
    have h1 : η 1 = 0 := by
      have := hη 1 1
      simp only [mul_one, map_one, one_mul] at this
      linear_combination -this
    letI : Module B ℂ := Module.compHom ℂ ((ev.toRingHom).comp (algebraMap B S))
    haveI : IsScalarTower ℂ B ℂ := ⟨fun c b z => by
      change ev (algebraMap B S (c • b)) * z = c * (ev (algebraMap B S b) * z)
      rw [Algebra.smul_def c b, map_mul, map_mul, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
      simp [mul_assoc]⟩
    let D' : Derivation ℂ B ℂ :=
      { toFun := fun b => η (algebraMap B S b)
        map_add' := fun a b => by simp only [map_add]
        map_smul' := fun c b => by
          simp only [RingHom.id_apply]
          rw [Algebra.smul_def c b, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def,
            map_smul]
        map_one_eq_zero' := by simp only [LinearMap.coe_mk, AddHom.coe_mk, map_one, h1]
        leibniz' := fun a b => by
          change η (algebraMap B S (a * b)) = ev (algebraMap B S a) * η (algebraMap B S b) +
            ev (algebraMap B S b) * η (algebraMap B S a)
          rw [map_mul, hη] }
    refine ⟨D'.liftKaehlerDifferential.restrictScalars ℂ, fun b => ?_, fun b ω => ?_⟩
    · simp only [LinearMap.coe_restrictScalars, Derivation.liftKaehlerDifferential_comp_D]
      rfl
    · simp only [LinearMap.coe_restrictScalars, map_smul]
      rfl
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ B S
  letI iS : Module S (Fin d → ℂ) := Module.compHom (Fin d → ℂ) ev.toRingHom
  letI iB : Module B (Fin d → ℂ) :=
    Module.compHom (Fin d → ℂ) ((ev.toRingHom).comp (algebraMap B S))
  haveI : IsScalarTower B S (Fin d → ℂ) := ⟨fun b s v => by
    change ev (b • s) • v = ev (algebraMap B S b) • (ev s • v)
    rw [Algebra.smul_def b s, map_mul, mul_smul]⟩
  let g : Ω[B⁄ℂ] →ₗ[B] (Fin d → ℂ) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun b ω => by rw [RingHom.id_apply]; exact hφ b ω }
  let F : Ω[S⁄ℂ] →ₗ[S] (Fin d → ℂ) := g.liftBaseChange S ∘ₗ e.symm.toLinearMap
  let δ : S →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun s => F (KaehlerDifferential.D ℂ S s)
      map_add' := fun a b => by simp only [map_add]
      map_smul' := fun c s => by
        rw [RingHom.id_apply, Derivation.map_smul,
          ← algebraMap_smul S c (KaehlerDifferential.D ℂ S s), map_smul]
        change ev (algebraMap ℂ S c) • F (KaehlerDifferential.D ℂ S s) =
          c • F (KaehlerDifferential.D ℂ S s)
        rw [AlgHom.commutes]
        rfl }
  have hδL : ∀ a b : S, δ (a * b) = ev a • δ b + ev b • δ a := fun a b => by
    change F (KaehlerDifferential.D ℂ S (a * b)) = _
    rw [Derivation.leibniz, map_add, map_smul, map_smul]
    rfl
  have hδB : ∀ b : B, δ (algebraMap B S b) = φ (KaehlerDifferential.D ℂ B b) := fun b => by
    change g.liftBaseChange S (e.symm (KaehlerDifferential.D ℂ S (algebraMap B S b))) = _
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
      LinearMap.liftBaseChange_tmul]
    change ev 1 • φ (KaehlerDifferential.D ℂ B b) = _
    rw [map_one, one_smul]
  refine ⟨δ, hδL, hδB, fun η hη => ?_⟩
  obtain ⟨L, hLD, hLs⟩ := hL η hη
  have hker' : LinearMap.ker φ ≤ LinearMap.ker L := by
    intro ω hω
    rw [LinearMap.mem_ker] at hω ⊢
    obtain ⟨m, b, ω', hb, rfl⟩ := hker ω hω
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [hLs, hb, zero_mul]
  let φq := (LinearMap.ker φ).liftQ φ le_rfl
  have hinj : LinearMap.ker φq = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  obtain ⟨ψ, hψ⟩ := φq.exists_leftInverse_of_injective hinj
  let r : (Fin d → ℂ) →ₗ[ℂ] ℂ := (LinearMap.ker φ).liftQ L hker' ∘ₗ ψ
  have hr : ∀ ω, L ω = r (φ ω) := fun ω => by
    have hq : ψ (φq (Submodule.Quotient.mk ω)) = Submodule.Quotient.mk ω := by
      simpa using LinearMap.congr_fun hψ (Submodule.Quotient.mk ω)
    change _ = (LinearMap.ker φ).liftQ L hker' (ψ (φq (Submodule.Quotient.mk ω)))
    rw [hq]
    rfl
  refine ⟨r, fun s => ?_⟩
  have hrδ : ∀ a b : S, r (δ (a * b)) = ev a * r (δ b) + ev b * r (δ a) := fun a b => by
    rw [hδL, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hδη : ∀ x : B, r (δ (algebraMap B S x)) = η (algebraMap B S x) := fun x => by
    rw [hδB, ← hr, hLD]
  obtain ⟨⟨b, t⟩, hs⟩ := IsLocalization.surj p.primeCompl s
  have ht : ev (algebraMap B S t) ≠ 0 := fun h => t.2 ((hp t).2 h)
  have h1 := hη s (algebraMap B S t)
  have h2 := hrδ s (algebraMap B S t)
  rw [hs] at h1 h2
  rw [hδη, hδη] at h2
  exact mul_left_cancel₀ ht (by linear_combination h2 - h1)
