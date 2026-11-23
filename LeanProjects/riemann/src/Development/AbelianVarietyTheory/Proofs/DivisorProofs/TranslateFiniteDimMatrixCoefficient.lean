import Mathlib

namespace GlobalTheory

private def rightTranslLin {G : Type} [CommGroup G] (s : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun t => t * s)

theorem exists_matrix_rep_of_finiteDimensional_translates :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] (H : Set G) (Fn : G → ℂ),
      (∀ s : G, Continuous fun t : G => t * s) → Continuous Fn →
      (∀ γ ∈ H, ∀ t, Fn (γ * t) = Fn t) →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s : G => fun t => Fn (t * s))) →
      ∃ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (a : Fin d → Fin d → ℂ),
        (∀ γ ∈ H, ρ γ = 1) ∧ (∀ i j, Continuous fun s => ρ s i j) ∧
        ∀ t, Fn t = ∑ i, ∑ j, a i j * ρ t i j := by
  intro G _ _ H Fn hmul hF hH hfin
  classical
  set V : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range fun s : G => fun t => Fn (t * s))
    with hV
  have hmap : ∀ s : G, ∀ v ∈ V, rightTranslLin s v ∈ V := by
    intro s v hv
    have : V ≤ V.comap (rightTranslLin s) := by
      rw [hV, Submodule.span_le]
      rintro _ ⟨s', rfl⟩
      refine Submodule.subset_span ⟨s * s', ?_⟩
      funext t
      simp [rightTranslLin, LinearMap.funLeft_apply, mul_assoc]
    exact this hv
  have hcont : ∀ v ∈ V, Continuous v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact hF.comp (hmul s)
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.const_smul c
  have hinv : ∀ γ ∈ H, ∀ v ∈ V, ∀ t, v (t * γ) = v t := by
    intro γ hγ v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      intro t
      show Fn (t * γ * s) = Fn (t * s)
      rw [mul_comm t γ, mul_assoc, hH γ hγ]
    | zero => intro t; rfl
    | add x y _ _ hx hy => intro t; simp [hx t, hy t]
    | smul c x _ hx => intro t; simp [hx t]
  let R : G →* Module.End ℂ V :=
    { toFun := fun s => (rightTranslLin s).restrict (hmap s)
      map_one' := by
        ext v t
        simp [rightTranslLin, LinearMap.funLeft_apply]
      map_mul' := by
        intro s s'
        ext v t
        simp [rightTranslLin, LinearMap.funLeft_apply, mul_assoc] }
  have hR : ∀ s (v : V) t, (R s v : G → ℂ) t = (v : G → ℂ) (t * s) := fun s v t => rfl
  let b := Module.finBasis ℂ V
  let ρ : G →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    ((LinearMap.toMatrixAlgEquiv b : Module.End ℂ V ≃ₐ[ℂ] _) : Module.End ℂ V →* _).comp R
  have hρ : ∀ s i j, ρ s i j = b.repr (R s (b j)) i := by
    intro s i j
    exact LinearMap.toMatrixAlgEquiv_apply b (R s) i j
  have hFV : Fn ∈ V := Submodule.subset_span ⟨1, by funext t; simp⟩
  refine ⟨_, ρ, fun i j => b.repr ⟨Fn, hFV⟩ j * (b i : G → ℂ) 1, ?_, ?_, ?_⟩
  · intro γ hγ
    have : R γ = 1 := by
      ext v t
      exact hinv γ hγ v v.2 t
    show LinearMap.toMatrixAlgEquiv b (R γ) = 1
    rw [this, map_one]
  · intro i j
    simp only [hρ]
    have h1 : Continuous (b.coord i) := LinearMap.continuous_of_finiteDimensional _
    have h2 : Continuous fun s => R s (b j) := by
      refine continuous_induced_rng.2 (continuous_pi fun x => ?_)
      have : (fun s => (R s (b j) : G → ℂ) x) = fun s => (b j : G → ℂ) (s * x) := by
        funext s
        rw [hR, mul_comm]
      exact this ▸ (hcont _ (b j).2).comp (hmul x)
    exact h1.comp h2
  · intro t
    let ev : V →ₗ[ℂ] ℂ := (LinearMap.proj (1 : G)).comp V.subtype
    have hev : ∀ v : V, ev v = (v : G → ℂ) 1 := fun v => rfl
    have e1 : Fn t = ev (R t ⟨Fn, hFV⟩) := by rw [hev, hR, one_mul]
    rw [e1, Finset.sum_comm]
    conv_lhs => rw [← b.sum_repr ⟨Fn, hFV⟩]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul]
    conv_lhs => rw [← b.sum_repr (R t (b j))]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hρ, hev, smul_eq_mul, smul_eq_mul]
    ring

end GlobalTheory
