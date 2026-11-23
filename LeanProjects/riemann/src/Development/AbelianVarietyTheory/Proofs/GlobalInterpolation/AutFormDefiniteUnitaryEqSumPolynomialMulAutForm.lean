import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RightFiniteMemPoly

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryDecomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev infSpan (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_RU (x y : UA E n) (φ : UA E n → ℂ) : RU E n x (RU E n y φ) = RU E n (x * y) φ := by
  rw [map_mul]; rfl

theorem mem_infSpan (φ : UA E n → ℂ) (k : infU E n) : RU E n k φ ∈ infSpan φ :=
  Submodule.subset_span ⟨k, rfl⟩

theorem infSpan_stable (φ : UA E n → ℂ) (k : infU E n) : ∀ ψ ∈ infSpan φ, RU E n k ψ ∈ infSpan φ := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨l, rfl⟩ := h
    rw [RU_RU]
    exact mem_infSpan φ (k * l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul c _ _ h => rw [map_smul]; exact Submodule.smul_mem _ c h

def finStab (φ : UA E n → ℂ) : Subgroup (finU E n) where
  carrier := {k | RU E n k φ = φ}
  one_mem' := by
    change RU E n 1 φ = φ
    rw [map_one]; rfl
  mul_mem' := fun {a b} ha hb => by
    change RU E n (a.1 * b.1) φ = φ
    rw [← RU_RU, show RU E n b φ = φ from hb]
    exact ha
  inv_mem' := fun {a} ha => by
    change RU E n (a.1)⁻¹ φ = φ
    conv_lhs => rw [← show RU E n a φ = φ from ha]
    rw [RU_RU, inv_mul_cancel, map_one]; rfl

theorem isAutFormU_of_mem (hc : ∀ k : infU E n, ∀ g ∈ finU E n, k.1 * g = g * k.1) {φ : UA E n → ℂ}
    (hφ : IsAutFormU φ) (ψ : UA E n → ℂ) (hψ : ψ ∈ infSpan φ) : IsAutFormU ψ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      exact hφ.cont.comp (continuous_mul_const l.1)
    | zero => exact continuous_const
    | add _ _ _ _ h₁ h₂ => exact h₁.add h₂
    | smul c _ _ h => exact h.const_smul c
  · intro γ hγ g
    induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      change φ (γ * g * l) = φ (g * l)
      rw [mul_assoc, hφ.left γ hγ]
    | zero => rfl
    | add _ _ _ _ h₁ h₂ => simp only [Pi.add_apply, h₁, h₂]
    | smul c _ _ h => simp only [Pi.smul_apply, h]
  · refine Subgroup.isOpen_mono (H₁ := finStab φ) (H₂ := finStab ψ) (fun k hk => ?_) hφ.level
    change RU E n k ψ = ψ
    induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      rw [RU_RU, ← hc l k.1 k.2, ← RU_RU, show RU E n k φ = φ from hk]
    | zero => rw [map_zero]
    | add _ _ _ _ h₁ h₂ => rw [map_add, h₁, h₂]
    | smul c _ _ h => rw [map_smul, h]
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := infSpan φ) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact infSpan_stable φ k ψ hψ

def coeff (φ : UA E n → ℂ) (l : infSpan φ →ₗ[ℂ] ℂ) : infSpan φ →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun k => l.comp ((RU E n k).restrict (infSpan_stable φ k))

theorem continuous_coeff {φ : UA E n → ℂ} (hφ : IsAutFormU φ) (l : infSpan φ →ₗ[ℂ] ℂ) :
    Continuous fun k : infU E n => l ⟨RU E n k φ, mem_infSpan φ k⟩ := by
  have := hφ.kfin
  refine l.continuous_of_finiteDimensional.comp (Continuous.subtype_mk (continuous_pi fun g => ?_) _)
  exact hφ.cont.comp (continuous_const.mul continuous_subtype_val)

theorem finite_coeff {φ : UA E n → ℂ} (hφ : IsAutFormU φ) (l : infSpan φ →ₗ[ℂ] ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => fun x : infU E n =>
      l ⟨RU E n (x * k : infU E n) φ, mem_infSpan φ (x * k)⟩)) := by
  have := hφ.kfin
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (coeff φ l)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine ⟨⟨_, mem_infSpan φ k⟩, funext fun x => congrArg l (Subtype.ext ?_)⟩
  exact RU_RU x.1 k.1 φ

theorem exists_poly_mul_autForm (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ)
    (hφ : IsAutFormU φ) : ∃ (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → UA E n → ℂ),
      (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}
        ∧ IsAutFormU (e i)) ∧ ∀ (k : infU E n) (g : UA E n), φ (g * k) = ∑ i, p i k * e i g := by
  have := hφ.kfin
  let b := Module.finBasis ℂ (infSpan φ)
  refine ⟨_, fun i k => b.coord i ⟨RU E n k φ, mem_infSpan φ k⟩, fun i => (b i).1, fun i => ⟨?_, ?_⟩, fun k g => ?_⟩
  · exact GlobalTheory.UnitaryBC.rightFinite_mem_poly E n _ (continuous_coeff hφ _) (finite_coeff hφ _)
  · exact isAutFormU_of_mem (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.1 hφ _ (b i).2
  · have h := congrArg (fun v : infSpan φ => v.1 g) (b.sum_repr ⟨RU E n k φ, mem_infSpan φ k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm

end GlobalTheory.UnitaryDecomp

end
