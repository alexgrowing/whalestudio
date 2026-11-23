import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar

namespace GlobalTheory.Published

def CentreFiniteUnitary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
          ∀ (T : Finset (Fin r)) (φ : GAd σ J → ℂ), IsAutOn σ J X Y T K φ →
            FiniteDimensional ℂ (Submodule.span ℂ {f : GAd σ J → ℂ | ∃ z ∈ levi σ J X Y T,
              (∀ m ∈ levi σ J X Y T, z * m = m * z) ∧ f = fun g => φ (z * g)})

end GlobalTheory.Published

namespace GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {K : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ}

omit [NumberField E] in

theorem centreFinite_of_char (T : Finset (Fin r)) (hφ : ∀ g h, φ (g * h) = φ g * φ h) (a : ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ {f : GAd σ J → ℂ | ∃ z ∈ levi σ J X Y T,
      (∀ m ∈ levi σ J X Y T, z * m = m * z) ∧ f = fun g => (a • φ) (z * g)}) := by
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, -, -, rfl⟩
  exact Submodule.mem_span_singleton.2 ⟨a * φ z, funext fun g => by simp [hφ, mul_assoc]⟩

example (h : IsCMExt F E σ) (hJ : IsHermND σ J) (T : Finset (Fin r)) (c : ℂ) :
    ∃ K, IsMaxCpt σ J K ∧ IsAutOn σ J X Y T K (fun _ => c) ∧
      FiniteDimensional ℂ (Submodule.span ℂ {f : GAd σ J → ℂ | ∃ z ∈ levi σ J X Y T,
        (∀ m ∈ levi σ J X Y T, z * m = m * z) ∧ f = fun g => (fun _ => c) (z * g)}) := by
  obtain ⟨K, hK⟩ := exists_isMaxCpt h hJ
  refine ⟨K, hK, isAutOn_const σ J X Y T K c, ?_⟩
  have e : (fun _ => c) = c • fun _ : GAd σ J => (1 : ℂ) := funext fun _ => by simp
  have := centreFinite_of_char (X := X) (Y := Y) (φ := fun _ : GAd σ J => (1 : ℂ)) T (by simp) c
  rwa [← e] at this

end GlobalTheory.StdPar

end
