import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem finite_realEmbeddings (F : Type) [Field F] [NumberField F] : Finite (F →+* ℝ) :=
  Finite.of_injective (fun σ : F →+* ℝ => (Complex.ofRealHom.comp σ : F →+* ℂ)) (by
    intro σ τ h
    ext x
    have := congrArg (fun f : F →+* ℂ => f x) h
    simpa using this)

theorem bounded_ratio_on_basis_cone : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) →
    ∃ R : ℝ, 0 < R ∧ ∀ x : F, (∀ i, 0 < b.repr x i) → ∀ σ τ : F →+* ℝ, σ x ≤ R * τ x := by
  intro F _ _ κ _ b hb
  classical
  haveI := finite_realEmbeddings F
  haveI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  have hterm : ∀ (i : κ) (σ τ : F →+* ℝ), 0 < σ (b i) / τ (b i) := fun i σ τ => div_pos (hb i σ) (hb i τ)
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 1 + ∑ i, ∑ σ : F →+* ℝ, ∑ τ : F →+* ℝ, σ (b i) / τ (b i) := ⟨_, rfl⟩
  have hsum : 0 ≤ ∑ i, ∑ σ : F →+* ℝ, ∑ τ : F →+* ℝ, σ (b i) / τ (b i) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun τ _ => (hterm i σ τ).le
  have hR : 0 < R := by rw [hRdef]; linarith
  have hle : ∀ (i : κ) (σ τ : F →+* ℝ), σ (b i) ≤ R * τ (b i) := by
    intro i σ τ
    have h1 : σ (b i) / τ (b i) ≤ ∑ τ' : F →+* ℝ, σ (b i) / τ' (b i) :=
      Finset.single_le_sum (f := fun τ' : F →+* ℝ => σ (b i) / τ' (b i)) (fun τ' _ => (hterm i σ τ').le) (Finset.mem_univ τ)
    have h2 : ∑ τ' : F →+* ℝ, σ (b i) / τ' (b i) ≤ ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i) :=
      Finset.single_le_sum (f := fun σ' : F →+* ℝ => ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i))
        (fun σ' _ => Finset.sum_nonneg fun τ' _ => (hterm i σ' τ').le) (Finset.mem_univ σ)
    have h3 : ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i) ≤ ∑ j, ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b j) / τ' (b j) :=
      Finset.single_le_sum (f := fun j => ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b j) / τ' (b j))
        (fun j _ => Finset.sum_nonneg fun σ' _ => Finset.sum_nonneg fun τ' _ => (hterm j σ' τ').le) (Finset.mem_univ i)
    have h4 : σ (b i) / τ (b i) ≤ R := by rw [hRdef]; linarith
    exact (div_le_iff₀ (hb i τ)).1 h4
  refine ⟨R, hR, fun x hx σ τ => ?_⟩
  have hrep : ∀ ρ : F →+* ℝ, ρ x = ∑ i, (b.repr x i : ℝ) * ρ (b i) := by
    intro ρ
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
  rw [hrep σ, hrep τ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hc : (0 : ℝ) < (b.repr x i : ℝ) := by exact_mod_cast hx i
  calc (b.repr x i : ℝ) * σ (b i) ≤ (b.repr x i : ℝ) * (R * τ (b i)) := mul_le_mul_of_nonneg_left (hle i σ τ) hc.le
    _ = R * ((b.repr x i : ℝ) * τ (b i)) := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
