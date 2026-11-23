import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFunctionCharacterExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateFiniteDimMatrixCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMatrixCoefficientsMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentTwistCharacterContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentPolynomialInLogStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

namespace GlobalTheory.AbExp

theorem coeff_mem_of_isNilpotent (G : Type) [CommGroup G] [TopologicalSpace G] (H : Set G) (L : G → ℂ)
    (hA : (∀ φ : G → ℂ, Continuous φ → (∀ s t, φ (s * t) = φ s + φ t) → (∀ γ ∈ H, φ γ = 0) → ∃ A : ℂ, ∀ t, φ t = A * L t)) (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (χ : G → ℂ)
    (hn : ∀ s, IsNilpotent (ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ))) (hH : ∀ γ ∈ H, ρ γ = 1)
    (hc : ∀ i j, Continuous fun s => ρ s i j) (i j : Fin d) :
    (fun s => ρ s i j) ∈ Submodule.span ℂ (Set.range fun p : (G →* ℂˣ) × ℕ => fun s : G => ((p.1 s : ℂˣ) : ℂ) * L s ^ p.2) := by
  obtain ⟨lam, hlam, hlamc, hlamH⟩ := GlobalTheory.T.nilpotent_twist_character_continuous G H d ρ χ (Fin.pos i) hn hH hc
  let u : G →* Matrix (Fin d) (Fin d) ℂ :=
    { toFun := fun s => (((lam s)⁻¹ : ℂˣ) : ℂ) • ρ s
      map_one' := by simp
      map_mul' := fun s t => by
        rw [map_mul, map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm, mul_comm (((lam s)⁻¹ : ℂˣ) : ℂ)] }
  have hu : ∀ s, u s = (((lam s)⁻¹ : ℂˣ) : ℂ) • ρ s := fun s => rfl
  have hun : ∀ s, IsNilpotent (u s - 1) := by
    intro s
    have : u s - 1 = (((lam s)⁻¹ : ℂˣ) : ℂ) • (ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
      rw [hu, smul_sub, smul_smul, ← hlam s, Units.inv_mul, one_smul]
    rw [this]; exact (hn s).smul _
  have huH : ∀ γ ∈ H, u γ = 1 := by
    intro γ hγ; rw [hu, hlamH γ hγ, hH γ hγ]; simp
  have hinvc : Continuous fun s => (((lam s)⁻¹ : ℂˣ) : ℂ) := by
    have : (fun s => (((lam s)⁻¹ : ℂˣ) : ℂ)) = fun s => ((lam s : ℂˣ) : ℂ)⁻¹ := by
      funext s; simp
    rw [this]; exact hlamc.inv₀ fun s => Units.ne_zero _
  have huc : ∀ i j, Continuous fun s => u s i j := by
    intro i j; simp only [hu, Matrix.smul_apply, smul_eq_mul]; exact hinvc.mul (hc i j)
  obtain ⟨K, M, hM⟩ := GlobalTheory.T.unipotent_polynomial_in_log G H L hA d u hun huH huc
  have hρ : (fun s => ρ s i j) = ∑ k ∈ Finset.range K, M k i j • fun s => ((lam s : ℂˣ) : ℂ) * L s ^ k := by
    funext s
    have h1 : ρ s = ((lam s : ℂˣ) : ℂ) • u s := by rw [hu, smul_smul, Units.mul_inv, one_smul]
    rw [h1, hM s]
    simp [Matrix.sum_apply, Finset.mul_sum, Finset.sum_apply, mul_comm, mul_left_comm]
    try exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hρ]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(lam, k), rfl⟩)

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ φ : (AE F E)ˣ → ℂ, Continuous φ → (∀ s t, φ (s * t) = φ s + φ t) → (∀ γ : Eˣ, φ (Units.map (inclR (F := F) (AF F)).toMonoidHom γ) = 0) → ∃ A : ℂ, ∀ t, φ t = A * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ)) → ∀ (Fn : (AE F E)ˣ → ℂ), Continuous Fn → (∀ (γ : Eˣ) (t : (AE F E)ˣ), Fn (Units.map (inclR (F := F) (AF F)).toMonoidHom γ * t) = Fn t) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s : (AE F E)ˣ => fun t => Fn (t * s))) → ∃ (N K : ℕ) (χ : Fin N → (AE F E)ˣ →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ ∧ ∀ t : (AE F E)ˣ, Fn t = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) ^ (k : ℕ) := by
  intro F E _ _ _ _ _ hA Fn hc hinv hfin
  let H : Set (AE F E)ˣ := Set.range (Units.map (inclR (F := F) (AF F)).toMonoidHom)
  let L : (AE F E)ˣ → ℂ := fun t => ((Real.log (absE F E t : ℝ) : ℝ) : ℂ)
  have hA' : ∀ φ : (AE F E)ˣ → ℂ, Continuous φ → (∀ s t, φ (s * t) = φ s + φ t) → (∀ γ ∈ H, φ γ = 0) →
      ∃ A : ℂ, ∀ t, φ t = A * L t := fun φ h1 h2 h3 => hA φ h1 h2 fun γ => h3 _ ⟨γ, rfl⟩
  have hmul : ∀ s : (AE F E)ˣ, Continuous fun t : (AE F E)ˣ => t * s := by
    haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    intro s; exact continuous_id.mul continuous_const
  obtain ⟨d, ρ, a, hρH, hρc, hFn⟩ := GlobalTheory.T.translate_finite_dim_matrix_coefficient (AE F E)ˣ H Fn hmul hc
    (by rintro _ ⟨γ, rfl⟩ t; exact hinv γ t) hfin
  have hS : ∀ i j, (fun s => ρ s i j) ∈ Submodule.span ℂ (Set.range fun p : ((AE F E)ˣ →* ℂˣ) × ℕ =>
      fun s : (AE F E)ˣ => ((p.1 s : ℂˣ) : ℂ) * L s ^ p.2) :=
    GlobalTheory.T.unipotent_matrix_coefficients_mem (AE F E)ˣ H _ (fun d ρ χ hn hH hc i j => coeff_mem_of_isNilpotent _ H L hA' d ρ χ hn hH hc i j) d ρ hρH hρc
  have hmem : Fn ∈ Submodule.span ℂ (Set.range fun p : ((AE F E)ˣ →* ℂˣ) × ℕ =>
      fun s : (AE F E)ˣ => ((p.1 s : ℂˣ) : ℂ) * L s ^ p.2) := by
    have : Fn = ∑ i, ∑ j, a i j • fun s => ρ s i j := by
      funext t; rw [hFn t]; simp [Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hS i j)
  exact GlobalTheory.T.finite_type_function_character_expansion (AE F E)ˣ L Fn hmem

end GlobalTheory.AbExp
