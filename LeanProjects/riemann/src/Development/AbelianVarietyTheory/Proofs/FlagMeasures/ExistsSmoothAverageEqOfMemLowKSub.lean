import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOnGExistsContDiffCompactSupportExtension

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory

noncomputable def leftMulEntries {n : ℕ} (a : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (Fin n → Fin n → ℂ) ≃L[ℂ] (Fin n → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x i j => ((a : Matrix (Fin n) (Fin n) ℂ) * Matrix.of x) i j
      invFun := fun x i j => (((a⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.of x) i j
      map_add' := fun x y => by
        have h := Matrix.mul_add (a : Matrix (Fin n) (Fin n) ℂ) (Matrix.of x) (Matrix.of y)
        exact h
      map_smul' := fun c x => by
        have h := Matrix.mul_smul (a : Matrix (Fin n) (Fin n) ℂ) c (Matrix.of x)
        exact h
      left_inv := fun x => by
        have h := Units.inv_mul_cancel_left a (Matrix.of x)
        exact h
      right_inv := fun x => by
        have h := Units.mul_inv_cancel_left a (Matrix.of x)
        exact h }

private lemma inUJ_of_mem_Kset' {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) : Formalism.REAL.inUJ ε g := by
  have hu : star g * g = 1 := Unitary.star_mul_self_of_mem hg.1
  unfold Formalism.REAL.inUJ
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, hu, Matrix.one_mul]

private lemma mul_mem_Kset {n : ℕ} {ε : Fin n → Bool} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) (hg' : g' ∈ Formalism.REAL.Kset ε) : g * g' ∈ Formalism.REAL.Kset ε := by
  refine ⟨Submonoid.mul_mem _ hg.1 hg'.1, ?_⟩
  rw [Matrix.mul_assoc, hg'.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]

private lemma exists_UJ_umat_eq_of_mem_Kset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) : ∃ k : Formalism.REAL.UJ ε, umat k = g :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩,
    inUJ_of_mem_Kset' hg⟩, rfl⟩

theorem exists_smooth_average_eq_of_mem_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (w : H), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → w ∈ lowKSub ε lam σ → w ≠ 0 → ∀ u ∈ lowKSub ε lam σ, ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g : UJ ε, F (fun i j => umat g i j) • σ (umat g) w ∂(muG ε) := by
  intro n ε H _ _ _ σ lam w hrep hK hw hw0 u hu
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have humat : Continuous fun g : Formalism.REAL.UJ ε => umat g :=
    Units.continuous_val.comp continuous_subtype_val
  have hcont : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w :=
    (hrep.2.2 w).comp_continuous humat hmem
  have he : Continuous fun g : Formalism.REAL.UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ) := humat

  have hint : ∀ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
      HasCompactSupport (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j)) →
      Integrable (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j) • σ (umat g) w) (muG ε) := by
    intro F hFd _ hFg
    have hc : Continuous fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j) := hFd.continuous.comp he
    exact (hc.smul hcont).integrable_of_hasCompactSupport
      (hFg.smul_right (f' := fun g : Formalism.REAL.UJ ε => σ (umat g) w))

  obtain ⟨α, hαs, hαc, hαfix⟩ := exists_smooth_fix_lowKSub n ε lam H σ hrep hK
  obtain ⟨F0, hF0d, hF0c, hF0e⟩ :=
    smoothOnG_exists_contDiff_compactSupport_extension n ε α hαs hαc
  have hF0g : HasCompactSupport (fun g : Formalism.REAL.UJ ε => F0 (fun i j => umat g i j)) := by
    have hfun : (fun g : Formalism.REAL.UJ ε => F0 (fun i j => umat g i j)) = fun g => α (umat g) :=
      funext fun g => (hF0e g).symm
    rw [hfun]
    exact hαc
  have hbase : ∫ g, F0 (fun i j => umat g i j) • σ (umat g) w ∂(muG ε) = w := by
    refine ext_inner_left ℂ fun v => ?_
    rw [← integral_inner (hint F0 hF0d hF0c hF0g) v]
    simp_rw [inner_smul_right, ← hF0e]
    exact hαfix w hw v

  let T : Submodule ℂ H :=
    { carrier := {v | ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
          HasCompactSupport (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j)) ∧
          v = ∫ g, F (fun i j => umat g i j) • σ (umat g) w ∂(muG ε)}
      add_mem' := by
        rintro _ _ ⟨F1, h1d, h1c, h1g, rfl⟩ ⟨F2, h2d, h2c, h2g, rfl⟩
        refine ⟨fun y => F1 y + F2 y, h1d.add h2d, h1c.add h2c, h1g.add h2g, ?_⟩
        rw [← integral_add (hint F1 h1d h1c h1g) (hint F2 h2d h2c h2g)]
        simp only [add_smul]
      zero_mem' := by
        refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, HasCompactSupport.zero, ?_⟩
        simp
      smul_mem' := by
        rintro c _ ⟨F1, h1d, h1c, h1g, rfl⟩
        refine ⟨fun y => c * F1 y, contDiff_const.mul h1d, h1c.mul_left, h1g.mul_left, ?_⟩
        rw [← integral_smul]
        simp only [mul_smul] }

  have hgen : ∀ g ∈ Formalism.REAL.Kset ε, σ g w ∈ T := by
    intro g hg
    obtain ⟨k, rfl⟩ := exists_UJ_umat_eq_of_mem_Kset hg
    let a : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((k⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    have hshift : ∀ x : Formalism.REAL.UJ ε,
        leftMulEntries a (fun i j => umat x i j) = fun i j => umat (k⁻¹ * x) i j := fun x => rfl
    refine ⟨fun y => F0 (leftMulEntries a y), ?_, ?_, ?_, ?_⟩
    · exact hF0d.comp ((leftMulEntries a).contDiff.restrict_scalars ℝ)
    · exact hF0c.comp_homeomorph (leftMulEntries a).toHomeomorph
    · simp only [hshift]
      exact hF0g.comp_homeomorph (Homeomorph.mulLeft k⁻¹)
    · simp only [hshift]
      have hinv := integral_mul_left_eq_self (μ := muG ε)
        (fun x : Formalism.REAL.UJ ε => F0 (fun i j => umat (k⁻¹ * x) i j) • σ (umat x) w) k
      simp only [inv_mul_cancel_left] at hinv
      rw [← hinv]
      have hmul : ∀ x : Formalism.REAL.UJ ε, F0 (fun i j => umat x i j) • σ (umat (k * x)) w
          = σ (umat k) (F0 (fun i j => umat x i j) • σ (umat x) w) := by
        intro x
        rw [map_smul]
        congr 1
        show σ (umat k * umat x) w = σ (umat k) (σ (umat x) w)
        rw [hrep.1.2 _ (hmem k) _ (hmem x)]
        rfl
      simp_rw [hmul]
      rw [ContinuousLinearMap.integral_comp_comm _ (hint F0 hF0d hF0c hF0g), hbase]

  let S' : Submodule ℂ H := Submodule.span ℂ {v | ∃ g ∈ Formalism.REAL.Kset ε, v = σ g w}
  have hS'le : S' ≤ lowKSub ε lam σ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hK.2.1 g hg w hw
  have hS'st : IsKStableOn ε σ S' := by
    intro g hg v hv
    have hle : S' ≤ S'.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g', hg', rfl⟩
      show σ g (σ g' w) ∈ S'
      refine Submodule.subset_span ⟨g * g', mul_mem_Kset hg hg', ?_⟩
      rw [hrep.1.2 g (inUJ_of_mem_Kset' hg) g' (inUJ_of_mem_Kset' hg')]
      rfl
    exact hle hv
  have h1K : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
    ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
  have hwS' : w ∈ S' := Submodule.subset_span ⟨1, h1K, by rw [hrep.1.1]; rfl⟩
  have hS'eq : S' = lowKSub ε lam σ := by
    rcases hK.2.2.1 S' hS'le hS'st with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hwS')) hw0
    · exact h
  have huS' : u ∈ S' := by rw [hS'eq]; exact hu
  have huT : u ∈ T := Submodule.span_le.2 (by rintro _ ⟨g, hg, rfl⟩; exact hgen g hg) huS'
  obtain ⟨F, hFd, hFc, _, hFu⟩ := huT
  exact ⟨F, hFd, hFc, hFu⟩

end GlobalTheory
