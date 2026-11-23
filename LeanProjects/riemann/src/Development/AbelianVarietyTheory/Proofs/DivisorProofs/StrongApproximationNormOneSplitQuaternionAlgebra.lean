import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionSplitOfIsotropicNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSL2AdelesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.Split

variable {F : Type} [Field F] [NumberField F] {a b : F}

def qi : ℍ[F, a, b] := ⟨0, 1, 0, 0⟩

def qj : ℍ[F, a, b] := ⟨0, 0, 1, 0⟩

def qk : ℍ[F, a, b] := ⟨0, 0, 0, 1⟩

theorem decomp (y : ℍ[F, a, b]) : y = y.re • (1 : ℍ[F, a, b]) + y.imI • qi + y.imJ • qj + y.imK • qk := by
  ext <;> simp [qi, qj, qk]

theorem map_smul_F (c : F) (M : Matrix (Fin 2) (Fin 2) F) :
    (c • M).map (algebraMap F (AF F)) = algebraMap F (AF F) c • M.map (algebraMap F (AF F)) := by
  ext i j; simp

theorem map_smul_one (c : F) :
    (c • (1 : Matrix (Fin 2) (Fin 2) F)).map (algebraMap F (AF F)) = algebraMap F (AF F) c • 1 := by
  rw [map_smul_F, Matrix.map_one _ (map_zero _) (map_one _)]

variable (φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F)

def bcBasis : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) (AF F)) (algebraMap F (AF F) a) 0
    (algebraMap F (AF F) b) where
  i := (φ qi).map (algebraMap F (AF F))
  j := (φ qj).map (algebraMap F (AF F))
  k := (φ qk).map (algebraMap F (AF F))
  i_mul_i := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qi : ℍ[F, a, b]) * qi = a • 1 := by ext <;> simp [qi]
    rw [this, map_smul, map_one, map_smul_one, zero_smul, add_zero]
  j_mul_j := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qj : ℍ[F, a, b]) * qj = b • 1 := by ext <;> simp [qj]
    rw [this, map_smul, map_one, map_smul_one]
  i_mul_j := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qi : ℍ[F, a, b]) * qj = qk := by ext <;> simp [qi, qj, qk]
    rw [this]
  j_mul_i := by
    rw [← Matrix.map_mul, ← map_mul, zero_smul, zero_sub]
    have : (qj : ℍ[F, a, b]) * qi = -qk := by ext <;> simp [qi, qj, qk]
    rw [this, map_neg, Matrix.map_neg _ (map_neg _)]

def Φ : DA F a b →ₐ[AF F] Matrix (Fin 2) (Fin 2) (AF F) := (bcBasis φ).liftHom

theorem Φ_apply (x : DA F a b) : Φ φ x = x.re • (1 : Matrix (Fin 2) (Fin 2) (AF F))
    + x.imI • (φ qi).map (algebraMap F (AF F)) + x.imJ • (φ qj).map (algebraMap F (AF F))
    + x.imK • (φ qk).map (algebraMap F (AF F)) := by
  simp [Φ, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift, bcBasis, Algebra.algebraMap_eq_smul_one]

def Ψ (m : Matrix (Fin 2) (Fin 2) (AF F)) : DA F a b :=
  ∑ i, ∑ j, m i j • rat (φ.symm (Matrix.single i j 1))

theorem rat_add (x y : ℍ[F, a, b]) : rat (x + y) = rat x + rat y := by ext <;> simp [rat]

theorem rat_smul (c : F) (x : ℍ[F, a, b]) : rat (c • x) = algebraMap F (AF F) c • rat x := by
  ext <;> simp [rat] <;> rw [Algebra.smul_def]

theorem rat_sum {ι : Type} (s : Finset ι) (f : ι → ℍ[F, a, b]) : rat (∑ i ∈ s, f i) = ∑ i ∈ s, rat (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext <;> simp [rat]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, rat_add, ih]

theorem rat_one : rat (1 : ℍ[F, a, b]) = 1 := by ext <;> simp [rat]

theorem Ψ_add (m n : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m + n) = Ψ φ m + Ψ φ n := by
  simp only [Ψ, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem Ψ_smul (c : AF F) (m : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (c • m) = c • Ψ φ m := by
  simp only [Ψ, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem Ψ_map (M : Matrix (Fin 2) (Fin 2) F) : Ψ φ (M.map (algebraMap F (AF F))) = rat (φ.symm M) := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [Ψ, Matrix.map_apply, map_sum, rat_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : F) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
    map_smul, rat_smul]

theorem Ψ_one : Ψ φ 1 = 1 := by
  rw [← Matrix.map_one (algebraMap F (AF F)) (map_zero _) (map_one _), Ψ_map, map_one, rat_one]

theorem Φ_rat (y : ℍ[F, a, b]) : Φ φ (rat y) = (φ y).map (algebraMap F (AF F)) := by
  conv_rhs => rw [decomp y]
  simp only [Φ_apply, map_add, map_smul, map_one, Matrix.map_add, map_smul_F, Matrix.map_one _ (map_zero _) (map_one (algebraMap F (AF F)))]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul, map_add, map_mul, rat]
  split_ifs <;> simp

theorem Φ_Ψ (m : Matrix (Fin 2) (Fin 2) (AF F)) : Φ φ (Ψ φ m) = m := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single m]
  simp only [Ψ, map_sum, map_smul, Φ_rat, AlgEquiv.apply_symm_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ext k l; simp [Matrix.single_apply]

theorem Ψ_Φ (x : DA F a b) : Ψ φ (Φ φ x) = x := by
  rw [Φ_apply, Ψ_add, Ψ_add, Ψ_add, Ψ_smul, Ψ_smul, Ψ_smul, Ψ_smul, Ψ_one, Ψ_map, Ψ_map, Ψ_map]
  simp only [AlgEquiv.symm_apply_apply]
  ext <;> simp [rat, qi, qj, qk]

theorem Ψ_mul (m n : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m * n) = Ψ φ m * Ψ φ n := by
  conv_lhs => rw [← Φ_Ψ φ m, ← Φ_Ψ φ n, ← map_mul, Ψ_Φ]

theorem det_four {R : Type} [CommRing R] (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) R) (x₀ x₁ x₂ x₃ : R) :
    (x₀ • A₀ + x₁ • A₁ + x₂ • A₂ + x₃ • A₃).det = x₀ ^ 2 * A₀.det + x₁ ^ 2 * A₁.det + x₂ ^ 2 * A₂.det
      + x₃ ^ 2 * A₃.det + x₀ * x₁ * ((A₀ + A₁).det - A₀.det - A₁.det) + x₀ * x₂ * ((A₀ + A₂).det - A₀.det - A₂.det)
      + x₀ * x₃ * ((A₀ + A₃).det - A₀.det - A₃.det) + x₁ * x₂ * ((A₁ + A₂).det - A₁.det - A₂.det)
      + x₁ * x₃ * ((A₁ + A₃).det - A₁.det - A₃.det) + x₂ * x₃ * ((A₂ + A₃).det - A₂.det - A₃.det) := by
  simp [Matrix.det_fin_two]; ring

theorem det_Φ (hφ : ∀ x, (φ x).det = nrm x) (x : DA F a b) : (Φ φ x).det = nrm x := by
  have hd : ∀ y : ℍ[F, a, b], ((φ y).map (algebraMap F (AF F))).det = algebraMap F (AF F) (nrm y) := by
    intro y; rw [← hφ y, RingHom.map_det]; rfl
  have hd2 : ∀ y z : ℍ[F, a, b], ((φ y).map (algebraMap F (AF F)) + (φ z).map (algebraMap F (AF F))).det
      = algebraMap F (AF F) (nrm (y + z)) := by
    intro y z; rw [← Matrix.map_add _ (map_add _), ← map_add]; exact hd _
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (AF F)) = (φ 1).map (algebraMap F (AF F)) := by
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Φ_apply, h1, det_four]
  simp only [hd2, hd]
  simp [nrm, qi, qj, qk]
  ring

theorem nrm_Ψ (hφ : ∀ x, (φ x).det = nrm x) (m : Matrix (Fin 2) (Fin 2) (AF F)) : nrm (Ψ φ m) = m.det := by
  rw [← det_Φ φ hφ, Φ_Ψ]

theorem Ψ_cont : Continuous (Ψ φ) := by
  have hc : ∀ x : DA F a b, coords x = QuaternionAlgebra.linearEquivTuple _ _ _ x := fun x => by
    ext k; fin_cases k <;> rfl
  apply continuous_induced_rng.2
  have : (coords ∘ Ψ φ : Matrix (Fin 2) (Fin 2) (AF F) → Fin 4 → AF F) =
      fun m => ∑ i, ∑ j, m i j • coords (rat (φ.symm (Matrix.single i j 1)) : DA F a b) := by
    funext m; simp only [Function.comp, Ψ, hc, map_sum, map_smul]
  rw [this]
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (continuous_id.matrix_elem i j).smul continuous_const

theorem Ψ_sub_one (m : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m - 1) = Ψ φ m - 1 := by
  rw [sub_eq_add_neg, Ψ_add, show -(1 : Matrix (Fin 2) (Fin 2) (AF F)) = (-1 : AF F) • 1 by simp, Ψ_smul, Ψ_one]
  simp [sub_eq_add_neg]

end GlobalTheory.QSA.Split

open GlobalTheory.QSA.Split in

theorem GlobalTheory.QSA.strongApprox_split : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb hiso S₁ S₂ ε hε hS g hg
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.quaternion_split_of_isotropic_norm F a b ha hb hiso
  have hdet : (Φ φ g).det = 1 := by rw [det_Φ φ hφ, hg]
  have hcl := GlobalTheory.T.strong_approximation_SL2_adeles F S₁ S₂ ε hε hS (Φ φ g) hdet
  rw [← Ψ_Φ φ g]
  refine map_mem_closure (Ψ_cont φ) hcl ?_
  rintro _ ⟨γ, hγ, h, hh, hεh, rfl⟩
  refine ⟨φ.symm γ, ?_, Ψ φ h, ?_, ?_, ?_⟩
  · rw [← hφ, AlgEquiv.apply_symm_apply, hγ]
  · rw [nrm_Ψ φ hφ, hh]
  · rw [← Ψ_sub_one, ← Ψ_smul, hεh]
  · rw [Ψ_mul, Ψ_map]
