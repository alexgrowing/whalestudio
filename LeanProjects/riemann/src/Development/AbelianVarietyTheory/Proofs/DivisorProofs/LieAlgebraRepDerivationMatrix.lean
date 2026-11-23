import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

theorem commutator_add_I_smul {R : Type} [Ring R] [Algebra ℂ R] (u v u' v' : R) :
    (u + Complex.I • v) * (u' + Complex.I • v') - (u' + Complex.I • v') * (u + Complex.I • v) =
      (u * u' - u' * u) + Complex.I • (u * v' - v' * u) + Complex.I • (v * u' - u' * v) - (v * v' - v' * v) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  linear_combination (norm := module) Complex.I_mul_I • (v * v' - v' * v)

theorem re_im_smul_add_I_smul {M : Type} [AddCommGroup M] [Module ℂ M] (a b : ℝ) (u v : M) :
    (a : ℂ) • u + ((-b : ℝ) : ℂ) • v + Complex.I • ((a : ℂ) • v + (b : ℂ) • u) =
      ((a : ℂ) + b * Complex.I) • (u + Complex.I • v) := by
  simp only [smul_add, add_smul, smul_smul]
  push_cast
  linear_combination (norm := module) Complex.I_mul_I • ((-(b : ℂ)) • v)

theorem exists_complexLinear_bracket_ext : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), Aᴴ = A → IsUnit A.det → ∀ (B : Type) [Ring B] [Algebra ℂ B]
    (ρ : Matrix (Fin n) (Fin n) ℂ → B),
    (∀ X X', Xᴴ * A + A * X = 0 → X'ᴴ * A + A * X' = 0 → ρ (X + X') = ρ X + ρ X') →
    (∀ (c : ℝ) X, Xᴴ * A + A * X = 0 → ρ (c • X) = (c : ℂ) • ρ X) →
    (∀ X X', Xᴴ * A + A * X = 0 → X'ᴴ * A + A * X' = 0 → ρ (X * X' - X' * X) = ρ X * ρ X' - ρ X' * ρ X) →
    ∃ D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B, (∀ X X', D (X * X' - X' * X) = D X * D X' - D X' * D X) ∧
      ∀ X, Xᴴ * A + A * X = 0 → D X = ρ X := by
  intro n A hA hd B _ _ ρ hadd hr hbr
  let P : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun X => (1 / 2 : ℂ) • (X - adj A X)
  let Q : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun X => (-Complex.I / 2 : ℂ) • (X + adj A X)
  have hP : ∀ X, (P X)ᴴ * A + A * P X = 0 := fun X => (skew_parts hA hd X).1
  have hQ : ∀ X, (Q X)ᴴ * A + A * Q X = 0 := fun X => (skew_parts hA hd X).2.1
  have hPQ : ∀ X, X = P X + Complex.I • Q X := fun X => (skew_parts hA hd X).2.2
  have ssmul : ∀ (c : ℝ) Y, Yᴴ * A + A * Y = 0 → ((c : ℂ) • Y)ᴴ * A + A * ((c : ℂ) • Y) = 0 := by
    intro c Y h
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h,
      smul_zero]
  have sbr : ∀ Y Y', Yᴴ * A + A * Y = 0 → Y'ᴴ * A + A * Y' = 0 →
      (Y * Y' - Y' * Y)ᴴ * A + A * (Y * Y' - Y' * Y) = 0 := by
    intro Y Y' h h'
    have e : Yᴴ * A = -(A * Y) := eq_neg_of_add_eq_zero_left h
    have e' : Y'ᴴ * A = -(A * Y') := eq_neg_of_add_eq_zero_left h'
    have e1 : Y'ᴴ * Yᴴ * A = A * Y' * Y := by
      rw [Matrix.mul_assoc, e, Matrix.mul_neg, ← Matrix.mul_assoc, e', Matrix.neg_mul, neg_neg]
    have e2 : Yᴴ * Y'ᴴ * A = A * Y * Y' := by
      rw [Matrix.mul_assoc, e', Matrix.mul_neg, ← Matrix.mul_assoc, e, Matrix.neg_mul, neg_neg]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    abel
  have hr' : ∀ (c : ℝ) Y, Yᴴ * A + A * Y = 0 → ρ ((c : ℂ) • Y) = (c : ℂ) • ρ Y := fun c Y h => by
    rw [Complex.coe_smul]; exact hr c Y h
  have adj_add : ∀ X X', adj A (X + X') = adj A X + adj A X' := fun X X' => by
    simp only [adj, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  have adj_smul : ∀ (c : ℂ) X, adj A (c • X) = star c • adj A X := fun c X => by
    simp only [adj, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have Padd : ∀ X X', P (X + X') = P X + P X' := fun X X' => by
    simp only [P, adj_add]; module
  have Qadd : ∀ X X', Q (X + X') = Q X + Q X' := fun X X' => by
    simp only [Q, adj_add]; module
  have Psmul : ∀ (a b : ℝ) X, P (((a : ℂ) + b * Complex.I) • X) = (a : ℂ) • P X + ((-b : ℝ) : ℂ) • Q X := by
    intro a b X
    simp only [P, Q, adj_smul]
    ext i j
    simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
    ring
  have Qsmul : ∀ (a b : ℝ) X, Q (((a : ℂ) + b * Complex.I) • X) = (a : ℂ) • Q X + (b : ℂ) • P X := by
    intro a b X
    simp only [P, Q, adj_smul]
    ext i j
    simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
    ring_nf; simp only [Complex.I_sq]; ring
  have skew_zero : (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * A + A * 0 = 0 := by simp
  have ρ0 : ρ 0 = 0 := by
    have := hadd 0 0 skew_zero skew_zero
    rw [add_zero] at this
    simpa using this
  have hsk : ∀ Y, Yᴴ * A + A * Y = 0 → adj A Y = -Y := fun Y h => by
    rw [adj, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  have PY : ∀ Y, Yᴴ * A + A * Y = 0 → P Y = Y := fun Y h => by
    simp only [P, hsk Y h]; module
  have QY : ∀ Y, Yᴴ * A + A * Y = 0 → Q Y = 0 := fun Y h => by
    simp only [Q, hsk Y h, add_neg_cancel, smul_zero]
  let D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B :=
    { toFun := fun X => ρ (P X) + Complex.I • ρ (Q X)
      map_add' := fun X X' => by
        rw [Padd, Qadd, hadd _ _ (hP _) (hP _), hadd _ _ (hQ _) (hQ _), smul_add]
        abel
      map_smul' := fun c X => by
        obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, c = a + b * Complex.I := ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
        simp only [RingHom.id_apply]
        rw [Psmul, Qsmul, hadd _ _ (ssmul _ _ (hP _)) (ssmul _ _ (hQ _)),
          hadd _ _ (ssmul _ _ (hQ _)) (ssmul _ _ (hP _)), hr' _ _ (hP _), hr' _ _ (hQ _), hr' _ _ (hQ _),
          hr' _ _ (hP _)]
        exact re_im_smul_add_I_smul a b _ _ }
  have hD : ∀ X, D X = ρ (P X) + Complex.I • ρ (Q X) := fun X => rfl
  have hDs : ∀ Y, Yᴴ * A + A * Y = 0 → D Y = ρ Y := fun Y h => by
    rw [hD, PY Y h, QY Y h, ρ0, smul_zero, add_zero]
  have key : ∀ p q p' q', pᴴ * A + A * p = 0 → qᴴ * A + A * q = 0 → p'ᴴ * A + A * p' = 0 →
      q'ᴴ * A + A * q' = 0 →
      D ((p + Complex.I • q) * (p' + Complex.I • q') - (p' + Complex.I • q') * (p + Complex.I • q)) =
        D (p + Complex.I • q) * D (p' + Complex.I • q') - D (p' + Complex.I • q') * D (p + Complex.I • q) := by
    intro p q p' q' hp hq hp' hq'
    rw [commutator_add_I_smul, map_sub, map_add, map_add, map_smul, map_smul, hDs _ (sbr _ _ hp hp'),
      hDs _ (sbr _ _ hp hq'), hDs _ (sbr _ _ hq hp'), hDs _ (sbr _ _ hq hq'), hbr _ _ hp hp', hbr _ _ hp hq',
      hbr _ _ hq hp', hbr _ _ hq hq', map_add, map_add, map_smul, map_smul, hDs _ hp, hDs _ hq, hDs _ hp', hDs _ hq',
      commutator_add_I_smul]
  refine ⟨D, fun X X' => ?_, hDs⟩
  have := key _ _ _ _ (hP X) (hQ X) (hP X') (hQ X')
  rwa [← hPQ X, ← hPQ X'] at this

end GlobalTheory.LeviHC
