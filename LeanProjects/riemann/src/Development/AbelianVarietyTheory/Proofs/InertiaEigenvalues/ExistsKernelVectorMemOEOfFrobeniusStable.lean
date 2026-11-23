import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantMemReductionOfFrobeniusEquationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EchelonProjectorKernelFrobeniusStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.KernelDescent

theorem shape_mul {T : Type*} [CommRing T] {d : ℕ} (I : Finset (Fin d)) (P P' : Matrix (Fin d) (Fin d) T)
    (hP : ∀ i, ∀ j ∉ I, P i j = 0) (hP' : ∀ i ∈ I, ∀ j, P' i j = if i = j then 1 else 0) : P * P' = P := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · by_cases hj : j ∈ I
    · rw [hP' j hj j, if_pos rfl, mul_one]
    · rw [hP i j hj, zero_mul]
  · intro k _ hk
    by_cases hkI : k ∈ I
    · rw [hP' k hkI j, if_neg hk, mul_zero]
    · rw [hP i k hkI, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem mul_eq_of_ker {C : Type*} [CommRing C] {d : ℕ} (Y Q M : Matrix (Fin d) (Fin d) C)
    (hQ : ∀ v, Y.mulVec v = 0 → Q.mulVec v = v) (hM : Y * M = 0) : Q * M = M := by
  ext i j
  have h := hQ (fun k => M k j) (by
    funext a
    have := congrFun (congrFun hM a) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
  have := congrFun h i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem shape_map {C T : Type*} [CommRing C] [CommRing T] {d : ℕ} (I : Finset (Fin d))
    (Q : Matrix (Fin d) (Fin d) C) (h₁ : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0)
    (h₂ : ∀ i, ∀ j ∉ I, Q i j = 0) (f g : C →+* T) : Q.map f * Q.map g = Q.map f := by
  refine shape_mul I _ _ (fun i j hj => ?_) (fun i hi j => ?_)
  · rw [Matrix.map_apply, h₂ i j hj, map_zero]
  · rw [Matrix.map_apply, h₁ i hi j]
    split_ifs
    · exact map_one g
    · exact map_zero g

theorem two_copies {l : ℕ} [Fact l.Prime] {C : Type} [Field C] [CharP C l] {d : ℕ} (I : Finset (Fin d))
    (A Q Λ : Matrix (Fin d) (Fin d) C) (h₁ : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0)
    (h₂ : ∀ i, ∀ j ∉ I, Q i j = 0) (hΛ : Q = A * Q.map (frobenius C l) * Λ)
    (hQA : Q * (A * Q.map (frobenius C l)) = A * Q.map (frobenius C l))
    (T : Type) [CommRing T] (i₁ i₂ : C →+* T) (hA : A.map i₁ = A.map i₂) :
    ∃ c : Fin d × Fin d → Fin d × Fin d → T, ∀ j : Fin d × Fin d,
      i₁ (Q j.1 j.2) - i₂ (Q j.1 j.2) = ∑ i : Fin d × Fin d, (i₁ (Q i.1 i.2) - i₂ (Q i.1 i.2)) ^ l * c i j := by
  rcases subsingleton_or_nontrivial T with hT | hT
  · exact ⟨0, fun _ => Subsingleton.elim _ _⟩
  haveI : CharP T l := charP_of_injective_ringHom i₁.injective l
  have e1 : Q.map i₂ * Q.map i₁ = Q.map i₂ := shape_map I Q h₁ h₂ i₂ i₁
  have e2 : Q.map i₁ = A.map i₂ * (Q.map (frobenius C l)).map i₁ * Λ.map i₁ := by
    rw [← hA, ← Matrix.map_mul, ← Matrix.map_mul, ← hΛ]
  have e3 : Q.map i₂ * (A.map i₂ * (Q.map (frobenius C l)).map i₂) = A.map i₂ * (Q.map (frobenius C l)).map i₂ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hQA]
  have e4 : Q.map i₁ - Q.map i₂ = ((1 - Q.map i₂) * A.map i₂) *
      ((Q.map (frobenius C l)).map i₁ - (Q.map (frobenius C l)).map i₂) * Λ.map i₁ := by
    have a1 : ((1 - Q.map i₂) * A.map i₂) * (Q.map (frobenius C l)).map i₂ = 0 := by
      rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, e3, sub_self]
    rw [Matrix.mul_sub, a1, sub_zero, Matrix.mul_assoc (1 - Q.map i₂), Matrix.mul_assoc (1 - Q.map i₂), ← e2,
      Matrix.sub_mul, Matrix.one_mul, e1]
  refine ⟨fun i j => ((1 - Q.map i₂) * A.map i₂) j.1 i.1 * i₁ (Λ i.2 j.2), fun j => ?_⟩
  have := congrFun (congrFun e4 j.1) j.2
  rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply] at this
  rw [this, Matrix.mul_apply, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.sub_apply, Matrix.map_apply, frobenius_def, map_pow, sub_pow_char]
  ring

theorem invariant {C : Type} [CommRing C] {d : ℕ} (I : Finset (Fin d))
    (Y Q R : Matrix (Fin d) (Fin d) C) (h₀ : Y * Q = 0) (hQ : ∀ v, Y.mulVec v = 0 → Q.mulVec v = v)
    (h₁ : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0)
    (h₂ : ∀ i, ∀ j ∉ I, Q i j = 0) (g : C →+* C) (hR : R * Y.map g = Y) : Q.map g = Q := by
  have a1 : Y * Q.map g = 0 := by
    rw [← hR, Matrix.mul_assoc, ← Matrix.map_mul, h₀, Matrix.map_zero _ (map_zero g), Matrix.mul_zero]
  have a2 := mul_eq_of_ker Y Q _ hQ a1
  have a3 : Q * Q.map g = Q := shape_map I Q h₁ h₂ (RingHom.id C) g
  rw [← a2, a3]

end GlobalTheory.BSP.KernelDescent

namespace GlobalTheory.BSP

open KernelDescent in

theorem exists_ker_vector_mem_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y A : Matrix (Fin d) (Fin d) (Cb l)), A.det ≠ 0 → (∀ i j, A i j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) → Y.map (frobenius (Cb l) l) = Y * A → (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (Cb l), IsUnit R ∧ R * Y.map (autCb l (galTilt l (g : GQ l))) = Y) → Y.det = 0 → ∃ v : Fin d → Cb l, v ≠ 0 ∧ (∀ i, v i ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) ∧ Y.mulVec v = 0 := by
  intro l _ K bk d Y A hA hAm hY hg hdet
  obtain ⟨I, Q, Λ, h₀, hQ, h₁, h₂, hΛ⟩ := GlobalTheory.T.echelon_projector_kernel_frobenius l (Cb l) d Y A hA hY
  have hQA : Q * (A * Q.map (frobenius (Cb l) l)) = A * Q.map (frobenius (Cb l) l) := by
    refine mul_eq_of_ker Y Q _ hQ ?_
    rw [← Matrix.mul_assoc, ← hY, ← Matrix.map_mul, h₀, Matrix.map_zero _ (map_zero _)]
  have hmem := GlobalTheory.T.tilt_invariant_mem_reduction_of_frobenius_equation l K bk (Fin d × Fin d) (fun j => Q j.1 j.2) (fun g hgf j => by
    obtain ⟨R, -, hR⟩ := hg g hgf
    have := invariant I Y Q R h₀ hQ h₁ h₂ (autCb l (galTilt l (g : GQ l)) : Cb l →+* Cb l) hR
    exact congrFun (congrFun this j.1) j.2) (fun T _ i₁ i₂ h =>
      two_copies I A Q Λ h₁ h₂ hΛ hQA T i₁ i₂ (by
        ext i j
        exact h _ (hAm i j)))
  obtain ⟨v, hv, hYv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hne : ∃ j, (fun i => Q i j) ≠ 0 := by
    by_contra hc
    push Not at hc
    have : Q = 0 := by
      ext i j
      exact congrFun (hc j) i
    apply hv
    rw [← hQ v hYv, this, Matrix.zero_mulVec]
  obtain ⟨j, hj⟩ := hne
  refine ⟨fun i => Q i j, hj, fun i => hmem (i, j), ?_⟩
  funext a
  have := congrFun (congrFun h₀ a) j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

end GlobalTheory.BSP
