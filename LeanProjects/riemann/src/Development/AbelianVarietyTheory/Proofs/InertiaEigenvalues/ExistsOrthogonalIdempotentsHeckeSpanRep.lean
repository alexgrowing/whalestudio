import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepMatrixCombinationKillingCharactersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSubMemOfPowSubMemStatement

noncomputable section

namespace GlobalTheory.SpanIdem

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {Γ X A : Type} [Group Γ] [CommRing A] {n r t : ℕ}

theorem overK_apply {k : ℕ} (σ : Γ →* GL (Fin k) A) (g : Γ) (u : Fin k → FractionRing A) :
    overK σ g u = ((mat σ g).map (toFr A)).mulVec u := rfl

theorem map_smul_mulVec {k : ℕ} (c : A) (M : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((c • M).map (toFr A)).mulVec u = toFr A c • (M.map (toFr A)).mulVec u := by
  rw [← Matrix.smul_mulVec]
  congr 1
  ext i j
  simp

theorem map_sum_mulVec {k m : ℕ} (M : Fin m → Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((∑ i, M i).map (toFr A)).mulVec u = ∑ i, ((M i).map (toFr A)).mulVec u := by
  rw [← Matrix.sum_mulVec]
  congr 1
  exact map_sum (toFr A).mapMatrix M Finset.univ

theorem map_mul_mulVec {k : ℕ} (M N : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((M * N).map (toFr A)).mulVec u = (M.map (toFr A)).mulVec ((N.map (toFr A)).mulVec u) := by
  rw [Matrix.map_mul, Matrix.mulVec_mulVec]

theorem map_one_sub_mulVec {k : ℕ} (M : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((1 - M).map (toFr A)).mulVec u = u - (M.map (toFr A)).mulVec u := by
  have : (1 - M).map (toFr A) = 1 - M.map (toFr A) := by
    have h := map_sub (toFr A).mapMatrix 1 M
    rw [map_one] at h
    exact h
  rw [this, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem eq_of_mulVec {k : ℕ} {M N : Matrix (Fin k) (Fin k) A}
    (h : ∀ u, (M.map (toFr A)).mulVec u = (N.map (toFr A)).mulVec u) : M = N := by
  have h1 : M.map (toFr A) = N.map (toFr A) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, h]
  exact Matrix.map_injective (IsFractionRing.injective A (FractionRing A)) h1

theorem exists_corner (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (ρ : Γ →* GL (Fin r) A)
    (χ : ℕ → (Γ →* Aˣ)) (π : X)
    (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A)))
    (hr : 2 ≤ r) (hs : Submodule.span A (Set.range (mat ρ)) = ⊤) (hd : IsDecomp (t := t) (rep π) ρ χ e)
    (P : Matrix (Fin r) (Fin r) A) :
    ∃ a, InRing T rep a ∧
      ∀ u, e (((a π).map (toFr A)).mulVec u) = ((P.map (toFr A)).mulVec (e u).1, 0) := by
  obtain ⟨m, f, h, hP, hχ⟩ := GlobalTheory.T.exists_repMatrix_combination_killing_characters ρ χ hr hs P
  refine ⟨∑ k, f k • fun x => mat (rep x) (h k),
    inRing_sum _ fun k _ => inRing_smul _ (inRing_mat _), fun u => ?_⟩
  rw [Finset.sum_apply, map_sum_mulVec, map_sum, ← hP, map_sum_mulVec]
  have key : ∀ k, e ((((f k • fun x => mat (rep x) (h k)) π).map (toFr A)).mulVec u) =
      (((f k • mat ρ (h k)).map (toFr A)).mulVec (e u).1,
        fun c : Fin t => toFr A (f k * ((χ ((c : ℕ) + 1) (h k) : Aˣ) : A)) * (e u).2 c) := by
    intro k
    rw [Pi.smul_apply, map_smul_mulVec, map_smul, ← overK_apply, hd, map_smul_mulVec, overK_apply]
    refine Prod.ext rfl ?_
    funext c
    simp [mul_assoc]
    simp [Algebra.smul_def]
  simp only [key]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
  · rw [Prod.snd_sum]
    funext c
    rw [Finset.sum_apply]
    simp only [← Finset.sum_mul, ← map_sum, hχ, map_zero, zero_mul, Pi.zero_apply]

theorem pow_succ_eval {b : X → Matrix (Fin n) (Fin n) A} {π : X} (h : b π * b π = b π) (k : ℕ) :
    (b ^ (k + 1)) π = b π := by
  rw [Pi.pow_apply]
  exact IsIdempotentElem.pow_succ_eq k h

theorem exists_idem (l : ℕ) [Fact l.Prime] [Finite X] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A]
    (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X)
    (b : X → Matrix (Fin n) (Fin n) A) (hb : InRing T rep b) (hπ : b π * b π = b π) :
    ∃ E, InRing T rep E ∧ E * E = E ∧ E π = b π ∧ (∀ y, y * b = 0 → y * E = 0) ∧
      (∀ y, b * y = 0 → E * y = 0) := by
  haveI : Module.Finite ℤ_[l] (Matrix (Fin n) (Fin n) A) :=
    inferInstanceAs (Module.Finite ℤ_[l] (Fin n → Fin n → A))
  obtain ⟨E, hE, hM⟩ := GlobalTheory.T.exists_idempotent_sub_mem_of_pow_sub_mem' l b
  refine ⟨E, ?_, hE, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have := hM ((Subalgebra.toSubmodule (ringR T rep)).restrictScalars ℤ_[l]) 0 fun k => by
      rw [sub_zero]
      exact pow_mem ((mem_ringR T rep b).2 hb) (k + 1)
    rw [sub_zero] at this
    exact (mem_ringR T rep E).1 this
  · have := hM (LinearMap.ker (LinearMap.proj π)) b fun k => by
      rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.sub_apply, pow_succ_eval hπ, sub_self]
    rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.sub_apply] at this
    exact sub_eq_zero.1 this
  · have := hM (LinearMap.ker (LinearMap.mulLeft ℤ_[l] y)) 0 fun k => by
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, sub_zero, pow_succ', ← mul_assoc, hy, zero_mul]
    rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply, sub_zero] at this
  · have := hM (LinearMap.ker (LinearMap.mulRight ℤ_[l] y)) 0 fun k => by
      rw [LinearMap.mem_ker, LinearMap.mulRight_apply, sub_zero, pow_succ, mul_assoc, hy, mul_zero]
    rwa [LinearMap.mem_ker, LinearMap.mulRight_apply, sub_zero] at this

theorem rank_single {K : Type} [Field K] (i : Fin r) :
    (Matrix.single i i (1 : K)).rank = 1 := by
  classical
  have : Matrix.single i i (1 : K) = Matrix.diagonal (Pi.single i 1) := by
    ext a b
    simp only [Matrix.single_apply, Matrix.diagonal_apply, Pi.single_apply]
    grind
  rw [this, Matrix.rank_diagonal]
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨i, by simp⟩, ?_⟩
  rintro ⟨a, ha⟩
  apply Subtype.ext
  by_contra h
  exact ha (Pi.single_eq_of_ne h 1)

theorem exists_orthogonal_idempotents : ∀ (l : ℕ) [Fact l.Prime] {Γ X A : Type} [Group Γ] [Finite X] [CommRing A] [IsDomain A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] {n r t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (π : X) (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A))), 2 ≤ r → Submodule.span A (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ eB e1 : X → Matrix (Fin n) (Fin n) A, (InRing T rep eB ∧ InRing T rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧ e1 * eB = 0) ∧ (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧ ∃ ε : Matrix (Fin r) (Fin r) (FractionRing A), ε.rank = 1 ∧ ∀ u, e (((e1 π).map (toFr A)).mulVec u) = (ε.mulVec (e u).1, 0) := by
  intro l _ Γ X A _ _ _ _ _ _ n r t T rep ρ χ π e hr hs hd
  obtain ⟨a, ha, hact⟩ := exists_corner T rep ρ χ π e hr hs hd 1
  have hb : ∀ u, e ((((1 - a) π).map (toFr A)).mulVec u) = (0, (e u).2) := by
    intro u
    rw [Pi.sub_apply, Pi.one_apply, map_one_sub_mulVec, map_sub, hact,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact Prod.ext (by simp) (by simp)
  obtain ⟨eB, hB, hBB, hBπ, -, -⟩ := exists_idem l T rep π (1 - a) (inRing_sub inRing_one ha) (by
    apply eq_of_mulVec
    intro u
    apply e.injective
    rw [map_mul_mulVec, hb, hb])
  rw [← hBπ] at hb
  let i : Fin r := ⟨0, by omega⟩
  obtain ⟨a', ha', hact'⟩ := exists_corner T rep ρ χ π e hr hs hd (Matrix.single i i 1)
  have hε : (Matrix.single i i (1 : A)).map (toFr A) = Matrix.single i i 1 := by
    rw [Matrix.map_single, map_one]
  rw [hε] at hact'
  have hc : ∀ u, e ((((1 - eB) π).map (toFr A)).mulVec u) = ((e u).1, 0) := by
    intro u
    rw [Pi.sub_apply, Pi.one_apply, map_one_sub_mulVec, map_sub, hb]
    exact Prod.ext (by simp) (by simp)
  have hb' : ∀ u, e (((((1 - eB) * a' * (1 - eB)) π).map (toFr A)).mulVec u) =
      ((Matrix.single i i 1).mulVec (e u).1, 0) := by
    intro u
    rw [Pi.mul_apply, Pi.mul_apply, map_mul_mulVec, map_mul_mulVec, hc, hact', hc]
  have h1 := inRing_sub inRing_one hB
  obtain ⟨e1, h1R, h11, h1π, hl, hrr⟩ := exists_idem l T rep π ((1 - eB) * a' * (1 - eB))
    (inRing_mul (inRing_mul h1 ha') h1) (by
      apply eq_of_mulVec
      intro u
      apply e.injective
      rw [map_mul_mulVec, hb', hb', Matrix.mulVec_mulVec, Matrix.single_mul_single_same, one_mul])
  refine ⟨eB, e1, ⟨hB, h1R, hBB, h11, hl eB ?_, hrr eB ?_⟩, hb, Matrix.single i i 1, rank_single i, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, mul_sub eB 1 eB, mul_one, hBB, sub_self, zero_mul, zero_mul]
  · rw [mul_assoc, sub_mul 1 eB eB, one_mul, hBB, sub_self, mul_zero]
  · rw [h1π]
    exact hb'

end GlobalTheory.SpanIdem

end
