import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfNormOneInSubalgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMapSurjectiveFiniteField
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem stdForm_incl_map_eq {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (γ : GL (Fin n) F) :
    ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F').map t =
      ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
  ext i j
  show t (algebraMap F F' ((γ : Matrix (Fin n) (Fin n) F) i j)) = algebraMap F F' ((γ : Matrix (Fin n) (Fin n) F) i j)
  exact t.commutes _

theorem stdForm_adjoin_map_mem {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (γ : GL (Fin n) F) {M : Matrix (Fin n) (Fin n) F'}
    (hM : M ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')}) :
    M.map t ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
  let T : Matrix (Fin n) (Fin n) F' →+* Matrix (Fin n) (Fin n) F' := ((t : F' ≃+* F') : F' →+* F').mapMatrix
  have hT : ∀ N, T N = N.map t := fun N => rfl
  rw [← hT]
  induction hM using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [hT, stdForm_incl_map_eq]
    exact Algebra.subset_adjoin rfl
  | algebraMap r =>
    have : T (algebraMap F' (Matrix (Fin n) (Fin n) F') r) = algebraMap F' (Matrix (Fin n) (Fin n) F') (t r) := by
      rw [hT]
      ext i j
      by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

theorem stdForm_commute_iff {F' : Type} [Field F'] {n : ℕ} (x y : GL (Fin n) F') :
    Commute x y ↔ Commute (x : Matrix (Fin n) (Fin n) F') (y : Matrix (Fin n) (Fin n) F') := by
  simp only [Commute, SemiconjBy, Units.ext_iff, Units.val_mul]

theorem isNorm_exists_twistedConj_adjoin :
    ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
      (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F') (γ : GL (Fin n) F),
      IsNorm s δ γ → ∃ y : GL (Fin n) F', ((y⁻¹ * δ * galAct F F' n s y : GL (Fin n) F') :
        Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧
        nrm s (y⁻¹ * δ * galAct F F' n s y) = incl F F' n γ := by
  intro F F' _ _ _ _ s hs n δ γ hN
  obtain ⟨_, -, h3, h4, h5⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n

  have hgfix : ∀ t : F' ≃ₐ[F] F', galAct F F' n t (incl F F' n γ) = incl F F' n γ := fun t =>
    Units.ext (stdForm_incl_map_eq n t γ)

  have hC : ∀ z w : GL (Fin n) F',
      (z : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} →
      Commute w (incl F F' n γ) → Commute z w := by
    intro z w hz hw
    rw [stdForm_commute_iff] at hw ⊢
    exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hz hw).symm
  have hCt : ∀ (t : F' ≃ₐ[F] F') (w : GL (Fin n) F'), Commute w (incl F F' n γ) →
      Commute (galAct F F' n t w) (incl F F' n γ) := by
    intro t w hw
    have := hw.map (galAct F F' n t)
    rwa [hgfix t] at this

  obtain ⟨c, hc⟩ := isConj_iff.1 hN
  have hn1 : nrm s (c⁻¹ * δ * galAct F F' n s c) = incl F F' n γ := by
    rw [h3, ← hc]; group
  have hcomm1 : Commute (c⁻¹ * δ * galAct F F' n s c) (incl F F' n γ) := by
    have := h4 (c⁻¹ * δ * galAct F F' n s c)
    rw [hn1, hgfix s] at this
    exact this

  obtain ⟨δ₀, hδ₀A, hn0⟩ := GlobalTheory.T.norm_map_surjective_finite_field F F' s hs n γ
  have hδ₀g : Commute δ₀ (incl F F' n γ) := hC δ₀ _ hδ₀A (Commute.refl _)
  have hεg : Commute (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) (incl F F' n γ) :=
    (hδ₀g.inv_left).mul_left hcomm1
  have hεn : nrm s (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) = 1 := by
    have hp := h5 δ₀ (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) (fun t u =>
      hC _ _ (by rw [show ((galAct F F' n t δ₀ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
        (δ₀ : Matrix (Fin n) (Fin n) F').map t from rfl]; exact stdForm_adjoin_map_mem n t γ hδ₀A) (hCt u _ hεg))
    rw [mul_inv_cancel_left, hn1, hn0] at hp
    exact (mul_eq_left.1 hp.symm)

  have hBst : ∀ M ∈ Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')},
      M.map s ∈ Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
    intro M hM
    rw [Subalgebra.mem_centralizer_iff] at hM ⊢
    intro g' hg'
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    have e := congrArg (fun N => ((s : F' ≃+* F') : F' →+* F').mapMatrix N) (hM _ rfl)
    simp only [map_mul] at e
    rw [← stdForm_incl_map_eq n s γ]
    exact e
  have hεB : ((δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c) : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈
      Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g' hg'
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    exact ((stdForm_commute_iff _ _).1 hεg).eq.symm
  obtain ⟨x, hxB, hεx⟩ := GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n _ hBst _ hεB hεn
  have hxg : Commute x (incl F F' n γ) := by
    rw [stdForm_commute_iff]
    exact ((Subalgebra.mem_centralizer_iff F').1 hxB _ rfl).symm
  have hxδ₀ : Commute δ₀ x := hC δ₀ x hδ₀A hxg
  have e1 : c⁻¹ * δ * galAct F F' n s c = δ₀ * (x⁻¹ * galAct F F' n s x) := by
    rw [← hεx, mul_inv_cancel_left]
  have key : (c * x⁻¹)⁻¹ * δ * galAct F F' n s (c * x⁻¹) = δ₀ := by
    rw [map_mul, map_inv]
    calc (c * x⁻¹)⁻¹ * δ * (galAct F F' n s c * (galAct F F' n s x)⁻¹)
        = x * (c⁻¹ * δ * galAct F F' n s c) * (galAct F F' n s x)⁻¹ := by group
      _ = x * δ₀ * x⁻¹ := by rw [e1]; group
      _ = δ₀ := by rw [← hxδ₀.eq]; group
  exact ⟨c * x⁻¹, by rw [key]; exact hδ₀A, by rw [key]; exact hn0⟩

end GlobalTheory.Shin
