import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem exists_forall_algHom_pi_eq_apply_of_finite {K P : Type} [Field K] [Finite P] (ψ : (P → K) →ₐ[K] K) :
    ∃ p, ∀ x, ψ x = x p := by
  classical
  have hex : ∃ p, ψ (Pi.single p 1) ≠ 0 := by
    by_contra h
    push_neg at h
    have := Fintype.ofFinite P
    have h1 : (1 : P → K) = ∑ p, Pi.single p 1 := by
      simpa using (Finset.univ_sum_single (1 : P → K)).symm
    have h2 : ψ 1 = 0 := by
      rw [h1, map_sum]
      simp [h]
    simp at h2
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, fun x => ?_⟩
  have hid : ψ (Pi.single p 1) = 1 := by
    have h2 : ψ (Pi.single p 1) * ψ (Pi.single p 1) = ψ (Pi.single p 1) := by
      rw [← map_mul]
      congr 1
      ext i
      by_cases h : i = p <;> simp [Pi.single_apply, h]
    exact (mul_left_inj' hp).1 (h2.trans (one_mul _).symm)
  have hx : x * Pi.single p 1 = algebraMap K (P → K) (x p) * Pi.single p 1 := by
    ext i
    by_cases h : i = p <;> simp [Pi.single_apply, h]
  have h3 := congrArg ψ hx
  rw [map_mul, map_mul, AlgHom.commutes, hid] at h3
  simpa using h3

theorem UpperTheory.Gal.crystallineComparison.splitsField_of :
    SplitsField := by
  intro R S K _ _ _ _ _ _ hE
  classical
  have hfin : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  haveI : IsArtinianRing (K ⊗[R] S) := isArtinian_of_tower K inferInstance
  haveI : Finite (PrimeSpectrum (K ⊗[R] S)) := inferInstance
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[R] S)
  let F := splitMap (R := R) (S := S) (B := K) (I := S →ₐ[R] K) (fun z => z)
  let L : (S →ₐ[R] K) → ((K ⊗[R] S) →ₐ[K] K) := fun ψ => (Pi.evalAlgHom K (fun _ => K) ψ).comp F
  have hL : ∀ ψ x, L ψ x = F x ψ := fun _ _ => rfl
  have hLs : ∀ ψ (s : S), L ψ (1 ⊗ₜ s) = ψ s := by
    intro ψ s
    simp [L, F, splitMap]
  choose q hq using fun ψ => exists_forall_algHom_pi_eq_apply_of_finite ((L ψ).comp e.symm.toAlgHom)
  have hLe : ∀ ψ x, L ψ x = e x (q ψ) := by
    intro ψ x
    simpa using hq ψ (e x)
  have qinj : Function.Injective q := by
    intro ψ1 ψ2 h
    ext s
    rw [← hLs, ← hLs, hLe, hLe, h]
  have hsec : ∀ p, ∃ ψ, q ψ = p := by
    intro p
    let g : (K ⊗[R] S) →ₐ[K] K := (Pi.evalAlgHom K (fun _ => K) p).comp e.toAlgHom
    let ψ : S →ₐ[R] K := (g.restrictScalars R).comp Algebra.TensorProduct.includeRight
    have hg : L ψ = g := by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · ext s
        simp [hLs, ψ]
    refine ⟨ψ, ?_⟩
    have h1 := hLe ψ (e.symm (Pi.single p 1))
    rw [hg] at h1
    simp only [g, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
      AlgEquiv.apply_symm_apply, Pi.evalAlgHom_apply] at h1
    by_contra hne
    simp [Pi.single_apply, hne] at h1
  refine ⟨Finite.of_injective q qinj, ?_⟩
  show Function.Bijective F
  constructor
  · intro x y h
    apply e.injective
    funext p
    obtain ⟨ψ, rfl⟩ := hsec p
    rw [← hLe, ← hLe, hL, hL, h]
  · intro v
    refine ⟨e.symm (Function.extend q v 0), ?_⟩
    funext ψ
    rw [← hL, hLe, e.apply_symm_apply, qinj.extend_apply]
