import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.UnipZero

theorem mem_unipRad_of_eq_one {R : Type} [CommRing R] {c N : ℕ} {n : Fin c → ℕ}
    {e : (Σ i, Fin (n i)) ≃ Fin N} {p q : Fin N} (hpq : blk e p < blk e q) (u : GL (Fin N) R)
    (hu : ∀ i j, ¬ (i = p ∧ j = q) → (u : Matrix (Fin N) (Fin N) R) i j = (1 : Matrix (Fin N) (Fin N) R) i j) :
    u ∈ unipRad R e := by
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : ¬ (i = p ∧ j = q) := by
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hij hpq
    rw [hu i j hne, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hij
  · have hne : ¬ (e ⟨a, i⟩ = p ∧ e ⟨a, j⟩ = q) := by
      rintro ⟨h1, h2⟩
      have h1' : blk e p = a := by rw [← h1, blk_apply]
      have h2' : blk e q = a := by rw [← h2, blk_apply]
      rw [h1', h2'] at hpq
      exact lt_irrefl _ hpq
    rw [hu _ _ hne]
    simp [Matrix.one_apply, e.injective.eq_iff]

end GlobalTheory.UnipZero

namespace GlobalTheory.UnipZero

theorem lieD_single_leviEmb_eq_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (e : (Σ i, Fin (n i)) ≃ Fin N) (ψ : Sm E N)
    (hψ : ∀ u ∈ unipRad (Ad E) e, ∀ g, ψ.1 (u * g) = ψ.1 g) (p q : Fin N) (hpq : blk e p < blk e q)
    (x : Cinf E) (m : ∀ i, GA E (n i)) :
    (lie E N (toL (Matrix.single p q x)) ψ).1 (leviEmb (Ad E) e m) = 0 := by
  set S : Matrix (Fin N) (Fin N) (Cinf E) := Matrix.single p q x with hS
  have hpq' : p ≠ q := by rintro rfl; exact lt_irrefl _ hpq
  have hSS : S * S = 0 := by rw [hS]; simp [hpq'.symm]
  let cc : ℝ → GL (Fin N) (Cinf E) := fun t =>
    ⟨1 + t • S, 1 - t • S, by
      rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_smul_comm, hSS, smul_zero]; abel, by
      rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hSS, smul_zero]; abel⟩
  have h0 : cc 0 = 1 := Units.ext (by simp [cc])
  have hc : HasDerivAt (fun t => toL (cc t).val) (toL S) 0 := by
    have h : HasDerivAt (fun t : ℝ => toL (1 : Matrix (Fin N) (Fin N) (Cinf E)) + t • toL S) ((1 : ℝ) • toL S) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const (toL S)).const_add _
    rw [one_smul] at h
    exact h
  set g := leviEmb (Ad E) e m
  have hmem : ∀ t, infGL E N (cc t) ∈ unipRad (Ad E) e := by
    intro t
    refine mem_unipRad_of_eq_one hpq _ fun i j hij => ?_
    have hij' : ((cc t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) i j =
        (1 : Matrix (Fin N) (Fin N) (Cinf E)) i j := by
      change ((1 : Matrix (Fin N) (Fin N) (Cinf E)) + t • S) i j = _
      have h1 : S i j = 0 := by
        rw [hS, Matrix.single_apply_of_ne]
        exact fun h => hij ⟨h.1.symm, h.2.symm⟩
      rw [Matrix.add_apply, Matrix.smul_apply, h1, smul_zero, add_zero]
    change (1 : Matrix (Fin N) (Fin N) (Ad E)) i j - sInf E ((1 : Matrix (Fin N) (Fin N) (Cinf E)) i j) +
      sInf E (((cc t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) i j) = _
    rw [hij', sub_add_cancel]
  have hconst : (fun t => ψ.1 (g * infGL E N (cc t))) = fun _ => ψ.1 g := by
    funext t
    have hconj : g * infGL E N (cc t) * g⁻¹ ∈ unipRad (Ad E) e :=
      (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer (Ad E) e m) _).1 (hmem t)
    have := hψ _ hconj g
    rwa [inv_mul_cancel_right] at this
  have hd := hasDerivAt_curve ψ g cc (toL S) h0 hc
  rw [hconst] at hd
  rw [lie_apply]
  exact hd.unique (hasDerivAt_const _ _)

end GlobalTheory.UnipZero
