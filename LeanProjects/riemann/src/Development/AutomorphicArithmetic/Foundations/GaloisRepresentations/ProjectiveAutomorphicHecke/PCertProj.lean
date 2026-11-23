import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem wop_sub_mem {F B J : Type*} [Field F] [CommRing B] [Algebra F B] (I : Ideal B)
    (T : J → B) (θ : J → F) (h : ∀ j, T j - algebraMap F B (θ j) ∈ I) (s : List J →₀ F) :
    wop T s - algebraMap F B (wop θ s) ∈ I := by
  rw [← Ideal.Quotient.eq]
  have hT : (fun j => Ideal.Quotient.mkₐ F I (T j)) =
      fun j => ((Ideal.Quotient.mkₐ F I).comp (Algebra.ofId F B)) (θ j) := by
    funext j
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (h j)
  calc Ideal.Quotient.mk I (wop T s) = Ideal.Quotient.mkₐ F I (wop T s) := rfl
    _ = wop (fun j => Ideal.Quotient.mkₐ F I (T j)) s := map_wop _ _ _
    _ = wop (fun j => ((Ideal.Quotient.mkₐ F I).comp (Algebra.ofId F B)) (θ j)) s := by rw [hT]
    _ = ((Ideal.Quotient.mkₐ F I).comp (Algebra.ofId F B)) (wop θ s) := (map_wop _ _ _).symm
    _ = Ideal.Quotient.mk I (algebraMap F B (wop θ s)) := rfl

private theorem fix_of_cert {F B W J : Type*} [Field F] [CommRing B] [Algebra F B] [AddCommGroup W]
    [Module F W] (g : B →ₐ[F] End F W) (T' : J → B) (θ : J → F) (t : List J →₀ F)
    (h1 : wop θ t = 1) (h2 : IsIdempotentElem (wop (fun j => g (T' j)) t)) (x : W)
    (hx : ∀ j, ∃ k : ℕ, ((g (T' j) - algebraMap F (End F W) (θ j)) ^ k) x = 0) :
    wop (fun j => g (T' j)) t x = x := by
  let A : Ideal B :=
    { carrier := {b | g b x = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c b hb
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        rw [map_mul, Module.End.mul_apply, hb, map_zero] }
  have hmem : ∀ b : B, (∃ k : ℕ, ((g b) ^ k) x = 0) → b ∈ A.radical := by
    rintro b ⟨k, hk⟩
    refine ⟨k, ?_⟩
    show g (b ^ k) x = 0
    rw [map_pow]
    exact hk
  have hmem' : ∀ b ∈ A.radical, ∃ k : ℕ, ((g b) ^ k) x = 0 := by
    rintro b ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    exact hk
  have hT : ∀ j, T' j - algebraMap F B (θ j) ∈ A.radical := by
    intro j
    apply hmem
    obtain ⟨k, hk⟩ := hx j
    refine ⟨k, ?_⟩
    rw [map_sub, AlgHom.commutes]
    exact hk
  have hw := wop_sub_mem A.radical T' θ hT t
  rw [h1, map_one] at hw
  obtain ⟨k, hk⟩ := hmem' _ (A.radical.neg_mem hw)
  rw [neg_sub, map_sub, map_one, map_wop] at hk
  have hid := h2.one_sub
  cases k with
  | zero =>
    simp at hk
    simp [hk]
  | succ m =>
    rw [hid.pow_succ_eq m] at hk
    have hk2 : x - wop (fun j => g (T' j)) t x = 0 := by simpa using hk
    exact (sub_eq_zero.mp hk2).symm

end UpperTheory.Gal.CertificateRingHomMap

theorem UpperTheory.Gal.CertificateRingHomMap.pCertProj_holds :
    UpperTheory.Gal.CertificateRingHomMap.CertProj.{u} := by
  rintro F _ W _ _ J T hc θ t ⟨h1, h2, h3⟩
  constructor
  · intro x
    rw [Submodule.mem_iInf]
    intro j
    rw [Module.End.mem_maxGenEigenspace]
    obtain ⟨N, hN⟩ := h3 j
    refine ⟨N, ?_⟩
    rw [← Algebra.algebraMap_eq_smul_one, ← Module.End.mul_apply, hN, LinearMap.zero_apply]
  · intro x hx
    have hs : ∀ a ∈ Set.range T, ∀ b ∈ Set.range T, a * b = b * a := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hc i j
    letI : CommRing (Algebra.adjoin F (Set.range T)) := Algebra.adjoinCommRingOfComm F hs
    let T' : J → Algebra.adjoin F (Set.range T) := fun j => ⟨T j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
    refine fix_of_cert (Algebra.adjoin F (Set.range T)).val T' θ t h1 h2 x ?_
    intro j
    have hj := (Submodule.mem_iInf _).mp hx j
    rw [Module.End.mem_maxGenEigenspace] at hj
    obtain ⟨k, hk⟩ := hj
    exact ⟨k, by rw [Algebra.algebraMap_eq_smul_one]; exact hk⟩
