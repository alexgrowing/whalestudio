import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem dense_ker_of_bounded {A R C Q : Type} [CommRing A] [CommRing R] [CommRing C] [CommRing Q]
    (p : ℕ) (α : A →+* R) (i : R →+* C) (f : C →+* Q) (N : ℕ)
    (hd : ∀ (x : C) (r : ℕ), ∃ (s : R) (z : C), x = i s + (p : C) ^ r * z)
    (hb : ∀ x : C, ∃ a : A, (p : Q) ^ N * f x = f (i (α a)))
    (x : C) (hx : f x = 0) :
    ∃ (u : R) (z : C), f (i u) = 0 ∧ x = i u + (p : C) * z := by
  obtain ⟨s, z, rfl⟩ := hd x (N + 1)
  obtain ⟨a, ha⟩ := hb z
  refine ⟨s + (p : R) * α a, (p : C) ^ N * z - i (α a), ?_, ?_⟩
  · rw [map_add, map_mul, map_pow, map_natCast] at hx
    rw [map_add, map_mul, map_natCast, map_add, map_mul, map_natCast, ← ha, ← hx]
    ring
  · rw [map_add, map_mul, map_natCast]
    ring

theorem ev_algebraMap (l : ℕ) [Fact l.Prime] (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem fil_dense : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → ∀ (n : ℕ) (x : Per.Acris l), j x ∈ Per.FilP l n → ∃ (u : Per.Acris0 l) (z : Per.Acris l), (u : Per.AinfP l) ∈ Per.kerP l ^ n ∧ x = algebraMap (Per.Acris0 l) (Per.Acris l) u + (l : Per.Acris l) * z := by
  intro l _ j hj n x hx
  obtain ⟨N, hN⟩ := hj.bdd n
  have h0 : ∀ u : Per.Acris0 l, ((Per.ev l n).comp j) (algebraMap (Per.Acris0 l) (Per.Acris l) u) =
      Ideal.Quotient.mk _ (u : Per.AinfP l) := fun u => by
    rw [RingHom.comp_apply, hj.on0, ev_algebraMap]
  obtain ⟨u, z, hu, hz⟩ := dense_ker_of_bounded l (algebraMap (Per.Ainf l) (Per.Acris0 l))
    (algebraMap (Per.Acris0 l) (Per.Acris l)) ((Per.ev l n).comp j) N (acris_basic l).2.2.1
    (fun y => by
      obtain ⟨a, ha⟩ := hN y
      refine ⟨a, ?_⟩
      rw [map_mul, map_pow, map_natCast] at ha
      rw [h0]
      exact ha) x ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l n (j x)).1 hx)
  refine ⟨u, z, ?_, hz⟩
  rw [h0] at hu
  exact Ideal.Quotient.eq_zero_iff_mem.1 hu

end GlobalTheory.MemLoc
