import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WBMemLatS
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem exists_monic_eval₂_of_span {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (S : Subring B)
    (T : Finset B) (hW : ∀ a, f a ∈ S) (hT : ∀ t ∈ T, t ∈ S)
    (hS : ∀ s ∈ S, ∃ a : B → A, s = ∑ t ∈ T, t * f (a t)) (e : B) (he : e ∈ S) :
    ∃ P : Polynomial A, P.Monic ∧ P.eval₂ f e = 0 := by
  letI : Algebra A B := f.toAlgebra
  let C : Subalgebra A B := { S with algebraMap_mem' := hW }
  have hfg : (Subalgebra.toSubmodule C).FG := by
    refine ⟨T, le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.2 fun t ht => hT t ht
    · intro s hs
      obtain ⟨a, rfl⟩ := hS s hs
      refine Submodule.sum_mem _ fun t ht => ?_
      have : t * f (a t) = a t • t := by
        rw [Algebra.smul_def, mul_comm]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ht)
  exact IsIntegral.of_mem_of_fg C hfg e he

theorem pow_natDegree_eq_zero_of_eval₂ {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]
    (f : A →+* B) (hf : Function.Injective f) (c : A →+* R) (P : Polynomial A) (hP : P.Monic)
    (e : B) (he : P.eval₂ f e = 0) (n v : A) (hn : c n = 0) (hv : f n * e = f v) :
    c v ^ P.natDegree = 0 := by
  have h1 : (P.scaleRoots n).eval₂ f (f v) = 0 := by
    rw [← hv, Polynomial.scaleRoots_eval₂_mul, he, mul_zero]
  have h2 : (P.scaleRoots n).eval v = 0 := by
    apply hf
    rw [← Polynomial.eval₂_at_apply, h1, map_zero]
  have h3 : (P.scaleRoots n).eval₂ c (c v) = 0 := by
    rw [Polynomial.eval₂_at_apply, h2, map_zero]
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.natDegree_scaleRoots,
    Finset.sum_eq_single P.natDegree] at h3
  · rw [Polynomial.coeff_scaleRoots, Nat.sub_self, pow_zero, mul_one, Polynomial.coeff_natDegree,
      hP.leadingCoeff, map_one, one_mul] at h3
    exact h3
  · intro i hi hne
    have hlt : i < P.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hne
    rw [Polynomial.coeff_scaleRoots, map_mul, map_pow, hn, zero_pow (Nat.sub_ne_zero_of_lt hlt)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h

theorem tch_ne_mul_of_pow_eq {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)) (T : Finset (Formalism.Per6.BdRp l)) :
    (∀ a, wB l a ∈ S) → (∀ t ∈ T, t ∈ S) →
    (∀ s ∈ S, ∃ a : Formalism.Per6.BdRp l → Wl l, s = ∑ t ∈ T, t * wB l (a t)) →
    ∀ (ϖ y : Formalism.Per6.BdRp l) (N : ℕ), y ∈ S → ϖ ^ N = (l : Formalism.Per6.BdRp l) * y →
    ∀ u : Tl l, u ≠ 0 → ∀ s ∈ S, tch l u ≠ ϖ * s := by
  intro hW hT hS ϖ y N hy hN u hu s hs h
  haveI := GroundTheory.PAdicHodge.IsPerfectoidField.isDomain_preTilt (K := ℂ_[l]) l
  obtain ⟨P, hP, hev⟩ := exists_monic_eval₂_of_span (wB l) S T hW hT hS (y * s ^ N)
    (S.mul_mem hy (S.pow_mem hs N))
  have hinj : Function.Injective (wB l) := PositivityTheory.LocInh.wittTo_injective
  have hv : wB l (l : Wl l) * (y * s ^ N) = wB l (WittVector.teichmuller l (u ^ N)) := by
    have h1 : wB l (WittVector.teichmuller l (u ^ N)) = tch l u ^ N := by
      rw [map_pow, map_pow]; rfl
    rw [h1, h, mul_pow, hN, map_natCast, mul_assoc]
  have hc : (WittVector.constantCoeff : Wl l →+* Tl l) (l : Wl l) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero _ _
  have h0 := pow_natDegree_eq_zero_of_eval₂ (wB l) hinj WittVector.constantCoeff P hP _ hev
    (l : Wl l) _ hc hv
  have h2 : (WittVector.constantCoeff : Wl l →+* Tl l) (WittVector.teichmuller l (u ^ N)) = u ^ N :=
    WittVector.teichmuller_coeff_zero l _
  rw [h2] at h0
  exact hu (eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero h0))

end GlobalTheory.CompanionTheory.LTPer
