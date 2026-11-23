import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Eps0UnramFrob
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.NoLocalInvariants

section General

variable {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]

theorem eq_zero_of_fixed {M : Matrix n n R} (h : (M - 1).det ≠ 0)
    {x : n → FractionRing R} (hx : (M.map (algebraMap R (FractionRing R))).mulVec x = x) : x = 0 := by
  have h1 : ((M - 1).map (algebraMap R (FractionRing R))).mulVec x = 0 := by
    have e : (M - 1).map (algebraMap R (FractionRing R)) =
        M.map (algebraMap R (FractionRing R)) - 1 := by
      ext a b
      simp [Matrix.sub_apply, Matrix.one_apply, apply_ite (algebraMap R (FractionRing R))]
    rw [e, Matrix.sub_mulVec, hx, Matrix.one_mulVec, sub_self]
  have h2 : ((M - 1).map (algebraMap R (FractionRing R))).det ≠ 0 := by
    have e : ((M - 1).map (algebraMap R (FractionRing R))).det =
        algebraMap R (FractionRing R) (M - 1).det := by
      simpa using ((algebraMap R (FractionRing R)).map_det (M - 1)).symm
    rw [e]
    exact fun h0 => h ((IsFractionRing.injective R (FractionRing R)) (by simpa using h0))
  exact Matrix.eq_zero_of_mulVec_eq_zero h2 h1

theorem det_inv_transpose_sub_one_ne_zero {M : Matrix n n R} (hu : IsUnit M.det)
    (h : (M - 1).det ≠ 0) : ((M⁻¹).transpose - 1).det ≠ 0 := by
  have e : (M⁻¹).transpose - 1 = (M⁻¹ - 1).transpose := by simp
  rw [e, Matrix.det_transpose]
  intro h0
  have h1 : (M⁻¹ - 1) * M = -(M - 1) := by
    rw [sub_mul, Matrix.nonsing_inv_mul _ hu, one_mul]
    abel
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_neg] at h2
  have h3 : ((-1 : R) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ (by simp)
  exact h (by simpa [h3] using h2.symm)

omit [IsDomain R] in

theorem det_scaled_sub_one_ne_zero [IsLocalRing R] (P : Matrix n n R) (c : Rˣ)
    (h : (P.map (IsLocalRing.residue R) - (IsLocalRing.residue R (c : R)) • (1 : Matrix n n _)).det ≠ 0) :
    ((((c⁻¹ : Rˣ) : R) • P) - 1).det ≠ 0 := by
  intro h0
  have e1 : P - (c : R) • (1 : Matrix n n R) = (c : R) • ((((c⁻¹ : Rˣ) : R) • P) - 1) := by
    rw [smul_sub, smul_smul, Units.mul_inv, one_smul]
  have e2 : (P - (c : R) • (1 : Matrix n n R)).det = 0 := by
    rw [e1, Matrix.det_smul, h0, mul_zero]
  apply h
  have e3 : P.map (IsLocalRing.residue R) - (IsLocalRing.residue R (c : R)) • (1 : Matrix n n _) =
      (P - (c : R) • (1 : Matrix n n R)).map (IsLocalRing.residue R) := by
    ext a b
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite (IsLocalRing.residue R)]
  rw [e3]
  have := (IsLocalRing.residue R).map_det (P - (c : R) • (1 : Matrix n n R))
  rw [e2, map_zero] at this
  simpa using this.symm

end General

theorem noInv_of_adm2At : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → ∀ k, D.host.g k ≠ D.ntw.l i → ∀ v ∈ placesOver D.host.E (D.host.g k), NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s h k hk v hv
  have hvl : v ∉ placesOver D.host.E (D.ntw.l i) := by
    intro hl
    have hlp : (D.ntw.l i).Prime := Fact.out
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2
      ((Nat.coprime_primes (D.host.g_prime k) hlp).2 hk)
    have h1 : (1 : 𝓞 D.host.E) ∈ v.asIdeal := by
      have e : (1 : 𝓞 D.host.E) = (a : 𝓞 D.host.E) * ((D.host.g k : ℕ) : 𝓞 D.host.E) +
          (b : 𝓞 D.host.E) * ((D.ntw.l i : ℕ) : 𝓞 D.host.E) := by
        have h2 := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
        push_cast at h2
        exact h2.symm
      rw [e]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hl)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have key : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) A v →
      ∃ σ ∈ Ine (F := D.host.E) A, (Tmat i s σ - 1).det ≠ 0 := by
    intro A hA
    obtain ⟨-, σ, hσ, hdet⟩ := h.2 k hk v hv A hA
    exact ⟨σ, hσ, det_scaled_sub_one_ne_zero _ _ hdet⟩
  constructor
  · intro A hA x hx
    obtain ⟨σ, hσ, hd⟩ := key A hA
    exact eq_zero_of_fixed hd (hx σ (Ine_le_Dec A hσ))
  · intro A hA x hx
    obtain ⟨σ, hσ, hd⟩ := key A hA
    have he := (GlobalTheory.TripleGal.eps0_unram_frob D i v hvl A hA).1 σ hσ
    have hu : IsUnit (Tmat i s σ).det := by
      rw [← Tgl_coe]
      exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    have hT : Tdual i s σ = ((Tmat i s σ)⁻¹).transpose := by
      simp [Tdual, he]
    have := hx σ (Ine_le_Dec A hσ)
    rw [hT] at this
    exact eq_zero_of_fixed (det_inv_transpose_sub_one_ne_zero hu hd) this

end GlobalTheory.NoLocalInvariants
