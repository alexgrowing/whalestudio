import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Eps0UnramFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffProdOneSubCMulX
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.HkFrobProof

theorem eval_charpolyRev_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b
  by_cases h : a = b <;> simp [h] <;> ring

theorem coeff_charpolyRev_map {n : ℕ} {R : Type} [CommRing R] (f : R →+* ℂ) (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    f (M.charpolyRev.coeff k) = (M.map f).charpolyRev.coeff k := by
  rw [← Polynomial.coeff_map]
  congr 1
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 1
  by_cases h : a = b <;> simp [h]

theorem charpolyRev_smul_inv {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (h : M * A = 1) (β : Multiset ℂ)
    (hβ : (0 : ℂ) ∉ β) (hA : A.charpoly = (β.map fun a => (X : ℂ[X]) - C a).prod) (c : ℂ) :
    (c • M).charpolyRev = (β.map fun a => (1 : ℂ[X]) - C (c * a⁻¹) * X).prod := by
  have ev : ∀ y : ℂ, (y • (1 : Matrix (Fin n) (Fin n) ℂ) - A).det = (β.map fun a => y - a).prod := by
    intro y
    have := congrArg (Polynomial.eval y) hA
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at this
    simpa using this
  apply Polynomial.funext
  intro z
  rw [eval_charpolyRev_eq, eval_multiset_prod, Multiset.map_map]
  have h0 := ev 0
  have h1 := ev (z * c)
  have hne : (β.map fun a => (0 : ℂ) - a).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hm
    obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.1 hm
    have : a = 0 := by simpa using ha0
    exact hβ (this ▸ ha)
  apply mul_right_cancel₀ hne
  rw [← Multiset.prod_map_mul]
  conv_lhs => rw [← h0, ← Matrix.det_mul]
  have e : (1 - z • c • M) * ((0 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A) = (z * c) • 1 - A := by
    rw [zero_smul, zero_sub, mul_neg, sub_mul, one_mul, smul_smul, Matrix.smul_mul, h, neg_sub]
  rw [e, h1]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  have ha0 : a ≠ 0 := fun h => hβ (h ▸ ha)
  simp only [Function.comp, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem rd_injective {D : D7} (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) :
    Function.Injective (rd i ι) :=
  ι.injective.comp (IsFractionRing.injective (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)))

theorem hkFrob_of_tripleAtt : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i),
    TripleAtt D.naut bkP i s → HkFrob i s := by
  rintro D bkP i s ⟨ι, π₁, π, -, hA, hR, hS⟩ P hP hsp σ hσ k hk
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)
  have hu : D.naut.unr (D.naut.locG π P) :=
    hR.unr P (fun k h => hP (D.ntw.placesOver_subset_exceptional i k h)) (fun h => hP (D.ntw.primes_subset_exceptional i h))
  have hpl : IsPlaceOver (F := D.host.E) (D.nd.plOm.1 P) P := D.nd.plOm.2 P
  have hfr := hA.frob P hl hu _ _ hpl hσ
  rw [D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at hfr
  have he := (GlobalTheory.TripleGal.eps0_unram_frob D i P hl _ hpl).2 _ hσ
  obtain ⟨h, hh, hrd⟩ := hS P hP hsp k hk
  have hq0 : (normV P : ℕ) ≠ 0 := by
    intro h0
    rw [h0] at he
    exact Units.ne_zero _ (he.trans Nat.cast_zero)
  have hqC : ((normV P : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have hne := D.naut.frobEig_ne_zero _ hu
  set q : ℂ := ((normV P : ℕ) : ℂ) with hq
  set α := D.naut.frobEig (D.naut.locG π P) with hα
  have hcard : Multiset.card α = D.R.r := by
    have := congrArg natDegree hfr
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have heps : rd i ι ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = q⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [hq, ← map_natCast (rd i ι), ← he, ← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, map_one]
  have hMA : (Tmat i s σ).map (rd i ι) *
      ((Tgl i s σ⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)).map (rd i ι) = 1 := by
    rw [← Tgl_coe, ← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hne' : (0 : ℂ) ∉ α.map (· * q ^ (((1 - (D.R.t : ℝ)) / 2 : ℝ) : ℂ)) := by
    intro hm
    obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.1 hm
    rcases mul_eq_zero.1 ha0 with h0 | h0
    · exact hne (h0 ▸ ha)
    · exact hqC ((Complex.cpow_eq_zero_iff _ _).1 h0).1
  have key := charpolyRev_smul_inv _ _ hMA _ hne' hfr (q⁻¹ ^ D.R.t)
  have hes := GlobalTheory.normalised_esymm_eq_coeff D.R.r ((normV P : ℕ) : ℝ) (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq0))
    (α.map fun a => a⁻¹ * q ^ (-((D.R.r : ℂ) + D.R.t) / 2)) (by rw [Multiset.card_map, hcard]) k hk
  rw [Complex.ofReal_natCast, ← hq, ← hrd] at hes
  have hmain : (-1 : D.ntw.O0 i) ^ k * ((normV P : ℕ) : D.ntw.O0 i) ^ (k * (k - 1) / 2) * h =
      (((((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) • Tmat i s σ).charpolyRev).coeff k := by
    apply rd_injective i ι
    rw [coeff_charpolyRev_map, Matrix.map_smul' _ _ _ (map_mul _), map_pow (rd i ι) _ D.R.t, heps, key, map_mul,
      map_mul, map_pow, map_pow, map_neg, map_one, map_natCast, ← hq, hes, Multiset.map_map, Multiset.map_map]
    congr 2
    apply Multiset.map_congr rfl
    intro a _
    simp only [Function.comp]
    congr 3
    have e1 : q ^ (((D.R.r : ℂ) - 1) / 2) * q ^ (-((D.R.r : ℂ) + D.R.t) / 2) =
        q⁻¹ ^ D.R.t * (q ^ (((1 - (D.R.t : ℝ)) / 2 : ℝ) : ℂ))⁻¹ := by
      rw [← Complex.cpow_add _ _ hqC, ← Complex.cpow_neg, inv_pow, ← Complex.cpow_natCast, ← Complex.cpow_neg,
        ← Complex.cpow_add _ _ hqC]
      congr 1
      push_cast
      ring
    rw [mul_inv, mul_left_comm, e1]
    ring
  rw [← hmain, hh]
  simp

end GlobalTheory.TripleGal.HkFrobProof
