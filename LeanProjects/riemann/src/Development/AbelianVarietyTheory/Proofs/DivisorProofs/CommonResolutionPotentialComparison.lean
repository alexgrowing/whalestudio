import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsUnitIffCharpolyCoeffZeroNe
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMobiusInverseMonicEq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem torusPair_pow_eq_one_iff {F : Type} [Field F] [Finite F] (n : ℕ) (α : AlgebraicClosure F) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ n - 1) = 1 ↔ (minpoly F α).natDegree ∣ n := by
  have hi : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  rw [(minpoly.irreducible hi).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]
  have hq : 0 < Nat.card F ^ n := pow_pos Nat.card_pos _
  simp only [map_sub, map_pow, aeval_X, sub_eq_zero]
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F ^ n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  constructor
  · intro h; rw [h, one_mul]
  · intro h; exact mul_right_cancel₀ h0 (h.trans (one_mul α).symm)

theorem torusPair_finite_monic {F : Type} [Field F] [Finite F] (n : ℕ) :
    {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}.Finite := by
  have : Finite (Polynomial.degreeLT F (n + 1)) := Finite.of_equiv _ (degreeLTEquiv F (n + 1)).symm.toEquiv
  have h : (Polynomial.degreeLT F (n + 1) : Set F[X]).Finite := Set.toFinite _
  refine h.subset fun P hP => ?_
  simp only [SetLike.mem_coe, mem_degreeLT]
  exact (degree_le_of_natDegree_le hP.2.1.le).trans_lt (by exact_mod_cast Nat.lt_succ_self n)

theorem torusPair_finite_torus {F : Type} [Field F] [Finite F] (n : ℕ) (hn : 0 < n) :
    {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}.Finite := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  refine (Polynomial.nthRootsFinset (Nat.card F ^ n - 1) (1 : AlgebraicClosure F)).finite_toSet.subset
    fun α hα => ?_
  exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset (by omega) _).2 hα)

theorem torusPair_mangoldt_pow {F : Type} [Field F] (s : F[X] → ℂ) (f : F[X]) (hf : f.Monic)
    (hirr : Irreducible f) (r : ℕ) (hr : 0 < r) : mangoldt s (f ^ r) = s f := by
  have hset : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ r' : ℕ, 0 < r' ∧ f ^ r = g ^ r'} = {f} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hg, hgi, r', hr', he⟩
      have h1 : g ∣ f ^ r := he ▸ dvd_pow_self g hr'.ne'
      have h2 : g ∣ f := hgi.prime.dvd_of_dvd_pow h1
      exact eq_of_monic_of_associated hg hf (hgi.associated_of_dvd hirr h2)
    · rintro rfl
      exact ⟨hf, hirr, r, hr, rfl⟩
  rw [mangoldt, hset, finsum_mem_singleton]

theorem torusPair_mangoldt_sum (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n k : ℕ)
    (S : F[X] → ℂ) (hn : 0 < n) :
    ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}, mangoldt (rootSum θ k) P * star (S P) =
      ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
        θ α ^ k * star (S (minpoly F α ^ (n / (minpoly F α).natDegree))) := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have hi : ∀ α : AlgebraicClosure F, IsIntegral F α := fun α => Algebra.IsIntegral.isIntegral α
  have hne : ∀ α : AlgebraicClosure F, α ^ (Nat.card F ^ n - 1) = 1 → α ≠ 0 := by
    rintro α h rfl
    rw [zero_pow (by omega)] at h
    exact zero_ne_one h
  rw [finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic n),
    finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_torus n hn),
    ← Finset.sum_fiberwise_of_maps_to (s := (torusPair_finite_torus (F := F) n hn).toFinset)
      (t := (torusPair_finite_monic (F := F) n).toFinset)
      (g := fun α => minpoly F α ^ (n / (minpoly F α).natDegree))]
  swap
  · intro α hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα ⊢
    have hm := minpoly.monic (hi α)
    refine ⟨hm.pow _, ?_, ?_⟩
    · rw [hm.natDegree_pow, Nat.div_mul_cancel ((torusPair_pow_eq_one_iff n α (hne α hα)).1 hα)]
    · rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
      exact pow_ne_zero _ (minpoly.coeff_zero_ne_zero (hi α) (hne α hα))
  refine Finset.sum_congr rfl fun P hP => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hP, hd, h0⟩ := hP
  by_cases hex : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m
  swap
  · have hempty : {f : F[X] | f.Monic ∧ Irreducible f ∧ ∃ m : ℕ, 0 < m ∧ P = f ^ m} = ∅ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hf, hirr, m, hm, rfl⟩
      exact hex ⟨f, m, hf, hirr, hm, rfl⟩
    rw [mangoldt, hempty, finsum_mem_empty, zero_mul]
    refine (Finset.sum_eq_zero fun α hα => ?_).symm
    exfalso
    obtain ⟨hα1, hα2⟩ := Finset.mem_filter.1 hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα1
    have hdv := (torusPair_pow_eq_one_iff n α (hne α hα1)).1 hα1
    exact hex ⟨minpoly F α, n / (minpoly F α).natDegree, minpoly.monic (hi α), minpoly.irreducible (hi α),
      Nat.div_pos (Nat.le_of_dvd hn hdv) (minpoly.natDegree_pos (hi α)), hα2.symm⟩
  obtain ⟨f, m, hf, hirr, hm, rfl⟩ := hex
  rw [hf.natDegree_pow] at hd
  have hdiv : n / f.natDegree = m := by
    rw [← hd, Nat.mul_div_cancel _ hirr.natDegree_pos]
  have hmp : ∀ α : AlgebraicClosure F, aeval α f = 0 → minpoly F α = f := fun α h =>
    (minpoly.eq_of_irreducible_of_monic hirr h hf).symm
  have hfib : Finset.filter (fun α : AlgebraicClosure F => minpoly F α ^ (n / (minpoly F α).natDegree) = f ^ m)
      (torusPair_finite_torus (F := F) n hn).toFinset = (f.map (algebraMap F (AlgebraicClosure F))).roots.toFinset := by
    ext α
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Multiset.mem_toFinset]
    rw [mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : n / (minpoly F α).natDegree ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd hn ((torusPair_pow_eq_one_iff n α (hne α h1)).1 h1))
          (minpoly.natDegree_pos (hi α))).ne'
      have h4 := congrArg (aeval α) h2
      rw [map_pow, map_pow, minpoly.aeval, zero_pow h3] at h4
      exact pow_eq_zero_iff hm.ne' |>.1 h4.symm
    · intro h
      have hα : α ≠ 0 := by
        rintro rfl
        apply h0
        rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
        rw [aeval_def, eval₂_at_zero, map_eq_zero] at h
        rw [h, zero_pow hm.ne']
      rw [torusPair_pow_eq_one_iff n α hα, hmp α h, hdiv]
      exact ⟨Dvd.intro_left _ hd, rfl⟩
  have hsep : f.Separable := PerfectField.separable_of_irreducible hirr
  have hnd : (f.map (algebraMap F (AlgebraicClosure F))).roots.Nodup := nodup_roots hsep.map
  rw [hfib, torusPair_mangoldt_pow _ f hf hirr m hm, rootSum,
    ← Multiset.dedup_eq_self.2 hnd, ← Multiset.toFinset_val, ← Finset.sum_eq_multiset_sum,
    Finset.val_toFinset, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Multiset.mem_toFinset, mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap] at hα
  rw [hmp α hα, hdiv]

theorem torusPair_finsum_GL_eq_ipGL (F : Type) [Field F] [Finite F] (m : ℕ) (s S : F[X] → ℂ) :
    ∑ᶠ x : GL (Fin m) F, psiG s m x * star (chG S m x) =
      ipGL (psi s (Fin m → F)) (fun g => S (LinearMap.charpoly g)) := by
  have h : ∀ x : GL (Fin m) F, psiG s m x * star (chG S m x) =
      (fun g => psi s (Fin m → F) g * star (S (LinearMap.charpoly g)))
        (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) := by
    intro x; simp [psiG, chG, Matrix.charpoly_toLin']
  rw [finsum_congr h, ipGL, ← finsum_mem_univ]
  apply finsum_mem_eq_of_bijOn (fun x : GL (Fin m) F => Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))
  · refine ⟨fun x _ => ?_, fun x _ y _ hxy => ?_, fun g hg => ?_⟩
    · have := x.isUnit.map (Matrix.toLinAlgEquiv' (R := F) (n := Fin m))
      simpa using this
    · exact Units.ext (Matrix.toLin'.injective hxy)
    · have hu : IsUnit (LinearMap.toMatrix' g) := by
        have := (show IsUnit g from hg).map (LinearMap.toMatrixAlgEquiv' (R := F) (n := Fin m))
        simpa using this
      exact ⟨hu.unit, Set.mem_univ _, by simp⟩
  · intro x _; rfl

theorem psiG_rootSum_pair_chG_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (m k : ℕ) (S : F[X] → ℂ), 0 < m → ((Nat.card F : ℂ) ^ m - 1) * ∑ᶠ x, psiG (rootSum θ k) m x * star (chG S m x) =
      (Nat.card (GL (Fin m) F) : ℂ) * ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ m - 1) = 1},
        θ α ^ k * star (S (minpoly F α ^ (m / (minpoly F α).natDegree))) := by
  intro F _ _ θ m k S hm
  have hadd := (rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  have hq1 : 1 < Nat.card F ^ m := Nat.one_lt_pow hm.ne' Finite.one_lt_card
  have hq : (Nat.card F : ℂ) ^ m - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hq1.ne'
  rw [torusPair_finsum_GL_eq_ipGL, ipGL_charpoly_eq_finsum_mass, Module.finrank_fin_fun,
    ← torusPair_mangoldt_sum F θ m k S hm]
  have hterm : ∀ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = m ∧ P.coeff 0 ≠ 0},
      mass (psi (rootSum θ k) (Fin m → F)) P * star (S P) =
        (Nat.card (GL (Fin m) F) : ℂ) * (mangoldt (rootSum θ k) P * star (S P)) / ((Nat.card F : ℂ) ^ m - 1) := by
    intro P hP
    obtain ⟨hPm, hPd, -⟩ := hP
    rw [mass_psi_eq_glCard_mul_mangoldt_div F (Fin m → F) (rootSum θ k) hadd P hPm (by simpa using hPd), hPd,
      glCard]
    ring
  rw [finsum_mem_congr rfl hterm, finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic m),
    finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic m), ← Finset.sum_div, ← Finset.mul_sum,
    mul_div_cancel₀ _ hq]

end GlobalTheory.Shin
