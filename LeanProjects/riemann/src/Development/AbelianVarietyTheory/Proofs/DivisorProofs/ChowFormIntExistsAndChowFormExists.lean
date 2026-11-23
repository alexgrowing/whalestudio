import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormOfHomogeneousPrimeKrullDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyConeIdealEqFieldDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDegreeLeChowFormDegreeAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormDegreeLeFieldDegreeAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeMapRationalFunctionsGenericLinearFormNotM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeSaturationGenericHyperplaneSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAndHilbertPolyEqOfPrimeInSaturation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormGenericHyperplaneSection

set_option autoImplicit false

namespace GlobalTheory.ChowExists

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {N : ℕ}

theorem isHomogeneous_of_component {I : Ideal (MvPolynomial (Fin N) K)}
    (h : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) :
    I.IsHomogeneous (homogeneousSubmodule (Fin N) K) := fun d g hg => by
  have e : ((DirectSum.decompose (homogeneousSubmodule (Fin N) K) g d : _) : MvPolynomial (Fin N) K) =
      homogeneousComponent d g := MvPolynomial.decomposition.decompose'_apply g d
  rw [e]
  exact h g hg d

theorem aeval_eq_zero_of_block {P : Ideal (MvPolynomial (Fin N) K)} {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f)
    (t : Fin (D + 1) × Fin N → AlgebraicClosure K) (i : Fin (D + 1)) (ht : ∀ j, t (i, j) = 0) :
    aeval t f = 0 := by
  have h1 := (isMultiHomogeneous_iff_block.1 h.homog).aeval_smul
    (fun l => if l = i then (0 : AlgebraicClosure K) else 1) t
  have h2 : (fun v : Fin (D + 1) × Fin N => (if v.1 = i then (0 : AlgebraicClosure K) else 1) * t v) = t := by
    funext v
    split_ifs with hv
    · obtain ⟨l, j⟩ := v
      obtain rfl : l = i := hv
      rw [ht, mul_zero]
    · rw [one_mul]
  rw [h2, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h.pos.ne']), zero_mul] at h1
  exact h1

theorem not_lt_of_isChowFormInt {P : Ideal (MvPolynomial (Fin N) K)} {D D' δ δ' : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} {f' : MvPolynomial (Fin (D' + 1) × Fin N) K}
    (h : IsChowFormInt P D δ f) (h' : IsChowFormInt P D' δ' f') : ¬ D < D' := fun hlt => by
  refine h.ne_zero (map_injective _ (algebraMap K (AlgebraicClosure K)).injective ?_)
  refine MvPolynomial.funext fun u => ?_
  rw [map_zero, map_zero, eval_map, ← aeval_def]
  obtain ⟨y, hy, hP, hu⟩ := (h'.zero_iff _).1 (aeval_eq_zero_of_block h'
    (fun v => if hv : (v.1 : ℕ) < D + 1 then u (⟨v.1, hv⟩, v.2) else 0) (Fin.last _)
    (fun j => dif_neg (by simp; omega)))
  refine (h.zero_iff u).2 ⟨y, hy, hP, fun i => ?_⟩
  have := hu ⟨i, by omega⟩
  simpa only [dif_pos i.2] using this

theorem exists_X_notMem {P : Ideal (MvPolynomial (Fin N) K)} {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f) : ∃ j, X j ∉ P := by
  obtain ⟨y, hy, hyI⟩ := h.exists_point
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  exact ⟨j, fun hX => hj (by simpa using hyI _ hX)⟩

theorem ringKrullDim_of_isChowFormInt {P : Ideal (MvPolynomial (Fin N) K)} [hp : P.IsPrime]
    (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f) :
    ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ) := by
  obtain ⟨j, hj⟩ := exists_X_notMem h
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ (isHomogeneous_of_component hP) hj
  obtain ⟨δ', f', h'⟩ := GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq K N e P hp hP he
  obtain rfl : e = D := le_antisymm (not_lt.1 (not_lt_of_isChowFormInt h h'))
    (not_lt.1 (not_lt_of_isChowFormInt h' h))
  exact he

theorem exists_eq_coneIdeal {P : Ideal (MvPolynomial (Fin N) K)} [hp : P.IsPrime]
    (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) {δ : ℕ}
    {f : MvPolynomial (Fin (0 + 1) × Fin N) K} (h : IsChowFormInt P 0 δ f) :
    ∃ (y : Fin N → AlgebraicClosure K) (j : Fin N), y j = 1 ∧ P = coneIdeal K y := by
  obtain ⟨y, hy, hyI⟩ := h.exists_point
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have hj' : y j ≠ 0 := hj
  refine ⟨(y j)⁻¹ • y, j, by simp [hj'], ?_⟩
  rw [coneIdeal_smul (inv_ne_zero hj')]
  have hle : P ≤ coneIdeal K y := fun g hg => (mem_coneIdeal_iff y g).2 fun d => hyI _ (hP g hg d)
  by_contra hne
  have := isPrime_coneIdeal (K := K) y
  have hX : (X j : MvPolynomial (Fin N) K) ∉ coneIdeal K y := fun hX =>
    hj' (by simpa using aeval_eq_zero_of_mem_coneIdeal hX)
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ (isHomogeneous_coneIdeal y) hX
  have := ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hle hne)
  rw [he, ringKrullDim_of_isChowFormInt hP h] at this
  have h2 : (e + 1 + 1 : ℕ) ≤ (0 + 1 : ℕ) := by exact_mod_cast this
  omega

theorem coeff_sub_comp {H : Polynomial ℚ} {D : ℕ} (h : H.natDegree ≤ D + 1) :
    (H - H.comp (Polynomial.X - Polynomial.C ((1 : ℕ) : ℚ))).coeff D = (D + 1) * H.coeff (D + 1) := by
  have e : H.comp (Polynomial.X - Polynomial.C ((1 : ℕ) : ℚ)) = Polynomial.taylor (-1) H := by
    rw [Polynomial.taylor_apply]; simp [sub_eq_add_neg]
  have h1 : (Polynomial.hasseDeriv D H).natDegree ≤ 1 :=
    (Polynomial.natDegree_hasseDeriv_le _ _).trans (by omega)
  rw [e, Polynomial.coeff_sub, Polynomial.taylor_coeff, Polynomial.eq_X_add_C_of_natDegree_le_one h1]
  simp [Polynomial.hasseDeriv_coeff, add_comm 1 D]

theorem degree_eq_coeff (D : ℕ) : ∀ (K : Type) [Field K] [CharZero K] (P : Ideal (MvPolynomial (Fin N) K))
    [P.IsPrime], (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → ∀ (δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f →
    (δ : ℚ) = (D.factorial : ℚ) * (idealHilbertPoly P).coeff D := by
  induction D with
  | zero =>
    intro K _ _ P _ hP δ f h
    obtain ⟨y, j, hy, rfl⟩ := exists_eq_coneIdeal hP h
    rw [GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin K N y j hy, le_antisymm (GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt K N δ y j f hy h) (GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt K N δ y j f hy h)]
    simp
  | succ D ih =>
    intro K _ _ P hp hP δ f h
    let L := FractionRing (MvPolynomial (Fin N) K)
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    obtain ⟨hE, hEH⟩ := GlobalTheory.HilbBaseChange.idealHilbertPoly_map K L N P hP
    obtain ⟨hEp, hl⟩ := GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem K L N P hp
    obtain ⟨Q, hQ, hIQ, hsat⟩ := GlobalTheory.Chow.exists_prime_saturation_generic_section K L N P hp fun u => by
      obtain ⟨y, hy, h1, h2⟩ := (h.zero_iff _).1 (aeval_eq_zero_of_block h
        (fun v => if v.1 = 0 then u v.2 else 0) (Fin.last _) (fun j => if_neg (by simp)))
      exact ⟨y, hy, h1, by simpa using h2 0⟩
    obtain ⟨f', hf'⟩ := GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section K L N P D δ f hP h
    have hlin : (∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
        MvPolynomial (Fin N) L).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X L j).C_mul _
    have hI := isHomogeneous_sup_span_singleton (isHomogeneous_of_component hE) hlin
    obtain ⟨hQh, hQH⟩ := GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq L N _ Q (fun g hg n => homogeneousComponent_mem_of_mem hI hg n) hQ hIQ hsat
    have hf'' : IsChowFormInt Q D δ f' := ⟨hf'.homog, hf'.irred, fun u => (hf'.zero_iff u).trans
      (exists_congr fun y => and_congr_right fun hy => and_congr_left fun _ =>
        ⟨fun h1 g hg => by
          obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
          obtain ⟨m, hm⟩ := hsat g hg j
          have := h1 _ hm
          rw [map_mul, map_pow, aeval_X] at this
          exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hj), fun h1 g hg => h1 g (hIQ hg)⟩)⟩
    have hdeg := degree_idealHilbertPoly_eq_of_isPrime (isHomogeneous_of_component hP)
      (ringKrullDim_of_isChowFormInt hP h)
    rw [ih L Q hQh δ f' hf'', hQH,
      idealHilbertPoly_sup_of_isPrime (isHomogeneous_of_component hE) hlin (hl (exists_X_notMem h)), hEH,
      coeff_sub_comp (Polynomial.natDegree_le_of_degree_le hdeg.le), Nat.factorial_succ]
    push_cast
    ring

theorem degree_eq_hilbertDegree [CharZero K] {P : Ideal (MvPolynomial (Fin N) K)} [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin N) K)) {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f) : δ = hilbertDegree P := by
  have hP' := fun g hg n => homogeneousComponent_mem_of_mem hP (p := g) hg n
  have h1 := degree_eq_coeff D K P hP' δ f h
  rw [← cast_hilbertDegree_of_degree_eq hP
    (degree_idealHilbertPoly_eq_of_isPrime hP (ringKrullDim_of_isChowFormInt hP' h))] at h1
  exact_mod_cast h1

theorem exists_isChowFormInt [CharZero K] {P : Ideal (MvPolynomial (Fin N) K)} (hp : P.IsPrime)
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin N) K)) {D : ℕ}
    (hD : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ)) :
    ∃ f : MvPolynomial (Fin (D + 1) × Fin N) K, IsChowFormInt P D (hilbertDegree P) f := by
  obtain ⟨δ, f, hf⟩ := exists_isChowFormInt_of_ringKrullDim_eq K N D P hp
    (fun g hg n => homogeneousComponent_mem_of_mem hP hg n) hD
  exact ⟨f, degree_eq_hilbertDegree hP hf ▸ hf⟩

theorem comap_map_eq {L σ : Type} [Field L] [Algebra K L] (I : Ideal (MvPolynomial σ K)) :
    (I.map (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L)).comap
      (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L) = I := by
  obtain ⟨r, hr⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  have hr' : ∀ c : K, r (algebraMap K L c) = c := fun c => LinearMap.congr_fun hr c
  let ρ : MvPolynomial σ L → MvPolynomial σ K := fun p => ∑ s ∈ p.support, monomial s (r (coeff s p))
  have hρ : ∀ p s, coeff s (ρ p) = r (coeff s p) := fun p s => by
    classical
    simp only [ρ, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.1 h, map_zero]
  have hadd : ∀ p q, ρ (p + q) = ρ p + ρ q := fun p q => MvPolynomial.ext _ _ fun s => by
    simp only [hρ, coeff_add, map_add]
  have hmul : ∀ p (g : MvPolynomial σ K), ρ (p * map (algebraMap K L) g) = ρ p * g := fun p g =>
    MvPolynomial.ext _ _ fun s => by
      classical
      simp only [hρ, coeff_mul, map_sum, coeff_map]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  refine le_antisymm (fun g hg => ?_) Ideal.le_comap_map
  have key : ∀ p ∈ I.map (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L),
      ∀ q, ρ (q * p) ∈ I := fun p hp => by
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact fun q => hmul q x ▸ I.mul_mem_left _ hx
    | zero =>
      intro q
      have : ρ (q * 0) = 0 := MvPolynomial.ext _ _ fun s => by simp [hρ]
      exact this ▸ I.zero_mem
    | add x y _ _ hx hy => exact fun q => by rw [mul_add, hadd]; exact I.add_mem (hx q) (hy q)
    | smul a x _ hx => exact fun q => by rw [smul_eq_mul, ← mul_assoc]; exact hx _
  have h1 := key _ hg 1
  have h2 : ρ (1 * map (algebraMap K L) g) = g := MvPolynomial.ext _ _ fun s => by
    rw [hρ, one_mul, coeff_map, hr']
  rwa [h2] at h1

theorem exists_isChowForm [CharZero K] {I : Ideal (MvPolynomial (Fin N) K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) K))
    (hp : (I.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) :
      MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (AlgebraicClosure K))).IsPrime) {D : ℕ}
    (hD : ringKrullDim (MvPolynomial (Fin N) K ⧸ I) = (D + 1 : ℕ)) :
    ∃ f : MvPolynomial (Fin (D + 1) × Fin N) K, IsChowForm I D (hilbertDegree I) f := by
  have hpI : I.IsPrime := by
    rw [← comap_map_eq (L := AlgebraicClosure K) I]
    exact Ideal.comap_isPrime _ _
  obtain ⟨f, hf⟩ := exists_isChowFormInt hpI hI hD
  refine ⟨f, hf.isChowForm ?_⟩
  obtain ⟨hE, hEH⟩ := GlobalTheory.HilbBaseChange.idealHilbertPoly_map K (AlgebraicClosure K) N I
    (fun g hg n => homogeneousComponent_mem_of_mem hI hg n)
  have hE' := isHomogeneous_of_component hE
  obtain ⟨j, hj⟩ := exists_X_notMem hf
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ hE' (i := j) (fun h => hj (by
    rw [← comap_map_eq (L := AlgebraicClosure K) I, Ideal.mem_comap, map_X]
    exact h))
  have h1 := degree_idealHilbertPoly_eq_of_isPrime hE' he
  rw [hEH, degree_idealHilbertPoly_eq_of_isPrime hI hD] at h1
  obtain rfl : D = e := by exact_mod_cast h1
  obtain ⟨f', hf'⟩ := exists_isChowFormInt hp hE' he
  rw [hilbertDegree, hEH, ← hilbertDegree] at hf'
  have hdvd : f' ∣ map (algebraMap K (AlgebraicClosure K)) f := hf'.dvd_of_forall_aeval_eq_zero fun u hu => by
    obtain ⟨y, hy, h2, h3⟩ := (hf'.zero_iff u).1 hu
    rw [aeval_map_algebraMap]
    refine (hf.zero_iff_of_isAlgClosed hI u).2 ⟨y, hy, fun g hg => ?_, h3⟩
    have := h2 _ (Ideal.mem_map_of_mem _ hg)
    rwa [aeval_map_algebraMap] at this
  have hF0 : map (algebraMap K (AlgebraicClosure K)) f ≠ 0 := fun h =>
    hf.ne_zero (map_injective _ (algebraMap K (AlgebraicClosure K)).injective (h.trans (map_zero _).symm))
  have hFh := ((isMultiHomogeneous_iff_block.1 hf.homog).isHomogeneous).map (algebraMap K (AlgebraicClosure K))
  have hfh := (isMultiHomogeneous_iff_block.1 hf'.homog).isHomogeneous
  obtain ⟨c, hc, hcf⟩ := GlobalTheory.Chow.exists_eq_C_mul_of_dvd hF0 hdvd
    (by rw [hFh.totalDegree hF0, hfh.totalDegree hf'.ne_zero])
  rw [hcf]
  exact (hf'.C_mul hc).irred

end GlobalTheory.ChowExists

namespace GlobalTheory.Published

theorem chowFormIntExists_holds : ChowFormIntExists :=
  chowFormIntExists_iff.2 fun _ _ _ _ _ _ hP hp hD => GlobalTheory.ChowExists.exists_isChowFormInt hp hP hD

theorem chowFormExists_holds : ChowFormExists :=
  chowFormExists_iff.2 fun _ _ _ _ _ _ hP hp hD => GlobalTheory.ChowExists.exists_isChowForm hP hp hD

end GlobalTheory.Published
