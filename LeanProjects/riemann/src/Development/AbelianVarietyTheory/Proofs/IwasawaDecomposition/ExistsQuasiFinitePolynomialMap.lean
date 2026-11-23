import Mathlib

namespace GlobalTheory.NoetherInt

open Polynomial

theorem quasiFinite_quotient_of_isUnit_coeff {R : Type*} [CommRing R] (G : R[X]) (k : ℕ)
    (hc : IsUnit (G.coeff k)) : Algebra.QuasiFinite R (R[X] ⧸ Ideal.span {G}) := by
  refine ⟨fun P _ => ?_⟩
  let f : R[X] →ₐ[R] (R[X] ⧸ Ideal.span {G}) := Ideal.Quotient.mkₐ R _
  have hf : Function.Surjective f := Ideal.Quotient.mkₐ_surjective R _
  let e := Polynomial.fiberEquivQuotient f hf P
  let I : Ideal (P.ResidueField[X]) :=
    (RingHom.ker (f : R[X] →+* (R[X] ⧸ Ideal.span {G}))).map (mapRingHom (algebraMap R P.ResidueField))
  let Gb : P.ResidueField[X] := G.map (algebraMap R P.ResidueField)
  have hG : Gb ≠ 0 := by
    intro h
    have h2 : (Gb).coeff k = 0 := by rw [h]; simp
    rw [coeff_map] at h2
    exact (hc.map (algebraMap R P.ResidueField)).ne_zero h2
  have hmem : Gb ∈ I := by
    refine Ideal.mem_map_of_mem (mapRingHom (algebraMap R P.ResidueField)) (x := G) ?_
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self G)
  have hM : (Gb * C Gb.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hG
  have hMI : Gb * C Gb.leadingCoeff⁻¹ ∈ I := I.mul_mem_right _ hmem
  have h1 : Module.Finite P.ResidueField
      (P.ResidueField[X] ⧸ Ideal.span {Gb * C Gb.leadingCoeff⁻¹}) := hM.finite_quotient
  have hle : Ideal.span {Gb * C Gb.leadingCoeff⁻¹} ≤ I := by
    rw [Ideal.span_singleton_le_iff_mem]; exact hMI
  have h2 : Module.Finite P.ResidueField (P.ResidueField[X] ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ P.ResidueField hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

theorem quasiFinite_of_eval₂_eq_zero {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T) (t : T)
    (h : (eval₂RingHom φ t).QuasiFinite) (G : R[X]) (hG : eval₂ φ t G = 0) (k : ℕ)
    (hc : IsUnit (G.coeff k)) : φ.QuasiFinite := by
  have hker : ∀ a ∈ Ideal.span {G}, eval₂RingHom φ t a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [hG]
  let ψ : (R[X] ⧸ Ideal.span {G}) →+* T := Ideal.Quotient.lift _ (eval₂RingHom φ t) hker
  have h1 : ψ.comp (Ideal.Quotient.mk (Ideal.span {G})) = eval₂RingHom φ t := by
    ext <;> simp [ψ]
  have h2 : ψ.QuasiFinite := RingHom.QuasiFinite.of_comp (g := Ideal.Quotient.mk (Ideal.span {G}))
    (h1 ▸ h)
  have h3 : (algebraMap R (R[X] ⧸ Ideal.span {G})).QuasiFinite :=
    RingHom.quasiFinite_algebraMap.2 (quasiFinite_quotient_of_isUnit_coeff G k hc)
  have h4 : ψ.comp (algebraMap R (R[X] ⧸ Ideal.span {G})) = φ := by
    ext a
    simp [ψ, IsScalarTower.algebraMap_apply R R[X] (R[X] ⧸ Ideal.span {G})]
  exact h4 ▸ h2.comp h3

theorem quasiFinite_of_isUnit_coeff {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T) (t : T)
    (h : (eval₂RingHom φ t).QuasiFinite) (G : R[X]) (hG : eval₂ φ t G = 0) (k : ℕ)
    (hc : IsUnit (φ (G.coeff k))) : φ.QuasiFinite := by
  let c := G.coeff k
  let φ' : Localization.Away c →+* T := IsLocalization.Away.lift c hc
  have hφ : φ'.comp (algebraMap R (Localization.Away c)) = φ := IsLocalization.Away.lift_comp c hc
  have hφx : ∀ a, φ' (algebraMap R (Localization.Away c) a) = φ a := fun a => by
    rw [← RingHom.comp_apply, hφ]
  have hι : (eval₂RingHom φ' t).comp (mapRingHom (algebraMap R (Localization.Away c)))
      = eval₂RingHom φ t := by
    ext <;> simp [hφx]
  have h1 : (eval₂RingHom φ' t).QuasiFinite := RingHom.QuasiFinite.of_comp
    (g := mapRingHom (algebraMap R (Localization.Away c))) (hι ▸ h)
  have hG' : eval₂ φ' t (G.map (algebraMap R (Localization.Away c))) = 0 := by
    have h5 := DFunLike.congr_fun hι G
    simpa [hG] using h5
  have h2 : φ'.QuasiFinite := quasiFinite_of_eval₂_eq_zero φ' t h1 _ hG' k (by
    rw [coeff_map]; exact IsLocalization.Away.algebraMap_isUnit c)
  have h3 : (algebraMap R (Localization.Away c)).QuasiFinite :=
    RingHom.quasiFinite_algebraMap.2 (.of_isLocalization (.powers c))
  exact hφ ▸ h2.comp h3

end GlobalTheory.NoetherInt

namespace GlobalTheory.NoetherInt

open MvPolynomial

section shear

variable {A : Type*} [CommRing A] {n : ℕ}

noncomputable def shearHom (A : Type*) [CommRing A] (n u : ℕ) (c : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ (u ^ i.1)

lemma shearHom_comp_neg (u : ℕ) (c : A) :
    (shearHom A n u c).comp (shearHom A n u (-c)) = AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;> simp [shearHom]

noncomputable def shear (A : Type*) [CommRing A] (n u : ℕ) :
    MvPolynomial (Fin (n + 1)) A ≃ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  AlgEquiv.ofAlgHom (shearHom A n u 1) (shearHom A n u (-1))
    (shearHom_comp_neg u 1)
    (by have := shearHom_comp_neg (A := A) (n := n) u (-1); rwa [neg_neg] at this)

lemma map_shear {B : Type*} [CommRing B] (φ : A →+* B) (u : ℕ)
    (g : MvPolynomial (Fin (n + 1)) A) :
    MvPolynomial.map φ (shear A n u g) = shear B n u (MvPolynomial.map φ g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [shear, shearHom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    cases i using Fin.cases <;> simp [shear, shearHom]

lemma map_finSuccEquiv {B : Type*} [CommRing B] (φ : A →+* B)
    (h : MvPolynomial (Fin (n + 1)) A) :
    Polynomial.map (MvPolynomial.map φ) (finSuccEquiv A n h) =
      finSuccEquiv B n (MvPolynomial.map φ h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq, Polynomial.map_add]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, hp]
    congr 1
    cases i using Fin.cases <;> simp [finSuccEquiv_X_zero, finSuccEquiv_X_succ]

end shear

section lead

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

local notation3 "up" => 2 + f.totalDegree
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1
local notation3 "T" => shear k n (2 + f.totalDegree)

variable {f v} in
private lemma lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ List.ofFn v, l < up := by
  grind

private lemma sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| List.ofFn_inj.mp ?_
  apply Nat.ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, mul_comm, List.sum_ofFn] using! h

private lemma shear_X_zero (u : ℕ) : shear k n u (X 0) = X 0 := by simp [shear, shearHom]

private lemma shear_X_succ (u : ℕ) (i : Fin n) :
    shear k n u (X i.succ) = X i.succ + X 0 ^ (u ^ i.succ.1) := by simp [shear, shearHom]

private lemma degreeOf_zero_t {a : k} (ha : a ≠ 0) : (T (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  have hT : T (MvPolynomial.C a) = MvPolynomial.C a := (shear k n _).commutes a
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [hT, Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    shear_X_zero, shear_X_succ, AlgEquiv.commutes, algebraMap_eq,
    map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (Polynomial.leadingCoeff_ne_zero.mp <| by
      simp [add_comm, Polynomial.leadingCoeff_X_pow_add_C])
  rw [Polynomial.natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), Polynomial.natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    Polynomial.natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [Polynomial.natDegree_pow, zero_add, Polynomial.natDegree_X, mul_one, Fin.val_zero,
    pow_zero, one_mul, add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), Polynomial.natDegree_X_pow_add_C, mul_comm])

private lemma degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (T <| monomial v <| coeff v f).degreeOf 0 ≠
    (T <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv, degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

private lemma leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv k n (T ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_prod]
    have h0 : (finSuccEquiv k n (T (MvPolynomial.C (coeff v f)))).leadingCoeff = algebraMap k _ (coeff v f) := by
      have : T (MvPolynomial.C (coeff v f)) = MvPolynomial.C (coeff v f) := (shear k n _).commutes (coeff v f)
      rw [this]; simp [finSuccEquiv_apply]
    have : ∀ j, ((finSuccEquiv k n) (T (X j))).leadingCoeff = 1 := fun j ↦ by
      cases j using Fin.cases with
      | zero => simp [shear_X_zero, finSuccEquiv_X_zero]
      | succ i =>
        simp only [shear_X_succ, map_add, map_pow, finSuccEquiv_X_succ, finSuccEquiv_X_zero]
        simp [add_comm, Polynomial.leadingCoeff_X_pow_add_C]
    simp only [h0, map_pow, Polynomial.leadingCoeff_pow, this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

theorem shear_leadingCoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (T f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n (T (h x))).degree <
      (finSuccEquiv k n (T (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply Polynomial.degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_t_ne_of_ne f _ _ h1 vin <| List.ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n (T (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n (T (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply Polynomial.leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| Polynomial.degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n (T (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| Polynomial.degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_t] at coeff
  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

end lead

end GlobalTheory.NoetherInt

namespace GlobalTheory.NoetherInt

open MvPolynomial

theorem exists_coeff_map_eq_C {K : Type*} [Field K] {n : ℕ} (φ : ℤ →+* K)
    (g : MvPolynomial (Fin (n + 1)) ℤ) (hg : MvPolynomial.map φ g ≠ 0) :
    ∃ (u k : ℕ) (a : K), a ≠ 0 ∧
      MvPolynomial.map φ ((finSuccEquiv ℤ n (shear ℤ n u g)).coeff k) = MvPolynomial.C a := by
  set f := MvPolynomial.map φ g with hf
  have hU := shear_leadingCoeff_isUnit f hg
  obtain ⟨a, ha, hE⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hU
  refine ⟨2 + f.totalDegree, (finSuccEquiv K n (shear K n (2 + f.totalDegree) f)).natDegree, a,
    ha.ne_zero, ?_⟩
  rw [← Polynomial.coeff_map, map_finSuccEquiv, map_shear, ← hf]
  exact hE

theorem exists_primitive_of_aeval_eq_zero {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    {n : ℕ} (y : Fin n → S) (g : MvPolynomial (Fin n) ℤ) (hg0 : g ≠ 0)
    (hg : aeval y g = 0) (I : Ideal ℤ) (hI : I ≠ ⊤) :
    ∃ g₀ : MvPolynomial (Fin n) ℤ, aeval y g₀ = 0 ∧ ∃ v, g₀.coeff v ∉ I := by
  classical
  have hs : g.support.Nonempty := support_nonempty.mpr hg0
  obtain ⟨b, hb, hgcd⟩ := Finset.extract_gcd (fun v => g.coeff v) hs
  set d := g.support.gcd (fun v => g.coeff v) with hd
  have hd0 : d ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := hs
    have := (Finset.gcd_eq_zero_iff.mp h) v hv
    exact (mem_support_iff.mp hv) this
  let g₀ : MvPolynomial (Fin n) ℤ := ∑ v ∈ g.support, monomial v (b v)
  have hc : ∀ v, v ∈ g.support → g₀.coeff v = b v := by
    intro v hv
    simp [g₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hv]
  have hc' : ∀ v, v ∉ g.support → g₀.coeff v = 0 := by
    intro v hv
    simp only [g₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    exact Finset.sum_eq_zero fun w hw => if_neg (fun h : w = v => hv (h ▸ hw))
  have hgd : g = MvPolynomial.C d * g₀ := by
    ext v
    rw [MvPolynomial.coeff_C_mul]
    by_cases hv : v ∈ g.support
    · rw [hc v hv]; exact hb v hv
    · rw [hc' v hv, mul_zero]; exact notMem_support_iff.mp hv
  refine ⟨g₀, ?_, ?_⟩
  · have h1 : ((d : ℤ) : S) * aeval y g₀ = 0 := by
      rw [hgd, map_mul] at hg
      simpa using hg
    exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hd0)
  · by_contra hall
    push_neg at hall
    obtain ⟨l, hl⟩ := (IsPrincipalIdealRing.principal I).principal
    have hdvd : l ∣ g.support.gcd b := Finset.dvd_gcd fun v hv => by
      have := hall v
      rw [hc v hv, hl] at this
      exact Ideal.mem_span_singleton.mp this
    rw [hgcd] at hdvd
    exact hI (by rw [hl]; exact Ideal.span_singleton_eq_top.mpr (isUnit_of_dvd_one hdvd))

theorem quasiFiniteAt_iff {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : Ideal S)
    [q.IsPrime] :
    f.QuasiFiniteAt q ↔ ((algebraMap S (Localization.AtPrime q)).comp f).QuasiFinite := by
  letI := f.toAlgebra
  have : f = algebraMap R S := rfl
  rw [this, ← IsScalarTower.algebraMap_eq R S (Localization.AtPrime q),
    RingHom.quasiFinite_algebraMap]

end GlobalTheory.NoetherInt

namespace GlobalTheory.NoetherInt

open MvPolynomial

theorem exists_quasiFiniteAt_of_not_injective {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    (q : Ideal S) [q.IsPrime] {n : ℕ} (y : Fin (n + 1) → S)
    (h : (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q)
    (hy : ¬ Function.Injective (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S)) :
    ∃ y' : Fin n → S, (aeval y' : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q := by

  obtain ⟨g, hg0, hg⟩ : ∃ g : MvPolynomial (Fin (n + 1)) ℤ, g ≠ 0 ∧ aeval y g = 0 := by
    rw [injective_iff_map_eq_zero] at hy
    push_neg at hy
    obtain ⟨g, h1, h2⟩ := hy
    exact ⟨g, h2, h1⟩
  let L := algebraMap S (Localization.AtPrime q)
  let K := IsLocalRing.ResidueField (Localization.AtPrime q)
  let res : Localization.AtPrime q →+* K := IsLocalRing.residue _
  let ι : ℤ →+* K := Int.castRingHom K
  obtain ⟨g₁, hg₁, v, hv⟩ := exists_primitive_of_aeval_eq_zero y g hg0 hg (RingHom.ker ι)
    (RingHom.ker_ne_top ι)
  have hne : MvPolynomial.map ι g₁ ≠ 0 := by
    intro h0
    apply hv
    have := congrArg (MvPolynomial.coeff v) h0
    rw [MvPolynomial.coeff_map] at this
    simpa [RingHom.mem_ker] using this
  obtain ⟨u, k, a, ha, hc⟩ := exists_coeff_map_eq_C ι g₁ hne

  let σ := shear ℤ n u
  let e := finSuccEquiv ℤ n
  let y₁ : Fin (n + 1) → S := fun i => aeval y (σ.symm (X i))
  have h1 : ∀ p, aeval y₁ p = aeval y (σ.symm p) := by
    intro p
    have : (aeval y₁ : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S) =
        (aeval y).comp (σ.symm : _ →ₐ[ℤ] _) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [y₁]
    exact DFunLike.congr_fun this p
  let y' : Fin n → S := fun i => y₁ i.succ
  let t := L (y₁ 0)
  let φ : MvPolynomial (Fin n) ℤ →+* Localization.AtPrime q :=
    L.comp (aeval y' : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S).toRingHom
  have key : ∀ p, Polynomial.eval₂ φ t (e p) = L (aeval y₁ p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [← Polynomial.coe_eval₂RingHom]
      simp only [eq_intCast, map_intCast]
    | add p r hp hr => simp [hp, hr, Polynomial.eval₂_add]
    | mul_X p i hp =>
      simp only [map_mul, Polynomial.eval₂_mul, hp]
      congr 1
      cases i using Fin.cases with
      | zero => simp [e, t, finSuccEquiv_X_zero]
      | succ i => simp [e, φ, y', finSuccEquiv_X_succ]
  let E : Polynomial (MvPolynomial (Fin n) ℤ) ≃+* MvPolynomial (Fin (n + 1)) ℤ :=
    (e.symm.trans σ.symm).toRingEquiv
  have hE : Polynomial.eval₂RingHom φ t =
      (L.comp (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S).toRingHom).comp E.toRingHom := by
    refine RingHom.ext fun p => ?_
    obtain ⟨p, rfl⟩ := e.surjective p
    rw [Polynomial.coe_eval₂RingHom, key, h1]
    simp [E]
  have hq : (Polynomial.eval₂RingHom φ t).QuasiFinite := by
    rw [hE]
    exact ((quasiFiniteAt_iff _ q).mp h).comp (RingHom.QuasiFinite.of_finite E.finite)
  have hG : Polynomial.eval₂ φ t (e (σ g₁)) = 0 := by
    rw [key, h1]; simp [hg₁]
  have hunit : IsUnit (φ ((e (σ g₁)).coeff k)) := by
    have hΦ : res.comp φ =
        (MvPolynomial.eval fun i => res (φ (X i))).comp (MvPolynomial.map ι) := by
      apply MvPolynomial.ringHom_ext
      · intro m; simp [ι]
      · intro i; simp
    have h2 : res (φ ((e (σ g₁)).coeff k)) = a := by
      have : res (φ ((e (σ g₁)).coeff k)) = MvPolynomial.eval (fun i => res (φ (X i)))
          (MvPolynomial.map ι ((e (σ g₁)).coeff k)) := DFunLike.congr_fun hΦ ((e (σ g₁)).coeff k)
      rw [this]
      simp only [e, σ]
      rw [hc]; simp
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (h2 ▸ ha)
  exact ⟨y', (quasiFiniteAt_iff _ q).mpr (quasiFinite_of_isUnit_coeff φ t hq _ hG k hunit)⟩

theorem exists_algebraicIndependent_of_quasiFiniteAt {S : Type*} [CommRing S] [IsDomain S]
    [CharZero S] (q : Ideal S) [q.IsPrime] (n : ℕ) :
    ∀ y : Fin n → S, (aeval y : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q →
    ∃ (r : ℕ) (y' : Fin r → S), AlgebraicIndependent ℤ y' ∧
      (aeval y' : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q := by
  induction n with
  | zero =>
    intro y h
    refine ⟨0, y, ?_, h⟩
    rw [algebraicIndependent_empty_type_iff]
    exact Int.cast_injective
  | succ n ih =>
    intro y h
    by_cases hy : Function.Injective (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S)
    · exact ⟨n + 1, y, hy, h⟩
    · obtain ⟨y', hy'⟩ := exists_quasiFiniteAt_of_not_injective q y h hy
      exact ih y' hy'

end GlobalTheory.NoetherInt

namespace GlobalTheory

open IsLocalRing

theorem exists_algebraicIndependent_int_quasiFiniteAt :
    ∀ (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra.FiniteType ℤ S] (𝔮 : Ideal S) [𝔮.IsPrime], ∃ (r : ℕ) (y : Fin r → S), AlgebraicIndependent ℤ y ∧ @Algebra.QuasiFiniteAt (MvPolynomial (Fin r) ℤ) S _ _ (MvPolynomial.aeval y : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.toAlgebra 𝔮 _ := by
  intro S _ _ _ hS 𝔮 _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hS
  have hfe : (MvPolynomial.aeval (fun i => f (MvPolynomial.X i)) :
      MvPolynomial (Fin n) ℤ →ₐ[ℤ] S) = f := by
    apply MvPolynomial.algHom_ext
    intro i; simp
  refine NoetherInt.exists_algebraicIndependent_of_quasiFiniteAt 𝔮 n
    (fun i => f (MvPolynomial.X i)) ?_
  rw [NoetherInt.quasiFiniteAt_iff, hfe]
  refine RingHom.QuasiFinite.comp ?_ (RingHom.QuasiFinite.of_finite
    (RingHom.Finite.of_surjective _ hf))
  exact RingHom.quasiFinite_algebraMap.2 (.of_isLocalization 𝔮.primeCompl)

end GlobalTheory
