import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

namespace BlockSurjectivity

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

abbrev BlockRing (n : ι → ℕ) (k₀ : ι) : Type := MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ

def sepBlock (k₀ : ι) : MvPolynomial (Coord n) ℤ →ₐ[ℤ] MvPolynomial (Coord n) (BlockRing n k₀) :=
  aeval fun v ↦ if h : v.1 = k₀ then C (X ⟨(), Fin.cast (by rw [h]) v.2⟩) else X v

def joinBlock (k₀ : ι) : MvPolynomial (Coord n) (BlockRing n k₀) →+* MvPolynomial (Coord n) ℤ :=
  eval₂Hom (rename (blockIncl (n := n) k₀)).toRingHom X

omit [Fintype ι] in
theorem joinBlock_sepBlock (k₀ : ι) (q : MvPolynomial (Coord n) ℤ) :
    joinBlock k₀ (sepBlock k₀ q) = q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [sepBlock, joinBlock]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, hp]
    congr 1
    rcases v with ⟨k, i⟩
    by_cases h : k = k₀
    · subst h
      simp [sepBlock, joinBlock, blockIncl]
    · simp [sepBlock, joinBlock, h]

def evalBlock {k₀ : ι} (w : Cone (fun _ : Unit ↦ n k₀) ℂ) : BlockRing n k₀ →+* ℂ :=
  eval₂Hom (Int.castRingHom ℂ) fun v ↦ w v.1 v.2

omit [Fintype ι] [DecidableEq ι] in
theorem evalBlock_apply {k₀ : ι} (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (f : BlockRing n k₀) :
    evalBlock w f = evalCone w f := rfl

def atBlock (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) :
    MvPolynomial (Coord n) ℤ →+* MvPolynomial (Coord n) ℂ :=
  (map (evalBlock w)).comp (sepBlock k₀).toRingHom

omit [Fintype ι] in
theorem atBlock_apply (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (q : MvPolynomial (Coord n) ℤ) :
    atBlock k₀ w q = map (evalBlock w) (sepBlock k₀ q) := rfl

def withBlock (k₀ : ι) (w₀ : Fin (n k₀ + 1) → ℂ) (x : Coord n → ℂ) : Cone n ℂ :=
  Function.update (fun k (i : Fin (n k + 1)) ↦ x ⟨k, i⟩) k₀ w₀

omit [Fintype ι] in
theorem withBlock_self (k₀ : ι) (w₀ : Fin (n k₀ + 1) → ℂ) (x : Coord n → ℂ) :
    withBlock k₀ w₀ x k₀ = w₀ :=
  Function.update_self _ _ _

omit [Fintype ι] in
theorem withBlock_of_ne {k₀ k : ι} (h : k ≠ k₀) (w₀ : Fin (n k₀ + 1) → ℂ) (x : Coord n → ℂ) :
    withBlock k₀ w₀ x k = fun i ↦ x ⟨k, i⟩ :=
  Function.update_of_ne h _ _

omit [Fintype ι] in
theorem eval_atBlock_X (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (x : Coord n → ℂ) (v : Coord n) :
    eval x (atBlock k₀ w (X v)) = withBlock k₀ (w ()) x v.1 v.2 := by
  rcases v with ⟨k, i⟩
  by_cases h : k = k₀
  · subst h
    simp [atBlock, sepBlock, evalBlock, withBlock_self]
  · simp [atBlock, sepBlock, h, withBlock_of_ne h]

omit [Fintype ι] in
theorem eval_atBlock (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (x : Coord n → ℂ)
    (q : MvPolynomial (Coord n) ℤ) :
    eval x (atBlock k₀ w q) = evalCone (withBlock k₀ (w ()) x) q := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    simp only [evalCone, eval₂_C]
    simp [atBlock, sepBlock]
  | add p q hp hq =>
    rw [map_add (atBlock k₀ w), map_add (eval x), hp, hq]
    simp only [evalCone, eval₂_add]
  | mul_X p v hp =>
    rw [map_mul (atBlock k₀ w), map_mul (eval x), hp, eval_atBlock_X]
    simp only [evalCone, eval₂_mul, eval₂_X]

omit [Fintype ι] in

theorem isWeightedHomogeneous_sepBlock (k₀ : ι) {q : MvPolynomial (Coord n) ℤ} {m : ι → ℕ}
    (hq : IsWeightedHomogeneous (coordDeg n) q m) :
    IsWeightedHomogeneous (coordDeg n) (sepBlock k₀ q) (Function.update m k₀ 0) := by
  classical
  rw [q.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun ν hν ↦ ?_
  have hw : Finsupp.weight (coordDeg n) ν = m := hq (mem_support_iff.mp hν)
  have hvar : ∀ v : Coord n, IsWeightedHomogeneous (coordDeg n)
      ((if h : v.1 = k₀ then C (X ⟨(), Fin.cast (by rw [h]) v.2⟩) else X v :
        MvPolynomial (Coord n) (BlockRing n k₀))) (Function.update (coordDeg n v) k₀ 0) := by
    rintro ⟨k, i⟩
    by_cases h : k = k₀
    · subst h
      simp only [dite_true]
      convert isWeightedHomogeneous_C (coordDeg n) _ using 1
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [coordDeg, hj]
    · simp only [h, dite_false]
      convert isWeightedHomogeneous_X (BlockRing n k₀) (coordDeg n) (⟨k, i⟩ : Coord n) using 1
      funext j
      by_cases hj : j = k₀
      · subst hj; simp [coordDeg, Ne.symm h]
      · simp [Function.update_of_ne hj]
  have hc : IsWeightedHomogeneous (coordDeg n)
      (algebraMap ℤ (MvPolynomial (Coord n) (BlockRing n k₀)) (coeff ν q)) 0 := by
    rw [MvPolynomial.algebraMap_apply]
    exact isWeightedHomogeneous_C _ _
  rw [sepBlock, aeval_monomial, Finsupp.prod]
  convert hc.mul (IsWeightedHomogeneous.prod ν.support _
    (fun v ↦ ν v • Function.update (coordDeg n v) k₀ 0) fun v _ ↦ (hvar v).pow (ν v)) using 1
  rw [← hw, zero_add]
  funext j
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = k₀
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem weight_coordDeg_apply (μ : Coord n →₀ ℕ) (k : ι) :
    Finsupp.weight (coordDeg n) μ k = ∑ i, μ ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype μ (fun i c ↦ c • coordDeg n i) (fun _ ↦ zero_smul _ _), Finset.sum_apply,
    Fintype.sum_sigma]
  simp [coordDeg, Pi.single_apply]

theorem le_weight_coordDeg (μ : Coord n →₀ ℕ) (v : Coord n) :
    μ v ≤ Finsupp.weight (coordDeg n) μ v.1 := by
  rw [weight_coordDeg_apply]
  exact Finset.single_le_sum (f := fun i ↦ μ ⟨v.1, i⟩) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v.2)

def offDeg (k₀ : ι) (D : ℕ) : ι → ℕ := Function.update (fun _ ↦ D) k₀ 0

variable (n) in

def offMonos (k₀ : ι) (D : ℕ) : Finset (Coord n →₀ ℕ) :=
  (Finset.finsuppAntidiag Finset.univ (∑ k, offDeg k₀ D k)).filter
    fun μ ↦ Finsupp.weight (coordDeg n) μ = offDeg k₀ D

theorem mem_offMonos {k₀ : ι} {D : ℕ} {μ : Coord n →₀ ℕ} :
    μ ∈ offMonos n k₀ D ↔ Finsupp.weight (coordDeg n) μ = offDeg k₀ D := by
  simp only [offMonos, Finset.mem_filter, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rw [← h]
  simp only [weight_coordDeg_apply]
  rw [Fintype.sum_sigma]

def fibreIdeal (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) :
    Ideal (MvPolynomial (Coord n) ℂ) :=
  Ideal.span (atBlock k₀ w '' P.ideal)

def coeffVec (M : Finset (Coord n →₀ ℕ)) : MvPolynomial (Coord n) ℂ →ₗ[ℂ] (M → ℂ) :=
  LinearMap.pi fun μ ↦ lcoeff ℂ μ.1

omit [Fintype ι] [DecidableEq ι] in
theorem coeffVec_apply (M : Finset (Coord n →₀ ℕ)) (g : MvPolynomial (Coord n) ℂ) (μ : M) :
    coeffVec M g μ = coeff μ.1 g := rfl

variable (n) in

def homogIn (P : ArithVariety n) (k₀ : ι) (D : ℕ) : Set (MvPolynomial (Coord n) ℤ) :=
  {q | q ∈ P.ideal ∧ IsWeightedHomogeneous (coordDeg n) (sepBlock k₀ q) (offDeg k₀ D)}

theorem exists_pow_prod_mem (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ)
    (hw0 : w () ≠ 0) (hno : ∀ z ∈ P.points ℂ, z k₀ ≠ w ()) :
    ∃ N : ℕ, ∀ c : (k : ι) → Fin (n k + 1),
      (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ^ N ∈ fibreIdeal P k₀ w := by
  classical
  have hprod : ∀ c : (k : ι) → Fin (n k + 1), ∃ N : ℕ,
      (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ^ N ∈ fibreIdeal P k₀ w := by
    intro c
    have hmem : (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ∈
        vanishingIdeal ℂ (zeroLocus ℂ (fibreIdeal P k₀ w)) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [aeval_eq_eval, eval_prod]
      by_contra hne
      rw [Finset.prod_eq_zero_iff] at hne
      push Not at hne
      refine hno (withBlock k₀ (w ()) x) ⟨fun k ↦ ?_, fun f hf ↦ ?_⟩ (withBlock_self _ _ _)
      · by_cases h : k = k₀
        · subst h
          rw [withBlock_self]
          exact hw0
        · rw [withBlock_of_ne h]
          intro h0
          exact hne k (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩) (by simpa using congrFun h0 (c k))
      · have h0 := (mem_zeroLocus_iff.mp hx) _ (Ideal.subset_span ⟨f, hf, rfl⟩)
        rw [aeval_eq_eval, eval_atBlock] at h0
        exact h0
    rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
    exact hmem
  choose Nc hNc using hprod
  refine ⟨∑ c, Nc c, fun c ↦ ?_⟩
  have hle : Nc c ≤ ∑ c, Nc c := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c)
  rw [← Nat.sub_add_cancel hle, pow_add]
  exact Ideal.mul_mem_left _ _ (hNc c)

theorem monomial_mem_of_pow_prod_mem {J : Ideal (MvPolynomial (Coord n) ℂ)} {k₀ : ι} {N : ℕ}
    (hJN : ∀ c : (k : ι) → Fin (n k + 1),
      (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ^ N ∈ J) :
    ∀ μ ∈ offMonos n k₀ (Fintype.card (Coord n) * N), (monomial μ 1 : MvPolynomial (Coord n) ℂ) ∈ J := by
  classical
  intro μ hμ
  rw [mem_offMonos] at hμ
  have hbig : ∀ k, ∃ i : Fin (n k + 1), k ≠ k₀ → N ≤ μ ⟨k, i⟩ := by
    intro k
    by_cases hk : k = k₀
    · exact ⟨0, fun h ↦ (h hk).elim⟩
    · by_contra hcon
      push Not at hcon
      have hsum : ∑ i, μ ⟨k, i⟩ = Fintype.card (Coord n) * N := by
        rw [← weight_coordDeg_apply, hμ, offDeg, Function.update_of_ne hk]
      have hlt : ∑ i, μ ⟨k, i⟩ < ∑ _i : Fin (n k + 1), N :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦ (hcon i).2
      have hcard : n k + 1 ≤ Fintype.card (Coord n) := by
        rw [Fintype.card_sigma]
        simp only [Fintype.card_fin]
        exact Finset.single_le_sum (f := fun k ↦ n k + 1) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
      rw [hsum] at hlt
      exact absurd hlt (not_lt.mpr (Nat.mul_le_mul_right N hcard))
  choose c hc using hbig
  have hinj : Set.InjOn (fun k ↦ (⟨k, c k⟩ : Coord n)) (Finset.univ.erase k₀) :=
    fun a _ b _ h ↦ congrArg Sigma.fst h
  have hdvd : (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ^ N ∣
      monomial μ 1 := by
    rw [← Finset.prod_pow]
    calc ∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ) ^ N
        ∣ ∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ) ^ μ ⟨k, c k⟩ :=
          Finset.prod_dvd_prod_of_dvd _ _ fun k hk ↦
            pow_dvd_pow _ (hc k (Finset.ne_of_mem_erase hk))
      _ = ∏ v ∈ (Finset.univ.erase k₀).image (fun k ↦ (⟨k, c k⟩ : Coord n)),
            (X v : MvPolynomial (Coord n) ℂ) ^ μ v := by
          rw [Finset.prod_image hinj]
      _ ∣ ∏ v, (X v : MvPolynomial (Coord n) ℂ) ^ μ v :=
          Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
      _ = monomial μ 1 := by
          rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  obtain ⟨r, hr⟩ := hdvd
  rw [hr]
  exact J.mul_mem_right _ (hJN c)

theorem coeffVec_atBlock_mem (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (D : ℕ)
    {p : MvPolynomial (Coord n) ℤ} (hp : p ∈ P.ideal) :
    coeffVec (offMonos n k₀ D) (atBlock k₀ w p) ∈
      Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D) := by
  classical
  have hp' := finsum_weightedHomogeneousComponent (coordDeg n) p
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p)] at hp'
  rw [← hp', map_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ ↦ ?_
  have hqP : weightedHomogeneousComponent (coordDeg n) m p ∈ P.ideal := P.homogeneous p hp m
  have hqh := isWeightedHomogeneous_sepBlock k₀
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := coordDeg n) m p)
  by_cases hm : Function.update m k₀ 0 = offDeg k₀ D
  · exact Submodule.subset_span ⟨_, ⟨hqP, hm ▸ hqh⟩, rfl⟩
  · have h0 : coeffVec (offMonos n k₀ D) (atBlock k₀ w (weightedHomogeneousComponent (coordDeg n) m p))
        = 0 := by
      funext μ
      rw [coeffVec_apply, atBlock_apply, coeff_map]
      have hμ := mem_offMonos.mp μ.2
      rw [hqh.coeff_eq_zero μ.1 (by rw [hμ]; exact Ne.symm hm), map_zero]
      rfl
    rw [h0]
    exact Submodule.zero_mem _

theorem coeffVec_mul_atBlock_mem (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ)
    (D : ℕ) (h : MvPolynomial (Coord n) ℂ) :
    ∀ p ∈ P.ideal, coeffVec (offMonos n k₀ D) (h * atBlock k₀ w p) ∈
      Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D) := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a =>
    intro p hp
    rw [C_mul', map_smul]
    exact Submodule.smul_mem _ a (coeffVec_atBlock_mem P k₀ w D hp)
  | add f g hf hg =>
    intro p hp
    rw [add_mul, map_add]
    exact Submodule.add_mem _ (hf p hp) (hg p hp)
  | mul_X f v hf =>
    intro p hp
    by_cases hv : v.1 = k₀
    · have h0 : coeffVec (offMonos n k₀ D) (f * X v * atBlock k₀ w p) = 0 := by
        funext μ
        rw [coeffVec_apply, mul_right_comm, coeff_mul_X']
        have hμ := mem_offMonos.mp μ.2
        have hμv : μ.1 v = 0 := by
          have := le_weight_coordDeg μ.1 v
          rw [hμ, hv, offDeg, Function.update_self] at this
          exact Nat.le_zero.mp this
        rw [if_neg (by simpa [Finsupp.mem_support_iff] using hμv)]
        rfl
      rw [h0]
      exact Submodule.zero_mem _
    · have hX : atBlock k₀ w (X v) = X v := by simp [atBlock_apply, sepBlock, hv]
      rw [mul_assoc, ← hX, ← map_mul]
      exact hf _ (P.ideal.mul_mem_left _ hp)

theorem coeffVec_mem_span (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (D : ℕ)
    {g : MvPolynomial (Coord n) ℂ} (hg : g ∈ fibreIdeal P k₀ w) :
    coeffVec (offMonos n k₀ D) g ∈
      Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D) := by
  have key : ∀ h : MvPolynomial (Coord n) ℂ, coeffVec (offMonos n k₀ D) (h * g) ∈
      Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D) := by
    refine Submodule.span_induction (p := fun g _ ↦ ∀ h : MvPolynomial (Coord n) ℂ,
      coeffVec (offMonos n k₀ D) (h * g) ∈
        Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D))
      ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨p, hp, rfl⟩ h
      exact coeffVec_mul_atBlock_mem P k₀ w D h p hp
    · intro h
      rw [mul_zero, map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy h
      rw [mul_add, map_add]
      exact Submodule.add_mem _ (hx h) (hy h)
    · intro a x _ hx h
      rw [smul_eq_mul, ← mul_assoc]
      exact hx (h * a)
  simpa using key 1

theorem det_mem_projIdeal (P : ArithVariety n) (k₀ : ι) (D : ℕ)
    (q : offMonos n k₀ D → MvPolynomial (Coord n) ℤ) (hq : ∀ i, q i ∈ homogIn n P k₀ D) :
    (Matrix.of fun i (μ : offMonos n k₀ D) ↦ coeff μ.1 (sepBlock k₀ (q i))).det ∈ P.projIdeal k₀ := by
  classical
  let Bm : Matrix (offMonos n k₀ D) (offMonos n k₀ D) (BlockRing n k₀) := Matrix.of fun i μ ↦ coeff μ.1 (sepBlock k₀ (q i))
  have hsupp : ∀ i, (sepBlock k₀ (q i)).support ⊆ offMonos n k₀ D := fun i ν hν ↦
    mem_offMonos.mpr ((hq i).2 (MvPolynomial.mem_support_iff.mp hν))
  have hexp : ∀ i, q i = ∑ μ : offMonos n k₀ D, rename (blockIncl k₀) (Bm i μ) * monomial μ.1 1 := by
    intro i
    conv_lhs => rw [← joinBlock_sepBlock k₀ (q i), (sepBlock k₀ (q i)).as_sum, map_sum]
    rw [Finset.sum_subset (hsupp i) ?_, ← Finset.sum_coe_sort (offMonos n k₀ D)]
    · refine Finset.sum_congr rfl fun μ _ ↦ ?_
      rw [joinBlock, coe_eval₂Hom, eval₂_monomial, monomial_eq, C_1, one_mul]
      rfl
    · intro ν _ hν
      rw [notMem_support_iff.mp hν, monomial_zero, map_zero]
  let f : BlockRing n k₀ →+* MvPolynomial (Coord n) ℤ := (rename (blockIncl (n := n) k₀)).toRingHom
  let rB : Matrix (offMonos n k₀ D) (offMonos n k₀ D) (MvPolynomial (Coord n) ℤ) := f.mapMatrix Bm
  let xv : offMonos n k₀ D → MvPolynomial (Coord n) ℤ := fun μ ↦ monomial μ.1 1
  have hmv : Matrix.mulVec rB xv = q := by
    funext i
    rw [hexp i]
    simp [rB, xv, f, Matrix.mulVec, dotProduct]
  have hcr : ∀ μ : offMonos n k₀ D, rB.det * xv μ ∈ P.ideal := by
    intro μ
    have h1 : Matrix.mulVec rB.adjugate (Matrix.mulVec rB xv) = rB.det • xv := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 := congrFun h1 μ
    rw [hmv, Pi.smul_apply, smul_eq_mul] at h2
    rw [← h2]
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ ↦ P.ideal.mul_mem_left _ (hq j).1
  choose r hr using P.relevant
  let μs : Coord n →₀ ℕ := ∑ k ∈ Finset.univ.erase k₀, Finsupp.single ⟨k, r k⟩ D
  have hμs : μs ∈ offMonos n k₀ D := by
    rw [mem_offMonos, map_sum]
    funext j
    rw [Finset.sum_apply]
    simp only [Finsupp.weight_single, coordDeg, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, offDeg]
    rw [Finset.sum_ite_eq]
    by_cases hj : j = k₀
    · subst hj; simp
    · simp [hj]
  have hxs : xv ⟨μs, hμs⟩ ∉ P.ideal := by
    have := P.isPrime
    simp only [xv, μs]
    rw [monomial_sum_one, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, _, hk⟩
    rw [← X_pow_eq_monomial] at hk
    exact hr k (P.isPrime.mem_of_pow_mem _ hk)
  have hdetP : rB.det ∈ P.ideal := (P.isPrime.mem_or_mem (hcr ⟨μs, hμs⟩)).resolve_right hxs
  have h : f Bm.det = rB.det := RingHom.map_det f Bm
  rw [← h] at hdetP
  exact Ideal.mem_comap.mpr hdetP

theorem exists_point_over (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ)
    (hw : w ∈ conePoints (P.projIdeal k₀) ℂ) : ∃ z ∈ P.points ℂ, z k₀ = w () := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨N, hJN⟩ := exists_pow_prod_mem P k₀ w (hw.1 ()) hno
  have hmono := monomial_mem_of_pow_prod_mem hJN
  generalize hD : Fintype.card (Coord n) * N = D at hmono
  have hWtop : Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) ''
      homogIn n P k₀ D) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℂ (offMonos n k₀ D)).span_eq, Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    have h1 : coeffVec (offMonos n k₀ D) (monomial μ.1 1) = Pi.basisFun ℂ (offMonos n k₀ D) μ := by
      funext ν
      rw [coeffVec_apply, coeff_monomial, Pi.basisFun_apply, Pi.single_apply]
      by_cases h : μ = ν
      · subst h; simp
      · rw [if_neg (fun h' ↦ h (Subtype.ext h')), if_neg (Ne.symm h)]
    rw [← h1]
    exact coeffVec_mem_span P k₀ w D (hmono μ.1 μ.2)
  obtain ⟨b, hbV, hbspan, hbli⟩ :=
    exists_linearIndependent ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D)
  let B : Basis b ℂ (offMonos n k₀ D → ℂ) := Basis.mk hbli (by rw [Subtype.range_coe, hbspan]; exact hWtop.ge)
  let e := (Pi.basisFun ℂ (offMonos n k₀ D)).indexEquiv B
  have hsel : ∀ i : offMonos n k₀ D, ∃ q ∈ homogIn n P k₀ D, coeffVec (offMonos n k₀ D) (atBlock k₀ w q) = (e i : offMonos n k₀ D → ℂ) := by
    intro i
    obtain ⟨q, hq, hqe⟩ := hbV (e i).2
    exact ⟨q, hq, hqe⟩
  choose q hqS hqe using hsel
  have hdet : evalBlock w (Matrix.of fun i (μ : offMonos n k₀ D) ↦ coeff μ.1 (sepBlock k₀ (q i))).det ≠ 0 := by
    rw [RingHom.map_det]
    have hrows : (evalBlock w).mapMatrix (Matrix.of fun i (μ : offMonos n k₀ D) ↦ coeff μ.1 (sepBlock k₀ (q i))) =
        Matrix.of fun i ↦ (e i : offMonos n k₀ D → ℂ) := by
      ext i μ
      show evalBlock w (coeff μ.1 (sepBlock k₀ (q i))) = (e i : offMonos n k₀ D → ℂ) μ
      rw [← hqe i, coeffVec_apply, atBlock_apply, coeff_map]
    rw [hrows]
    have hli : LinearIndependent ℂ (Matrix.of fun i ↦ (e i : offMonos n k₀ D → ℂ)).row := hbli.comp e e.injective
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli)).ne_zero
  rw [evalBlock_apply] at hdet
  exact hdet (hw.2 _ (det_mem_projIdeal P k₀ D q hqS))

end BlockSurjectivity

theorem BlockSurjectivity.proof : BlockSurjectivity.Statement := by
  intro ι _ _ n P k₀
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨fun _ ↦ hz.1 k₀, fun f hf ↦ ?_⟩
    have h := hz.2 _ (Ideal.mem_comap.mp hf)
    simp only [evalCone, eval₂_rename] at h
    exact h
  · intro hw
    obtain ⟨z, hz, hzw⟩ := BlockSurjectivity.exists_point_over P k₀ w hw
    exact ⟨z, hz, funext fun u ↦ by cases u; exact hzw⟩

end

end GroundTheory.Heights₂.Heights
