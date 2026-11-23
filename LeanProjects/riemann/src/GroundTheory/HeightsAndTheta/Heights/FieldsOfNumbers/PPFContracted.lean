import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContractedDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace PFContracted

section Homog

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def blockDeg (k : K) : (Σ k, ι k) → ℕ := fun v => blockWeight ι v k

theorem weight_blockDeg (k : K) (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockDeg (ι := ι) k) d = Finsupp.weight (blockWeight ι) d k := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockDeg]

theorem isHomogeneous_iff {M : Type*} [AddCommMonoid M] [DecidableEq M] (w : (Σ k, ι k) → M)
    (I : Ideal (MRing ι F)) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F w) ↔
      ∀ (m : M), ∀ r ∈ I, weightedHomogeneousComponent w m r ∈ I := by
  constructor
  · intro h m r hr
    exact (mem_iff_weightedHomogeneousComponent_mem F w h r).mp hr m
  · intro h m r hr
    have := h m r hr
    rwa [← weightedDecomposition.decompose'_apply] at this

theorem component_blockDeg_of_isMultiHomog {p : MRing ι F} {b : K → ℕ} (hp : IsMultiHomog p b)
    (k : K) (n : ℕ) :
    weightedHomogeneousComponent (blockDeg k) n p = if b k = n then p else 0 := by
  ext d
  rw [coeff_weightedHomogeneousComponent, weight_blockDeg]
  by_cases hd : coeff d p = 0
  · split_ifs <;> simp [hd]
  · have hw : Finsupp.weight (blockWeight ι) d = b := hp hd
    rw [hw]
    split_ifs <;> simp

theorem blockDeg_component_mem {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) (k : K) (n : ℕ)
    {r : MRing ι F} (hr : r ∈ I) : weightedHomogeneousComponent (blockDeg k) n r ∈ I := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) r,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp r), map_sum]
  refine Ideal.sum_mem _ fun b _ => ?_
  rw [component_blockDeg_of_isMultiHomog (weightedHomogeneousComponent_isWeightedHomogeneous b r)]
  split_ifs
  · exact hI r hr b
  · exact I.zero_mem

theorem isMultiHomogIdeal_of_blockDeg [Fintype K] {I : Ideal (MRing ι F)}
    (h : ∀ (k : K) (n : ℕ), ∀ r ∈ I, weightedHomogeneousComponent (blockDeg k) n r ∈ I) :
    IsMultiHomogIdeal I := by
  classical
  intro r hr b
  let G : Finset K → MRing ι F := fun T =>
    ∑ d ∈ r.support.filter (fun d => ∀ k ∈ T, Finsupp.weight (blockWeight ι) d k = b k),
      monomial d (coeff d r)
  have hG : ∀ T d, coeff d (G T) =
      if ∀ k ∈ T, Finsupp.weight (blockWeight ι) d k = b k then coeff d r else 0 := by
    intro T d
    simp only [G, coeff_sum, coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter,
      mem_support_iff]
    by_cases hc : coeff d r = 0 <;> simp [hc]
  have hmem : ∀ T, G T ∈ I := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : G ∅ = r := by
        ext d
        rw [hG]
        simp
      rw [this]
      exact hr
    | insert k T hk ih =>
      have : G (insert k T) = weightedHomogeneousComponent (blockDeg k) (b k) (G T) := by
        ext d
        rw [hG, coeff_weightedHomogeneousComponent, hG, weight_blockDeg]
        simp only [Finset.forall_mem_insert, ite_and]
      rw [this]
      exact h k (b k) _ ih
  have : G Finset.univ = weightedHomogeneousComponent (blockWeight ι) b r := by
    ext d
    rw [hG, coeff_weightedHomogeneousComponent]
    by_cases hw : Finsupp.weight (blockWeight ι) d = b
    · simp [hw]
    · rw [if_neg hw, if_neg]
      exact fun h => hw (funext fun k => h k (Finset.mem_univ k))
  rw [← this]
  exact hmem _

theorem isMultiHomogIdeal_of_mem_minimalPrimes [Fintype K] {I W : Ideal (MRing ι F)}
    (hI : IsMultiHomogIdeal I) (hW : W ∈ I.minimalPrimes) : IsMultiHomogIdeal W := by
  refine isMultiHomogIdeal_of_blockDeg fun k n r hr => ?_
  have hIk : I.IsHomogeneous (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k)) :=
    (isHomogeneous_iff _ I).mpr fun n r hr => blockDeg_component_mem hI k n hr
  have hcore : (W.homogeneousCore
      (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k))).toIdeal.IsPrime :=
    hW.1.1.homogeneousCore
  have hle : I ≤ (W.homogeneousCore
      (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k))).toIdeal :=
    hIk.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  have heq : (W.homogeneousCore
      (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k))).toIdeal = W :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
      (hW.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _))
  have hWk : W.IsHomogeneous (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k)) := by
    rw [Ideal.IsHomogeneous.iff_eq]
    exact heq
  exact (isHomogeneous_iff _ W).mp hWk n r hr

theorem isMultiHomogIdeal_sup_span {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {f : MRing ι F} {c : K → ℕ} (hf : IsMultiHomog f c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {f}) := by
  classical
  have hI' : I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    (isHomogeneous_iff (blockWeight ι) I).mpr fun m r hr => hI r hr m
  have : (I ⊔ Ideal.span {f}).IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    hI'.sup (Ideal.homogeneous_span _ _ fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨c, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf⟩)
  intro r hr b
  exact (isHomogeneous_iff _ _).mp this b r hr

end Homog

section Dim

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem exists_ringKrullDim_eq [Fintype K] [∀ k, Fintype (ι k)] {Q : Ideal (MRing ι F)}
    [Q.IsPrime] (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q)
    (hrel : IsRelevant Q) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRing ι F ⧸ Q) = D := by
  have h1 := card_le_ringKrullDim hQ hrel
  have h2 := ringKrullDim_lt_top Q
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ringKrullDim (MRing ι F ⧸ Q) = D := by
    cases h : ringKrullDim (MRing ι F ⧸ Q) with
    | bot =>
      rw [h] at h1
      exact absurd h1 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        rw [h] at h2
        exact absurd h2 (by simp)
      | coe D => exact ⟨D, rfl⟩
  refine ⟨D, ?_, hD⟩
  rw [hD] at h1
  exact_mod_cast h1

theorem relDim_eq_int [Fintype K] {Q : Ideal (MRing ι F)} {D : ℕ}
    (hD : ringKrullDim (MRing ι F ⧸ Q) = D) :
    relDim Q = ((((D : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  rw [relDim, hD]
  rfl

theorem natCast_withBot_withTop (n : ℕ) :
    ((n : ℕ) : WithBot (WithTop ℤ)) = (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl

end Dim

section Contract

variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]

theorem rename_killBlocks (j : K ↪ K') (ι' : K' → Type*) (T : Finset K)
    (q : MRing (fun k => ι' (j k)) F) :
    rename (blockIncl j ι') (killBlocks T q) = killBlocks (T.map j) (rename (blockIncl j ι') q) := by
  have : (rename (blockIncl j ι')).comp (killBlocks (F := F) T) =
      (killBlocks (T.map j)).comp (rename (blockIncl j ι')) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rename_X, killBlocks_X, blockIncl, Finset.mem_map',
      apply_ite (rename (blockIncl j ι')), map_zero]
  exact AlgHom.congr_fun this q

theorem contractPrime_killStable (j : K ↪ K') (ι' : K' → Type*) {P' : Ideal (MRing ι' F)}
    (hP' : IsMultiHomogIdeal P') (T : Finset K) (q : MRing (fun k => ι' (j k)) F)
    (hq : q ∈ contractPrime j P') : killBlocks T q ∈ contractPrime j P' := by
  change rename (blockIncl j ι') (killBlocks T q) ∈ P'
  rw [rename_killBlocks]
  exact killBlocks_mem_of_isMultiHomogIdeal hP' _ hq

theorem contractPrime_isRelevant (j : K ↪ K') (ι' : K' → Type*) {P' : Ideal (MRing ι' F)}
    (h : IsRelevant P') : IsRelevant (contractPrime j P') := by
  intro k
  obtain ⟨i, hi⟩ := h (j k)
  refine ⟨i, ?_⟩
  change rename (blockIncl j ι') (X ⟨k, i⟩) ∉ P'
  rw [rename_X]
  exact hi

end Contract

theorem eventualValue_eq_zero {K : Type*} {f : (K → ℤ) → ℤ}
    (h : ∀ᶠ m in Filter.atTop, f m = 0) : eventualValue f = 0 := by
  unfold eventualValue
  split_ifs with hc
  · obtain ⟨m, h1, h2⟩ := (hc.choose_spec.and h).exists
    rw [← h1, h2]
  · rfl

section Main

variable (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]

def pullNat (e : K → ℕ) : K' → ℕ := ∑ κ, e κ • (Pi.single (j κ) 1 : K' → ℕ)

theorem pullNat_apply (e : K → ℕ) (k' : K') :
    (pullNat K K' j e k' : ℤ) = Function.extend j (fun κ => (e κ : ℤ)) 0 k' := by
  by_cases h : ∃ κ, j κ = k'
  · obtain ⟨κ, rfl⟩ := h
    rw [j.injective.extend_apply]
    simp [pullNat, Finset.sum_apply, Pi.single_apply, j.injective.eq_iff]
  · rw [Function.extend_apply' _ _ _ h]
    simp only [pullNat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [Finset.sum_eq_zero]
    · simp
    · intro κ _
      rw [if_neg (fun hk => h ⟨κ, hk.symm⟩), mul_zero]

theorem pullNat_sub (b : K → ℤ) :
    (fun k' => (pullNat K K' j (fun κ => (b κ).toNat) k' : ℤ) -
      pullNat K K' j (fun κ => (-b κ).toNat) k') = pullDeg j b := by
  funext k'
  rw [pullNat_apply, pullNat_apply, pullDeg]
  by_cases h : ∃ κ, j κ = k'
  · obtain ⟨κ, rfl⟩ := h
    rw [j.injective.extend_apply, j.injective.extend_apply, j.injective.extend_apply]
    exact Int.toNat_sub_toNat_neg (b κ)
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h,
      Function.extend_apply' _ _ _ h]
    simp

variable {F K K' j ι'}

def monoSmall (i : ∀ k', ι' k') (e : K → ℕ) : MRing (fun k => ι' (j k)) F :=
  ∏ κ, X ⟨κ, i (j κ)⟩ ^ e κ

theorem rename_monoSmall (i : ∀ k', ι' k') (e : K → ℕ) :
    rename (blockIncl j ι') (monoSmall (F := F) i e) = ∏ κ, X ⟨j κ, i (j κ)⟩ ^ e κ := by
  simp [monoSmall, map_prod, blockIncl]

theorem isMultiHomog_rename_monoSmall (i : ∀ k', ι' k') (e : K → ℕ) :
    IsMultiHomog (rename (blockIncl j ι') (monoSmall (F := F) i e)) (pullNat K K' j e) := by
  rw [rename_monoSmall]
  have := IsWeightedHomogeneous.prod Finset.univ
    (fun κ => (X ⟨j κ, i (j κ)⟩ : MRing ι' F) ^ e κ)
    (fun κ => e κ • blockWeight ι' ⟨j κ, i (j κ)⟩)
    (fun κ _ => (isWeightedHomogeneous_X F (blockWeight ι') _).pow (e κ))
  exact this

theorem key (h1 : MixedDiffConst.Statement.{u}) (h2 : CutRational.Statement.{u}) :
    ∀ (n : ℕ) (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ D D0 : ℕ,
      ringKrullDim (MRing ι' F ⧸ P') = D → D ≤ n + Fintype.card K' →
      ringKrullDim (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') = D0 →
      D0 < n + Fintype.card K →
      ∀ bs : Fin n → K → ℤ, intNum F P' (fun i => pullDeg j (bs i)) = 0 := by
  intro n
  induction n with
  | zero =>
    intro P' hP' D D0 _ _ hD0 hlt bs
    have := hP'.isPrime
    obtain ⟨D1, hc, hD1⟩ := exists_ringKrullDim_eq
      (contractPrime_killStable j ι' hP'.multiHomog) (contractPrime_isRelevant j ι' hP'.relevant)
    rw [hD0] at hD1
    have : D0 = D1 := by exact_mod_cast hD1
    omega
  | succ k ih =>
    intro P' hP' D D0 hD hDle hD0 hlt bs
    have := hP'.isPrime
    obtain ⟨D', hc', hD'⟩ := exists_ringKrullDim_eq
      (fun T q hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq) hP'.relevant
    rw [hD] at hD'
    have hDD : D = D' := by exact_mod_cast hD'
    subst hDD
    by_cases hlow : D - Fintype.card K' < k + 1
    · have hrel : relDim P' = ((D - Fintype.card K' : ℕ) : WithBot (WithTop ℤ)) := by
        rw [relDim_eq_int hD, natCast_withBot_withTop]
        congr 2
        omega
      exact eventualValue_eq_zero
        ((h1 F K' ι' P' hP'.multiHomog hP'.relevant _ hrel).2 (k + 1) hlow _)
    · have hrel : relDim P' = ((k + 1 : ℕ) : WithBot (WithTop ℤ)) := by
        rw [relDim_eq_int hD, natCast_withBot_withTop]
        congr 2
        omega
      choose i hi using hP'.relevant
      set b := bs (Fin.last k)
      set ep : K → ℕ := fun κ => (b κ).toNat
      set em : K → ℕ := fun κ => (-b κ).toNat
      have hnotmem : ∀ e : K → ℕ, rename (blockIncl j ι') (monoSmall (F := F) i e) ∉ P' := by
        intro e hmem
        rw [rename_monoSmall] at hmem
        obtain ⟨κ, -, hκ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP'.isPrime)).mp hmem
        exact hi (j κ) (hP'.isPrime.mem_of_pow_mem _ hκ)

      have hzero : ∀ (e : K → ℕ) (W : Ideal (MRing ι' F)),
          W ∈ (P' ⊔ Ideal.span {rename (blockIncl j ι') (monoSmall (F := F) i e)}).minimalPrimes →
          IsRelevant W → intNum F W (fun x : Fin k => pullDeg j (bs x.castSucc)) = 0 := by
        intro e W hmin hWrel
        have hWp : W.IsPrime := hmin.1.1
        have hWh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes
          (isMultiHomogIdeal_sup_span hP'.multiHomog (isMultiHomog_rename_monoSmall i e)) hmin
        have hPW : P' ≤ W := le_sup_left.trans hmin.1.2
        have hfW : rename (blockIncl j ι') (monoSmall (F := F) i e) ∈ W :=
          (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
        obtain ⟨DW, -, hDW⟩ := exists_ringKrullDim_eq
          (fun T q hq => killBlocks_mem_of_isMultiHomogIdeal hWh T hq) hWrel
        obtain ⟨DW0, -, hDW0⟩ := exists_ringKrullDim_eq
          (contractPrime_killStable j ι' hWh) (contractPrime_isRelevant j ι' hWrel)
        have hdrop := ringKrullDim_add_one_le hPW (hnotmem e) hfW
        rw [hDW, hD] at hdrop
        have hdrop' : DW + 1 ≤ D := by exact_mod_cast hdrop
        have hdrop0 := ringKrullDim_add_one_le (P := contractPrime j P') (Q := contractPrime j W)
          (Ideal.comap_mono hPW) (f := monoSmall i e) (hnotmem e) hfW
        rw [hDW0, hD0] at hdrop0
        have hdrop0' : DW0 + 1 ≤ D0 := by exact_mod_cast hdrop0
        exact ih W ⟨hWp, hWh, hWrel⟩ DW DW0 hDW (by omega) hDW0 (by omega) _
      have hsupp : ∀ (g : MRing ι' F) (W : Ideal (MRing ι' F)), divCycle P' g W ≠ 0 →
          W ∈ (P' ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W := by
        intro g W h
        unfold divCycle at h
        split_ifs at h with hc
        · exact hc
        · exact absurd rfl h
      have hcut := h2 F K' ι' P' hP' k hrel _ _ _ _ (isMultiHomog_rename_monoSmall i ep)
        (isMultiHomog_rename_monoSmall i em) (hnotmem ep) (hnotmem em)
        (fun x : Fin k => pullDeg j (bs x.castSucc))
      rw [pullNat_sub] at hcut
      have hsplit : (fun x => pullDeg j (bs x)) = Fin.snoc (α := fun _ => K' → ℤ)
          (fun x : Fin k => pullDeg j (bs x.castSucc)) (pullDeg j b) := by
        funext x
        refine Fin.lastCases ?_ (fun y => ?_) x
        · simp [b]
        · simp
      rw [hsplit, hcut]
      have hterm : ∀ W, ratDiv P' (rename (blockIncl j ι') (monoSmall (F := F) i ep))
          (rename (blockIncl j ι') (monoSmall (F := F) i em)) W *
            intNum F W (fun x : Fin k => pullDeg j (bs x.castSucc)) = 0 := by
        intro W
        by_cases hA : divCycle P' (rename (blockIncl j ι') (monoSmall (F := F) i ep)) W = 0
        · by_cases hB : divCycle P' (rename (blockIncl j ι') (monoSmall (F := F) i em)) W = 0
          · simp [ratDiv, hA, hB]
          · obtain ⟨hm, hr⟩ := hsupp _ W hB
            rw [hzero em W hm hr, mul_zero]
        · obtain ⟨hm, hr⟩ := hsupp _ W hA
          rw [hzero ep W hm hr, mul_zero]
      simp only [cycEval, hterm, finsum_zero]

end Main

end PFContracted

theorem PFContracted.proof (h1 : MixedDiffConst.Statement.{u}) (h2 : CutRational.Statement.{u}) :
    ProjectionFormulaContracted.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hrel hlt bs
  have := hP'.isPrime
  obtain ⟨D, -, hD⟩ := PFContracted.exists_ringKrullDim_eq
    (fun T q hq => PFContracted.killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq)
    hP'.relevant
  obtain ⟨D0, -, hD0⟩ := PFContracted.exists_ringKrullDim_eq
    (PFContracted.contractPrime_killStable j ι' hP'.multiHomog)
    (PFContracted.contractPrime_isRelevant j ι' hP'.relevant)
  rw [PFContracted.relDim_eq_int hD, PFContracted.natCast_withBot_withTop] at hrel
  rw [PFContracted.relDim_eq_int hD0, PFContracted.natCast_withBot_withTop] at hlt
  have e1 : (D : ℤ) - Fintype.card K' = n := WithTop.coe_inj.mp (WithBot.coe_inj.mp hrel)
  have e2 : (D0 : ℤ) - Fintype.card K < n := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hlt)
  exact PFContracted.key h1 h2 n P' hP' D D0 hD (by omega) hD0 (by omega) bs

end

end GroundTheory.Heights₂.Heights.FieldNumbers
