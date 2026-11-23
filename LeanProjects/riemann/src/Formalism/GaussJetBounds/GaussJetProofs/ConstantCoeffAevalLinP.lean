import Formalism.GaussJetBounds.StatementJ
import Formalism.GaussJetBounds.GaussJetProofs.ThmAOp

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

section JetPair

variable {K : Type u} [Field K] {ι : Type}

lemma jetPair_eq_sum (P : MvPolynomial ι K) (F : MvPowerSeries ι K) (S : Finset (ι →₀ ℕ))
    (hS : P.support ⊆ S) :
    jetPair P F =
      ∑ κ ∈ S, MvPolynomial.coeff κ P * ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F := by
  classical
  unfold jetPair
  refine Finset.sum_subset hS ?_
  intro κ _ hκ
  have h0 : MvPolynomial.coeff κ P = 0 := by simpa [MvPolynomial.mem_support_iff] using hκ
  simp [h0]

lemma jetPair_add_left (P Q : MvPolynomial ι K) (F : MvPowerSeries ι K) :
    jetPair (P + Q) F = jetPair P F + jetPair Q F := by
  classical
  rw [jetPair_eq_sum (P + Q) F (P.support ∪ Q.support) MvPolynomial.support_add,
    jetPair_eq_sum P F (P.support ∪ Q.support) Finset.subset_union_left,
    jetPair_eq_sum Q F (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  rw [MvPolynomial.coeff_add]
  ring

lemma jetPair_zero_left (F : MvPowerSeries ι K) : jetPair (0 : MvPolynomial ι K) F = 0 := by
  simp [jetPair]

lemma jetPair_C_mul_left (c : K) (P : MvPolynomial ι K) (F : MvPowerSeries ι K) :
    jetPair (MvPolynomial.C c * P) F = c * jetPair P F := by
  classical
  rw [jetPair_eq_sum (MvPolynomial.C c * P) F P.support, jetPair, Finset.mul_sum]
  · refine Finset.sum_congr rfl (fun κ _ => ?_)
    rw [MvPolynomial.coeff_C_mul]
    ring
  · intro κ hκ
    rw [MvPolynomial.mem_support_iff] at hκ ⊢
    rw [MvPolynomial.coeff_C_mul] at hκ
    exact right_ne_zero_of_mul hκ

lemma jetPair_sum_left {α : Type*} (s : Finset α) (P : α → MvPolynomial ι K)
    (F : MvPowerSeries ι K) : jetPair (∑ a ∈ s, P a) F = ∑ a ∈ s, jetPair (P a) F := by
  classical
  refine Finset.induction_on s (by simp [jetPair_zero_left]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, jetPair_add_left, ih]

lemma jetPair_add_right (P : MvPolynomial ι K) (F G : MvPowerSeries ι K) :
    jetPair P (F + G) = jetPair P F + jetPair P G := by
  simp only [jetPair, map_add, mul_add, Finset.sum_add_distrib]

lemma jetPair_C_mul_right (c : K) (P : MvPolynomial ι K) (F : MvPowerSeries ι K) :
    jetPair P (MvPowerSeries.C c * F) = c * jetPair P F := by
  simp only [jetPair, MvPowerSeries.coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  ring

lemma jetPair_sum_right {α : Type*} (s : Finset α) (P : MvPolynomial ι K)
    (F : α → MvPowerSeries ι K) : jetPair P (∑ a ∈ s, F a) = ∑ a ∈ s, jetPair P (F a) := by
  simp only [jetPair, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

lemma jetPair_C_left (c : K) (F : MvPowerSeries ι K) :
    jetPair (MvPolynomial.C c) F = c * MvPowerSeries.constantCoeff F := by
  classical
  rw [jetPair_eq_sum (MvPolynomial.C c) F {0}]
  · simp [mfact, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro κ hκ
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hκ
    rw [Finset.mem_singleton]
    by_contra h
    exact hκ (if_neg (fun h' => h h'.symm))

lemma mfact_add_single (κ : ι →₀ ℕ) (i : ι) :
    mfact (κ + Finsupp.single i 1) = mfact κ * (κ i + 1) := by
  classical
  unfold mfact
  have key : ∀ (μ : ι →₀ ℕ) (s : Finset ι), μ.support ⊆ s →
      (μ.prod fun _ k => k.factorial) = ∏ j ∈ s, (μ j).factorial :=
    fun μ s h => Finsupp.prod_of_support_subset μ h (fun _ k => k.factorial)
      (fun _ _ => Nat.factorial_zero)
  have h1 : κ.support ⊆ insert i (κ.support.erase i) :=
    Finset.subset_insert_iff.mpr (Finset.Subset.refl _)
  have hsub : (κ + Finsupp.single i 1).support ⊆ insert i (κ.support.erase i) := by
    intro j hj
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply] at hj
    by_cases h : i = j
    · rw [← h]; exact Finset.mem_insert_self _ _
    · rw [if_neg h, add_zero] at hj
      exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Ne.symm h, Finsupp.mem_support_iff.mpr hj⟩)
  have hnot : i ∉ κ.support.erase i := by simp
  rw [key κ _ h1, key _ _ hsub, Finset.prod_insert hnot, Finset.prod_insert hnot]
  have hrest : ∏ j ∈ κ.support.erase i, ((κ + Finsupp.single i 1 : ι →₀ ℕ) j).factorial =
      ∏ j ∈ κ.support.erase i, (κ j).factorial := by
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finsupp.add_apply, Finsupp.single_apply,
      if_neg (fun h => (Finset.ne_of_mem_erase hj) h.symm), add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

lemma jetPair_mul_X (P : MvPolynomial ι K) (i : ι) (F : MvPowerSeries ι K) :
    jetPair (P * MvPolynomial.X i) F = jetPair P (MvPowerSeries.pderiv K i F) := by
  classical
  rw [jetPair, MvPolynomial.support_mul_X, Finset.sum_map, jetPair]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  simp only [addRightEmbedding_apply, MvPolynomial.coeff_mul_X, mfact_add_single,
    MvPowerSeries.coeff_pderiv]
  push_cast
  ring

end JetPair

section Chain

variable {K : Type u} [Field K] {ι ι' : Type} [Fintype ι] [Fintype ι']

def linP (A : ι → ι' → K) (j : ι') : MvPolynomial ι K :=
  ∑ i : ι, MvPolynomial.C (A i j) * MvPolynomial.X i

lemma pderiv_linP (A : ι → ι' → K) (i : ι) (j : ι') :
    MvPolynomial.pderiv i (linP A j) = MvPolynomial.C (A i j) := by
  classical
  simp [linP, MvPolynomial.pderiv_X, Pi.single_apply]

lemma pderiv_aeval_linP (A : ι → ι' → K) (i : ι) (G : MvPolynomial ι' K) :
    MvPolynomial.pderiv i (MvPolynomial.aeval (linP A) G) =
      ∑ j, MvPolynomial.C (A i j) * MvPolynomial.aeval (linP A) (MvPolynomial.pderiv j G) := by
  classical
  induction G using MvPolynomial.induction_on
  · simp
  · rename_i p q hp hq
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  · rename_i p j hp
    have hk : ∀ k : ι', MvPolynomial.aeval (linP A) (MvPolynomial.pderiv k (p * MvPolynomial.X j)) =
        MvPolynomial.aeval (linP A) p * (if j = k then 1 else 0) +
          linP A j * MvPolynomial.aeval (linP A) (MvPolynomial.pderiv k p) := by
      intro k
      rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul,
        map_mul, MvPolynomial.aeval_X, Pi.single_apply]
      split_ifs <;> simp
    simp only [hk, mul_add, Finset.sum_add_distrib]
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, pderiv_linP, hp, smul_eq_mul, smul_eq_mul]
    have h1 : ∑ k : ι', MvPolynomial.C (A i k) *
        (MvPolynomial.aeval (linP A) p * (if j = k then 1 else 0)) =
        MvPolynomial.aeval (linP A) p * MvPolynomial.C (A i j) := by
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [if_neg (Ne.symm hk)]; ring)
        (fun h => absurd (Finset.mem_univ j) h), if_pos rfl]
      ring
    rw [h1, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring

def linP' (A : ι → ι' → K) (i : ι) : MvPolynomial ι' K :=
  ∑ j : ι', MvPolynomial.C (A i j) * MvPolynomial.X j

lemma constantCoeff_aeval_linP (A : ι → ι' → K) (G : MvPolynomial ι' K) :
    MvPolynomial.constantCoeff (MvPolynomial.aeval (linP A) G) = MvPolynomial.constantCoeff G := by
  induction G using MvPolynomial.induction_on
  · simp
  · rename_i p q hp hq
    simp only [map_add, hp, hq]
  · rename_i p j hp
    simp only [map_mul, MvPolynomial.aeval_X, hp, MvPolynomial.constantCoeff_X, mul_zero]
    simp [linP]

private theorem mvPowerSeries_pderiv_coe_eq_coe_pderiv {L : Type u} [Field L] {σ : Type} (i : σ)
    (G : MvPolynomial σ L) :
    MvPowerSeries.pderiv L i (G : MvPowerSeries σ L) =
      ((MvPolynomial.pderiv i G : MvPolynomial σ L) : MvPowerSeries σ L) := by
  ext n
  rw [MvPowerSeries.coeff_pderiv, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_pderiv]

lemma jetPair_poly (A : ι → ι' → K) (P : MvPolynomial ι K) :
    ∀ G : MvPolynomial ι' K,
      jetPair P ((MvPolynomial.aeval (linP A) G : MvPolynomial ι K) : MvPowerSeries ι K) =
        jetPair (MvPolynomial.aeval (linP' A) P) (G : MvPowerSeries ι' K) := by
  classical
  induction P using MvPolynomial.induction_on
  · rename_i c
    intro G
    rw [jetPair_C_left, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, jetPair_C_left]
    congr 1
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      MvPolynomial.coeff_coe]
    have h := constantCoeff_aeval_linP A G
    first
    | exact h
    | simpa [MvPolynomial.constantCoeff_eq] using h
  · rename_i P Q hP hQ
    intro G
    rw [jetPair_add_left, hP, hQ, map_add, jetPair_add_left]
  · rename_i P i hP
    intro G
    have hsum : ∀ (f : ι' → MvPolynomial ι K),
        ((∑ j, f j : MvPolynomial ι K) : MvPowerSeries ι K) = ∑ j, (f j : MvPowerSeries ι K) := by
      intro f
      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
      simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
    rw [jetPair_mul_X, mvPowerSeries_pderiv_coe_eq_coe_pderiv, pderiv_aeval_linP, hsum, jetPair_sum_right]
    rw [map_mul, MvPolynomial.aeval_X]
    rw [linP']
    rw [Finset.mul_sum, jetPair_sum_left]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_C, jetPair_C_mul_right, hP,
      show MvPolynomial.aeval (linP' A) P * (MvPolynomial.C (A i j) * MvPolynomial.X j) =
        MvPolynomial.C (A i j) * (MvPolynomial.aeval (linP' A) P * MvPolynomial.X j) by ring,
      jetPair_C_mul_left, jetPair_mul_X, mvPowerSeries_pderiv_coe_eq_coe_pderiv]

lemma jetPair_monomial_right (P : MvPolynomial ι' K) (μ : ι' →₀ ℕ) :
    jetPair P ((MvPolynomial.monomial μ (1 : K) : MvPolynomial ι' K) : MvPowerSeries ι' K) =
      MvPolynomial.coeff μ P * ((mfact μ : ℕ) : K) := by
  classical
  rw [jetPair_eq_sum P _ (insert μ P.support) (Finset.subset_insert _ _), Finset.sum_eq_single μ]
  · simp [MvPolynomial.coeff_coe]
  · intro κ _ hκ
    rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_monomial, if_neg (Ne.symm hκ), mul_zero]
  · intro h
    exact absurd (Finset.mem_insert_self μ _) h

theorem jet_pair_linearity : JetPairLin.{u} := by
  classical
  intro K _ ι ι' _ _ A P F
  set a : ι' → MvPowerSeries ι K :=
    fun j => ∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i with ha
  have ha0 : ∀ j, MvPowerSeries.constantCoeff (a j) = 0 := fun j => by simp [ha]
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hcoe : ∀ j, a j = ((linP A j : MvPolynomial ι K) : MvPowerSeries ι K) := fun j => by
    rw [ha, linP, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    simp
  have hmon : ∀ μ : ι' →₀ ℕ, (μ.prod fun s e => a s ^ e) =
      ((MvPolynomial.aeval (linP A) (MvPolynomial.monomial μ (1 : K)) : MvPolynomial ι K) :
        MvPowerSeries ι K) := fun μ => by
    rw [MvPolynomial.aeval_monomial, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_mul,
      Finsupp.prod, Finsupp.prod, map_prod]
    simp [hcoe]
  change jetPair P (MvPowerSeries.subst a F) = jetPair (MvPolynomial.aeval (linP' A) P) F
  set P' := MvPolynomial.aeval (linP' A) P with hP'
  have hfin := fun κ => MvPowerSeries.coeff_subst_finite hs F κ
  set T : Finset (ι' →₀ ℕ) := (P.support.biUnion fun κ => (hfin κ).toFinset) ∪ P'.support with hT
  rw [jetPair_eq_sum P' F T Finset.subset_union_right]
  have h1 : ∀ κ ∈ P.support, MvPowerSeries.coeff κ (MvPowerSeries.subst a F) =
      ∑ μ ∈ T, MvPowerSeries.coeff μ F * MvPowerSeries.coeff κ (μ.prod fun s e => a s ^ e) := by
    intro κ hκ
    rw [MvPowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset]
    · rfl
    · intro μ hμ
      rw [hT, Finset.coe_union]
      left
      rw [Finset.coe_biUnion]
      exact Set.mem_biUnion hκ (by simpa using hμ)
  unfold jetPair
  rw [Finset.sum_congr rfl fun κ hκ => by rw [h1 κ hκ, Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h2 := jetPair_poly A P (MvPolynomial.monomial μ (1 : K))
  rw [jetPair_monomial_right, ← hmon] at h2
  rw [← hP'] at h2
  rw [← h2]
  unfold jetPair
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun κ _ => ?_
  ring

end Chain

section Frames

lemma subst_linSub {K : Type u} [Field K] {d N0 N1 : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι']
    (M : ZV d N0 N1 → ι' → K) (A : ι → ι' → K) (Mg : ZV d N0 N1 → ι → K)
    (h : ∀ z i, Mg z i = ∑ y, M z y * A i y) (z : ZV d N0 N1) :
    MvPowerSeries.subst
        (fun j : ι' => (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K))
        (linSub M z) = linSub Mg z := by
  have ha : MvPowerSeries.HasSubst (fun j : ι' =>
      (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => by simp)
  have hC : ∀ c : K, MvPowerSeries.subst (fun j : ι' =>
      (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K))
      (MvPowerSeries.C c : MvPowerSeries ι' K) = MvPowerSeries.C c := by
    intro c
    first
    | simpa using (MvPowerSeries.substAlgHom ha).commutes c
    | (rw [← MvPowerSeries.coe_substAlgHom ha]; simpa using (MvPowerSeries.substAlgHom ha).commutes c)
    | (rw [← MvPowerSeries.coe_substAlgHom ha]
       exact (MvPowerSeries.substAlgHom ha).commutes c)
  unfold linSub
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  simp only [map_mul, MvPowerSeries.coe_substAlgHom, hC, MvPowerSeries.subst_X ha, h, map_sum,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun y _ => ?_))
  ring

lemma subst_mvExp {K : Type u} [NormedField K] [CharZero K] {ι ι' : Type} {a : ι' → MvPowerSeries ι K}
    (hs : MvPowerSeries.HasSubst a) (f : MvPowerSeries ι' K)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := by
  unfold mvExp
  have hf' : MvPowerSeries.HasSubst (fun _ : Unit => f) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hf)
  unfold PowerSeries.subst
  exact MvPowerSeries.subst_comp_subst_apply hf' hs _

lemma sum_ZV_slice {d N0 N1 : ℕ} [NeZero d] {M : Type*} [AddCommMonoid M] (s : ZMod d)
    (b : Fin N1) (f : ZV d N0 N1 → M) (hf : ∀ y, ¬ (y.1 = s ∧ y.2.2 = b) → f y = 0) :
    ∑ y, f y = ∑ k, f (s, k, b) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.image (fun k : Fin N0 => ((s, k, b) : ZV d N0 N1))))]
  · rw [Finset.sum_image]
    intro k₁ _ k₂ _ h
    simpa using h
  · intro y _ hy
    apply hf
    rintro ⟨h1, h2⟩
    exact hy (Finset.mem_image.mpr ⟨y.2.1, Finset.mem_univ _, Prod.ext h1.symm (Prod.ext rfl h2.symm)⟩)

def genA {K : Type u} [Field K] {d N0 N1 : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) : ZV d N0 N1 → ZV d N0 N1 → K :=
  fun y y' => if y'.1 = y.1 ∧ y'.2.2 = y.2.2 then effMat TT T y.1 y.2.1 y'.2.1 else 0

lemma frameM_genA {K : Type u} [Field K] {d N0 N1 : ℕ} [NeZero d] (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (x xg : ZMod d × Fin N0 × Fin N0 → K)
    (hxg : ∀ s i a, xg (s, i, a) = ∑ k : Fin N0, effMat TT T s i k * x (s, k, a))
    (z i : ZV d N0 N1) :
    frameM (N1 := N1) xg z i = ∑ y, frameM (N1 := N1) x z y * genA TT T i y := by
  classical
  rw [sum_ZV_slice z.1 z.2.2]
  · simp only [frameM, genA, eq_self_iff_true, and_self, ↓reduceIte]
    by_cases h : i.1 = z.1 ∧ i.2.2 = z.2.2
    · rw [if_pos h, hxg]
      obtain ⟨h1, h2⟩ := h
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [if_pos ⟨h1.symm, h2.symm⟩, h1]
      ring
    · rw [if_neg h]
      refine (Finset.sum_eq_zero (fun k _ => ?_)).symm
      rw [if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), mul_zero]
  · intro y hy
    simp only [frameM]
    rw [if_neg hy, zero_mul]

lemma sum_genA_eq_rowOp {K : Type u} [Field K] {d N0 N1 : ℕ} [NeZero d] (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (i : Fin N0) (b : Fin N1) :
    (∑ j : ZV d N0 N1, MvPolynomial.C (genA TT T (s, i, b) j) * MvPolynomial.X j :
      MvPolynomial (ZV d N0 N1) K) = rowOp (N1 := N1) TT T s i b := by
  classical
  rw [sum_ZV_slice s b]
  · simp only [genA, rowOp, effMat, eq_self_iff_true, and_self, ↓reduceIte]
    by_cases h : s ∈ TT ∧ i.val = 0
    · simp only [if_pos h]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [hk]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · simp only [if_neg h]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs <;> simp
  · intro y hy
    simp only [genA]
    rw [if_neg hy, map_zero, zero_mul]

lemma map_minorProd {R : Type u} [CommRing R] {σ σ' : Type} {N0 N1 C : ℕ}
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ' R)
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) :
    φ (minorProd row p hp I) = minorProd (fun i b => φ (row i b)) p hp I := by
  unfold minorProd
  rw [map_prod]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [AlgHom.map_det]
  congr 1

end Frames

private theorem cc_subst_lemma {K : Type u} [Field K] {σ τ : Type} [Finite σ]
    (a : σ → MvPowerSeries τ K) (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (f : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  classical
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst ha,
    finsum_eq_single _ 0]
  · simp
  · intro e he
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod]
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr he
    rw [Finset.prod_eq_zero hs
      (by rw [map_pow, ha0, zero_pow (Finsupp.mem_support_iff.mp hs)]), smul_zero]

theorem thmAGen : ThmAGen.{u} := by
  unfold ThmAGen
  intro K _ _ _ l d N0 N1 _ hl hl3 hd hde hlt h0 K0 hK0 ζ hζ be hbe x hx g hg0 hg U hU ε hε
    TT colN p hp hp1 I T hT xg hxg nu1 nu2 size hnu1 hnu2 hsize a ha hsa spec hs1 hs2 hs3
  have hOp := thmAOp.{u}
  unfold ThmAOp at hOp
  have key := hOp K l d N0 N1 hl hl3 hd hde hlt h0 K0 hK0 ζ hζ be hbe x hx g hg0 hg U hU ε hε
    TT colN p hp hp1 I T hT nu1 nu2 size hnu1 hnu2 hsize a ha hsa spec hs1 hs2 hs3
  have hJ := jet_pair_linearity.{u}
  unfold JetPairLin at hJ
  have hsub : MvPowerSeries.HasSubst (fun j : ZV d N0 N1 =>
      (∑ i : ZV d N0 N1, MvPowerSeries.C (genA TT T i j) * MvPowerSeries.X i :
        MvPowerSeries (ZV d N0 N1) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => by simp)
  have hlin : ∀ z, MvPowerSeries.subst (fun j : ZV d N0 N1 =>
      (∑ i : ZV d N0 N1, MvPowerSeries.C (genA TT T i j) * MvPowerSeries.X i :
        MvPowerSeries (ZV d N0 N1) K))
      (linSub (frameM (N1 := N1) x) z) = linSub (frameM (N1 := N1) xg) z :=
    fun z => subst_linSub (frameM (N1 := N1) x) (genA TT T) (frameM (N1 := N1) xg)
      (fun z i => frameM_genA TT T x xg hxg z i) z
  have hL : ∀ (a0 : Fin N0) (b0 : Fin N1),
      MvPowerSeries.HasSubst (fun s : ZMod d => linSub (frameM (N1 := N1) x) (s, a0, b0)) :=
    fun a0 b0 => MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp [linSub])
  have hLx : MvPowerSeries.HasSubst (linSub (frameM (N1 := N1) x)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp [linSub])
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    by_contra hne
    have h1 := hbe.2.2.1 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
    simp [degE] at h1
  have hB : MvPowerSeries.constantCoeff (bSum (frameM (N1 := N1) x) be) = 0 := by
    simp only [bSum, map_sum]
    refine Finset.sum_eq_zero (fun ab _ => ?_)
    rw [cc_subst_lemma, hbe0]
    intro s
    simp [linSub]
  have hf0 : MvPowerSeries.constantCoeff (ε • bSum (frameM (N1 := N1) x) be) = 0 := by
    first
    | (rw [MvPowerSeries.smul_eq_C_mul, map_mul, hB, mul_zero])
    | (rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hB]; simp)
  have hF : MvPowerSeries.subst (fun j : ZV d N0 N1 =>
      (∑ i : ZV d N0 N1, MvPowerSeries.C (genA TT T i j) * MvPowerSeries.X i :
        MvPowerSeries (ZV d N0 N1) K))
      (MvPowerSeries.subst (linSub (frameM (N1 := N1) x)) (MvPowerSeries.subst g U) *
        mvExp (ε • bSum (frameM (N1 := N1) x) be)) =
      MvPowerSeries.subst (linSub (frameM (N1 := N1) xg)) (MvPowerSeries.subst g U) *
        mvExp (ε • bSum (frameM (N1 := N1) xg) be) := by
    rw [MvPowerSeries.subst_mul hsub, MvPowerSeries.subst_comp_subst_apply hLx hsub,
      subst_mvExp hsub _ hf0]
    congr 2
    · funext z
      exact hlin z
    · rw [← MvPowerSeries.coe_substAlgHom hsub, map_smul]
      congr 1
      simp only [bSum, map_sum]
      refine Finset.sum_congr rfl (fun ab _ => ?_)
      rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_comp_subst_apply (hL ab.1 ab.2) hsub]
      congr 1
      funext s
      exact hlin _
  have hP : MvPolynomial.aeval (fun i : ZV d N0 N1 =>
      (∑ j : ZV d N0 N1, MvPolynomial.C (genA TT T i j) * MvPolynomial.X j :
        MvPolynomial (ZV d N0 N1) K))
      (∏ s : ZMod d, minorProd (fun (i : Fin N0) (b : Fin N1) =>
        (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K)) (p s) (hp s) (I s)) =
      ∏ s : ZMod d, minorProd (rowOp (N1 := N1) TT T s) (p s) (hp s) (I s) := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [map_minorProd]
    congr 1
    funext i b
    rw [MvPolynomial.aeval_X]
    exact sum_genA_eq_rowOp TT T s i b
  have e1 := hJ K (ZV d N0 N1) (ZV d N0 N1) (genA TT T)
    (∏ s : ZMod d, minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K)) (p s) (hp s) (I s))
    (MvPowerSeries.subst (linSub (frameM (N1 := N1) x)) (MvPowerSeries.subst g U) *
      mvExp (ε • bSum (frameM (N1 := N1) x) be))
  rw [hF, hP] at e1
  rw [e1]
  exact key

end Formalism.DworkPowerSeriesWeights
