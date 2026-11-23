import Development.EtaleCohomology.DivisorCycles.CycleCount
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PowEig

open Matrix Polynomial
namespace LateralTheory.DivDb.CycleCount₂
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

def fixSp (P : Mat C N) : Submodule C (Fin N → C) where
  carrier := {u | P *ᵥ u = u}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.mulVec_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c u hu
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.mulVec_smul, hu]

theorem mem_fixSp {P : Mat C N} {u : Fin N → C} : u ∈ fixSp P ↔ P *ᵥ u = u := Iff.rfl

theorem eig_in [IsAlgClosed C] (W : Submodule C (Fin N → C)) (M : Mat C N)
    (hW : ∀ u ∈ W, M *ᵥ u ∈ W) (hne : ∃ u ∈ W, u ≠ 0) :
    ∃ u ∈ W, u ≠ 0 ∧ ∃ c : C, M *ᵥ u = c • u := by
  obtain ⟨u0, hu0, hu0'⟩ := hne
  have hW' : ∀ u ∈ W, Matrix.toLin' M u ∈ W := fun u hu => by
    rw [Matrix.toLin'_apply]; exact hW u hu
  let f : Module.End C W := (Matrix.toLin' M).restrict hW'
  have : Nontrivial W := ⟨⟨⟨u0, hu0⟩, 0, fun h => hu0' (by simpa using congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  refine ⟨x, x.2, fun h => hx.2 (Subtype.ext h), c, ?_⟩
  have := congrArg Subtype.val hx.apply_eq_smul
  simpa [f, LinearMap.restrict_apply, Matrix.toLin'_apply] using this

theorem eig_root (y : Mat C N) (l : C) (w : Fin N → C) (hw : w ≠ 0) (h : y *ᵥ w = l • w) :
    y.charpoly.IsRoot l := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly]
  apply (Matrix.exists_mulVec_eq_zero_iff).mp
  refine ⟨w, hw, ?_⟩
  rw [Matrix.sub_mulVec, h]
  simp [Matrix.scalar_apply, Pi.smul_def]

theorem pow_eig (y : Mat C N) (l : C) (w : Fin N → C) (h : y *ᵥ w = l • w) (m : ℕ) :
    (y ^ m) *ᵥ w = l ^ m • w :=
  _root_.UpperTheory.Reformulated.B.Qp8.pow_eig y l w h m

theorem aeval_eig (y : Mat C N) (l : C) (w : Fin N → C) (h : y *ᵥ w = l • w) (q : C[X]) :
    (aeval y q) *ᵥ w = q.eval l • w := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Matrix.add_mulVec, hp, hq, eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_mulVec,
      pow_eig y l w h, smul_smul, eval_monomial]

theorem intertw {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n))
    (hπ : ∀ j, y * p j = p (π j) * y) (m : ℕ) (j : Fin n) : y ^ m * p j = p ((π ^ m) j) * y ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, hπ, mul_assoc, pow_succ', Equiv.Perm.mul_apply]

theorem move {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n))
    (hπ : ∀ j, y * p j = p (π j) * y) (m : ℕ) (j : Fin n) (v : Fin N → C) (hv : p j *ᵥ v = v) :
    p ((π ^ m) j) *ᵥ (y ^ m *ᵥ v) = y ^ m *ᵥ v := by
  conv_rhs => rw [← hv]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, intertw p y π hπ]

theorem cyc [IsAlgClosed C] [CharZero C] {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n))
    (hS : Sys p) (hy : IsUnit y) (hπ : ∀ j, y * p j = p (π j) * y) (j : Fin n) :
    ∃ S : Finset C, S.card = Function.minimalPeriod π j ∧ ∀ l ∈ S, ∃ w : Fin N → C, w ≠ 0 ∧
      y *ᵥ w = l • w ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ w = 0 := by
  classical
  set k := Function.minimalPeriod π j with hkdef
  have hk : 0 < k := Function.minimalPeriod_pos_of_mem_periodicPts (π.injective.mem_periodicPts j)
  have hkj : (π ^ k) j = j := by rw [Equiv.Perm.coe_pow]; exact Function.isPeriodicPt_minimalPeriod π j
  have hne : ∀ m, 0 < m → m < k → (π ^ m) j ≠ j := fun m h0 h1 h =>
    Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod h0.ne' h1 (by rw [Equiv.Perm.coe_pow] at h; exact h)
  have hcomm : y ^ k * p j = p j * y ^ k := by rw [intertw p y π hπ, hkj]
  have hWm : ∀ u ∈ fixSp (p j), y ^ k *ᵥ u ∈ fixSp (p j) := by
    intro u hu; rw [mem_fixSp] at *; rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hu]
  have hWne : ∃ u ∈ fixSp (p j), u ≠ 0 := by
    by_contra hc; push_neg at hc
    apply hS.2 j
    refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
    rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
    exact hc _ (by rw [mem_fixSp, Matrix.mulVec_mulVec, (hS.1.idem j).eq])
  obtain ⟨v, hvW, hv0, β, hβ⟩ := eig_in _ _ hWm hWne
  rw [mem_fixSp] at hvW
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hv0
    obtain ⟨U, hU⟩ := hy.pow k
    have h1 : ((U⁻¹ : (Mat C N)ˣ) : Mat C N) * (U : Mat C N) = 1 := U.inv_mul
    rw [← Matrix.one_mulVec v, ← h1, ← Matrix.mulVec_mulVec, hU, hβ, zero_smul, Matrix.mulVec_zero]
  refine ⟨(nthRoots k β).toFinset, ?_, ?_⟩
  · have hsep : (X ^ k - Polynomial.C β).Separable := separable_X_pow_sub_C β (by exact_mod_cast hk.ne') hβ0
    rw [Multiset.toFinset_card_of_nodup (by unfold nthRoots; exact nodup_roots hsep)]
    unfold nthRoots
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_X_pow_sub_C]
  · intro l hl
    rw [Multiset.mem_toFinset, mem_nthRoots hk] at hl
    have hl0 : l ≠ 0 := by rintro rfl; rw [zero_pow hk.ne'] at hl; exact hβ0 hl.symm
    set a : ℕ → (Fin N → C) := fun m => (l⁻¹) ^ m • (y ^ m *ᵥ v) with ha
    have hya : ∀ m, y *ᵥ a m = l • a (m + 1) := by
      intro m; simp only [ha]
      rw [smul_smul, show l * (l⁻¹) ^ (m + 1) = (l⁻¹) ^ m by
        rw [pow_succ, mul_left_comm, mul_inv_cancel₀ hl0, mul_one], Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ']
    have hak : a k = a 0 := by
      simp only [ha]; rw [hβ, smul_smul, inv_pow, hl, inv_mul_cancel₀ hβ0, one_smul, pow_zero, pow_zero, one_smul,
        Matrix.one_mulVec]
    have hpa : ∀ i m, p i *ᵥ a m = if (π ^ m) j = i then a m else 0 := by
      intro i m; simp only [ha]; rw [Matrix.mulVec_smul]; split_ifs with h
      · subst h; rw [move p y π hπ m j v hvW]
      · rw [← move p y π hπ m j v hvW, Matrix.mulVec_mulVec, hS.1.ortho (Ne.symm h), Matrix.zero_mulVec, smul_zero]
    have hpj : p j *ᵥ ∑ m ∈ Finset.range k, a m = v := by
      rw [Matrix.mulVec_sum, Finset.sum_eq_single 0]
      · rw [hpa]; simp [ha]
      · intro m hm hm0; rw [hpa, if_neg]; exact hne m (Nat.pos_of_ne_zero hm0) (Finset.mem_range.mp hm)
      · intro h; exact absurd (Finset.mem_range.mpr hk) h
    refine ⟨∑ m ∈ Finset.range k, a m, ?_, ?_, ?_⟩
    · intro h; apply hv0; rw [← hpj, h, Matrix.mulVec_zero]
    · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Matrix.mulVec_sum, Finset.sum_congr rfl (fun m _ => hya m), ← Finset.smul_sum]
      congr 1
      rw [hk', Finset.sum_range_succ (fun m => a (m + 1)) k', Finset.sum_range_succ' a k', ← hk', hak]
    · intro i hi; rw [Matrix.mulVec_sum]; apply Finset.sum_eq_zero; intro m _; rw [hpa, if_neg]
      intro h; exact hi ⟨m, by rw [zpow_natCast]; exact h⟩

theorem eigs [IsAlgClosed C] [CharZero C] {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n))
    (hS : Sys p) (hy : IsUnit y) (hπ : ∀ j, y * p j = p (π j) * y) (hD : Disj y π p) :
    ∃ f : Fin n → C, Function.Injective f ∧ ∀ i, ∃ w : Fin N → C, w ≠ 0 ∧
      y *ᵥ w = f i • w ∧ ∀ k, ¬ π.SameCycle i k → p k *ᵥ w = 0 := by
  classical
  choose S hSc hSe using fun j => cyc p y π hS hy hπ j
  let rep : Fin n → Fin n := fun i => (@Quotient.mk _ (Equiv.Perm.SameCycle.setoid π) i).out
  have hrep : ∀ i, π.SameCycle (rep i) i := fun i => Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid π) i
  have hrepeq : ∀ i i', π.SameCycle i i' → rep i = rep i' := by
    intro i i' h
    exact congrArg Quotient.out (Quotient.sound (s := Equiv.Perm.SameCycle.setoid π) h)
  have hm : ∀ i, ∃ m, m < Function.minimalPeriod π (rep i) ∧ (π ^ m) (rep i) = i := by
    intro i; obtain ⟨m, hm⟩ := (hrep i).exists_nat_pow_eq
    refine ⟨m % Function.minimalPeriod π (rep i), Nat.mod_lt _
      (Function.minimalPeriod_pos_of_mem_periodicPts (π.injective.mem_periodicPts _)), ?_⟩
    rw [Equiv.Perm.coe_pow, Function.iterate_mod_minimalPeriod_eq, ← Equiv.Perm.coe_pow, hm]
  choose m hmlt hmeq using hm
  let g : Fin n → ℕ → C := fun r t => if h : t < (S r).card then ((S r).equivFin.symm ⟨t, h⟩ : C) else 0
  have hg : ∀ i, g (rep i) (m i) ∈ S (rep i) := by
    intro i; simp only [g]; rw [dif_pos (by rw [hSc]; exact hmlt i)]; exact Finset.coe_mem _
  have hsupp : ∀ i, ∃ w : Fin N → C, w ≠ 0 ∧ y *ᵥ w = g (rep i) (m i) • w ∧ ∀ k, ¬ π.SameCycle i k → p k *ᵥ w = 0 := by
    intro i; obtain ⟨w, hw0, hwe, hws⟩ := hSe _ _ (hg i)
    exact ⟨w, hw0, hwe, fun k hk => hws k (fun hc => hk ((hrep i).symm.trans hc))⟩
  refine ⟨fun i => g (rep i) (m i), ?_, hsupp⟩
  intro i i' h
  simp only at h
  have hsame : rep i = rep i' := by
    by_contra hne
    have hnc : ¬ π.SameCycle (rep i) (rep i') := fun hc =>
      hne (hrepeq _ _ (((hrep i).symm.trans hc).trans (hrep i')))
    obtain ⟨w, hw0, hwe, hws⟩ := hSe _ _ (hg i)
    obtain ⟨w', hw0', hwe', hws'⟩ := hSe _ _ (hg i')
    exact hD (rep i) (rep i') hnc _ w w' hw0 hw0' hwe (by rw [h]; exact hwe') hws hws'
  have hmm : m i = m i' := by
    have h2 := h
    simp only [g] at h2
    rw [dif_pos (by rw [hSc]; exact hmlt i), dif_pos (by rw [hSc]; exact hmlt i')] at h2
    have key : ∀ r r' : Fin n, r = r' → ∀ t t' (ht : t < (S r).card) (ht' : t' < (S r').card),
        ((S r).equivFin.symm ⟨t, ht⟩ : C) = (S r').equivFin.symm ⟨t', ht'⟩ → t = t' := by
      intro r r' hr; subst hr; intro t t' ht ht' he
      exact congrArg Fin.val ((S r).equivFin.symm.injective (Subtype.ext he))
    exact key _ _ hsame _ _ _ _ h2
  rw [← hmeq i, ← hmeq i', hsame, hmm]

theorem fixed_scalar [IsAlgClosed C] {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n))
    (hS : Sys p) (hπ : ∀ j, y * p j = p (π j) * y) (hdeg : Deg n y) (hD : Disj y π p)
    (f : Fin n → C) (hf : Function.Injective f) (hfe : ∀ i, ∃ w : Fin N → C, w ≠ 0 ∧
      y *ᵥ w = f i • w ∧ ∀ k, ¬ π.SameCycle i k → p k *ᵥ w = 0) (i : Fin n) (hi : π i = i) :
    ∃ c : C, y * p i = c • p i := by
  classical
  obtain ⟨q, hq0, hqd, hqy⟩ := hdeg
  have hroot : ∀ l (w : Fin N → C), w ≠ 0 → y *ᵥ w = l • w → q.eval l = 0 := by
    intro l w hw h
    have := aeval_eig y l w h q
    rw [hqy, Matrix.zero_mulVec] at this
    exact (smul_eq_zero.mp this.symm).resolve_right hw
  have hsub : Finset.univ.image f ⊆ q.roots.toFinset := by
    intro x hx
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw0, hwe, -⟩ := hfe i'
    rw [Multiset.mem_toFinset, mem_roots hq0]; exact hroot _ w hw0 hwe
  have hcard : (Finset.univ.image f).card = n := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have h1 : q.roots.toFinset.card ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
  have h2 : Multiset.card q.roots ≤ n := (Polynomial.card_roots' q).trans hqd
  have h3 := Finset.card_le_card hsub
  have hnd : q.roots.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega)
  have heq : Finset.univ.image f = q.roots.toFinset := Finset.eq_of_subset_of_card_le hsub (by omega)
  have honly : ∀ l (u : Fin N → C), u ≠ 0 → p i *ᵥ u = u → y *ᵥ u = l • u → l = f i := by
    intro l u hu hpu hyu
    have : l ∈ Finset.univ.image f := by
      rw [heq, Multiset.mem_toFinset, mem_roots hq0]; exact hroot l u hu hyu
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp this
    by_cases hc : π.SameCycle i i'
    · rw [hc.eq_of_left hi]
    · exfalso
      obtain ⟨w, hw0, hwe, hws⟩ := hfe i'
      refine hD i i' hc (f i') u w hu hw0 hyu hwe ?_ hws
      intro k hk
      have hki : k ≠ i := fun h => hk (h ▸ Equiv.Perm.SameCycle.refl _ _)
      rw [← hpu, Matrix.mulVec_mulVec, hS.1.ortho hki, Matrix.zero_mulVec]
  set l := f i
  have hlroot : q.IsRoot l := by obtain ⟨w, hw0, hwe, -⟩ := hfe i; exact hroot _ w hw0 hwe
  set q' := q /ₘ (X - Polynomial.C l)
  have hqq : q = q' * (X - Polynomial.C l) := by
    rw [mul_comm]; exact ((mul_divByMonic_eq_iff_isRoot).mpr hlroot).symm
  have hq'l : q'.eval l ≠ 0 := by
    intro h0
    have hdvd : (X - Polynomial.C l) ^ 2 ∣ q := by
      obtain ⟨r, hr⟩ := (Polynomial.dvd_iff_isRoot).mpr h0
      exact ⟨r, by rw [hqq, hr]; ring⟩
    have h4 := (le_rootMultiplicity_iff hq0).mpr hdvd
    rw [← count_roots] at h4
    have h5 := (Multiset.nodup_iff_count_le_one.mp hnd) l
    omega
  have hcomm : y * p i = p i * y := by rw [hπ, hi]
  have hc2 : aeval y q' * y = y * aeval y q' := by
    have := congrArg (aeval y) (mul_comm q' X)
    simpa [aeval_X] using this
  have hinj : ∀ u, p i *ᵥ u = u → aeval y q' *ᵥ u = 0 → u = 0 := by
    intro u hu hq'u
    by_contra hu0
    let W : Submodule C (Fin N → C) := fixSp (p i) ⊓ LinearMap.ker (Matrix.toLin' (aeval y q'))
    have hWm : ∀ x ∈ W, y *ᵥ x ∈ W := by
      intro x hx
      rw [Submodule.mem_inf, mem_fixSp, LinearMap.mem_ker, Matrix.toLin'_apply] at hx ⊢
      refine ⟨?_, ?_⟩
      · rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hx.1]
      · rw [Matrix.mulVec_mulVec, hc2, ← Matrix.mulVec_mulVec, hx.2, Matrix.mulVec_zero]
    obtain ⟨u', hu'W, hu'0, c, hc⟩ := eig_in W y hWm ⟨u, by
      rw [Submodule.mem_inf, mem_fixSp, LinearMap.mem_ker, Matrix.toLin'_apply]; exact ⟨hu, hq'u⟩, hu0⟩
    rw [Submodule.mem_inf, mem_fixSp, LinearMap.mem_ker, Matrix.toLin'_apply] at hu'W
    have hcl : c = l := honly c u' hu'0 hu'W.1 hc
    have h6 := aeval_eig y c u' hc q'
    rw [hu'W.2, hcl] at h6
    exact hq'l ((smul_eq_zero.mp h6.symm).resolve_right hu'0)
  refine ⟨l, ?_⟩
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun u => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec]
  have hc3 : p i * (y - l • 1) = (y - l • 1) * p i := by
    rw [mul_sub, sub_mul, ← hcomm, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have h4 : aeval y q' * (y - l • 1) = 0 := by
    rw [← hqy, hqq, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  have hz := hinj ((y - l • 1) *ᵥ (p i *ᵥ u)) (by
      simp only [Matrix.mulVec_mulVec]; rw [← mul_assoc, hc3, mul_assoc, (hS.1.idem i).eq])
    (by simp only [Matrix.mulVec_mulVec]; rw [← mul_assoc, h4, Matrix.zero_mul, Matrix.zero_mulVec])
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, Matrix.mulVec_mulVec] at hz
  exact hz

theorem CycleCount_of : CycleCount := by
  intro C _ _ _ N n p y π hS hy hπ hdeg hD
  obtain ⟨f, hf, hfe⟩ := eigs p y π hS hy hπ hD
  refine ⟨⟨f, hf, fun i => ?_⟩, fun i hi => fixed_scalar p y π hS hπ hdeg hD f hf hfe i hi⟩
  obtain ⟨w, hw0, hwe, -⟩ := hfe i
  exact eig_root y _ w hw0 hwe

end LateralTheory.DivDb.CycleCount₂
