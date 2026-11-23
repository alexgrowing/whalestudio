import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem map_finset_prod_eq_sum_of_add_hom_on_subgroup {F M ι : Type} [Field F] [AddCommMonoid M] (U : Subgroup Fˣ)
    (f : Fˣ → M) (hf : ∀ x ∈ U, ∀ y ∈ U, f (x * y) = f x + f y) (hf1 : f 1 = 0)
    (s : Finset ι) (g : ι → Fˣ) (hg : ∀ i ∈ s, g i ∈ U) :
    f (∏ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf1]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, g i ∈ U := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      hf _ (hg a (Finset.mem_insert_self a s)) _ (Subgroup.prod_mem U hs), ih hs]

private theorem sum_eq_sum_range_pow_of_cyclic_generator {G M : Type} [Group G] [Fintype G] [AddCommMonoid M] (γ : G)
    (hγ : ∀ σ : G, σ ∈ Subgroup.zpowers γ) (g : G → M) :
    ∑ σ, g σ = ∑ j ∈ Finset.range (orderOf γ), g (γ ^ j) := by
  classical
  have hfin : IsOfFinOrder γ := isOfFinOrder_of_finite γ
  symm
  refine Finset.sum_nbij (fun j => γ ^ j) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij
  · intro σ _
    have h := hfin.mem_powers_iff_mem_zpowers.mpr (hγ σ)
    rw [hfin.mem_powers_iff_mem_range_orderOf] at h
    simpa using h

theorem UpperTheory.V.ZK.Cl.cBetaVal :
    UpperTheory.V.ZK.Cl.CBetaVal := by
  intro L F _ _ _ _ _ l c ν E _ ζ γ hL kap hk U f hU hf α hα p
  set z := toF ζ with hzdef
  have hz : IsPrimitiveRoot z (l ^ ν) :=
    hL.prim.map_of_injective (Units.map_injective RingOfIntegers.coe_injective)
  have hcong : ∀ m n : ℕ, z ^ m = z ^ n → (m : ZMod (l ^ ν)) = n := fun m n h =>
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by rw [hz.eq_orderOf]; exact pow_eq_pow_iff_modEq.mp h)
  have hact : ∀ (σ τ : Gal(F/L)) (x : Fˣ), actU (σ * τ) x = actU σ (actU τ x) :=
    fun σ τ x => Units.ext rfl
  have hkm : ∀ σ τ : Gal(F/L), ((kap (σ * τ) : ℕ) : ZMod (l ^ ν)) = kap σ * kap τ := by
    intro σ τ
    rw [← Nat.cast_mul]
    apply hcong
    rw [← hk, hact, hk, map_pow, hk, ← pow_mul]
  have hkγ : ((kap γ : ℕ) : ZMod (l ^ ν)) = 1 + (l : ZMod (l ^ ν)) ^ c := by
    have h := hcong (kap γ) (1 + l ^ c) (by
      rw [← hk]
      ext
      simpa [actU, toF, z] using hL.act)
    simpa using h
  have hk1 : ((kap 1 : ℕ) : ZMod (l ^ ν)) = 1 := by
    have h := hcong (kap 1) 1 (by rw [← hk, pow_one]; exact Units.ext rfl)
    simpa using h
  have hkpow : ∀ j : ℕ, ((kap (γ ^ j) : ℕ) : ZMod (l ^ ν)) = (1 + (l : ZMod (l ^ ν)) ^ c) ^ j := by
    intro j
    induction j with
    | zero => simpa using hk1
    | succ j ih => rw [pow_succ, hkm, ih, hkγ, pow_succ]
  have hf1 : f 1 = 0 := by
    have h := hf 1 U.one_mem 1 U.one_mem
    rw [mul_one] at h
    simpa using h
  have hfn : ∀ x ∈ U, ∀ n : ℕ, f (x ^ n) = n * f x := by
    intro x hx n
    induction n with
    | zero => simp [hf1]
    | succ n ih =>
      rw [pow_succ, hf _ (U.pow_mem hx n) _ hx, ih]
      push_cast
      ring
  have hfz : ∀ x ∈ U, ∀ n : ℤ, f (x ^ n) = n * f x := by
    intro x hx n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [zpow_natCast, hfn x hx]
      push_cast
      ring
    · have h := hf _ (U.pow_mem hx m) _ (U.inv_mem (U.pow_mem hx m))
      rw [mul_inv_cancel, hf1, hfn x hx] at h
      rw [zpow_neg, zpow_natCast]
      push_cast
      linear_combination -h
  have hUa : ∀ σ : Gal(F/L), actU σ α ∈ U := fun σ => hU σ α hα
  have hL1 : ∀ σ : Gal(F/L), f (actU σ (polAct γ p α)) =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        (p.coeff i : ZMod (l ^ ν)) * f (actU (σ * (γ ^ i)⁻¹) α) := by
    intro σ
    simp only [polAct, map_prod, map_zpow]
    rw [map_finset_prod_eq_sum_of_add_hom_on_subgroup U f hf hf1 _ _ (fun i _ => U.zpow_mem (hU σ _ (hUa _)) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfz _ (hU σ _ (hUa _)), ← hact, inv_pow]
  set S := ∑ τ : Gal(F/L), (kap τ : ZMod (l ^ ν)) ^ E * f (actU τ α) with hSdef
  have hS : ∀ i : ℕ, ∑ σ : Gal(F/L), (kap σ : ZMod (l ^ ν)) ^ E * f (actU (σ * (γ ^ i)⁻¹) α) =
      ((1 + (l : ZMod (l ^ ν)) ^ c) ^ E) ^ i * S := by
    intro i
    rw [← (Equiv.mulRight (γ ^ i)).sum_comp, hSdef, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [Equiv.coe_mulRight, mul_inv_cancel_right]
      rw [hkm, hkpow]
      ring
    · intro _ _
      simp
  have hR : f (nrm γ ((1 + l ^ c) ^ E) α) = S := by
    simp only [nrm]
    rw [map_finset_prod_eq_sum_of_add_hom_on_subgroup U f hf hf1 _ _ (fun j _ => U.pow_mem (hUa _) _), hSdef,
      sum_eq_sum_range_pow_of_cyclic_generator γ hL.gen]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfn _ (hUa _), hkpow]
    push_cast
    ring
  have hE : ((eval (((1 + l ^ c) ^ E : ℕ) : ℤ) p : ℤ) : ZMod (l ^ ν)) =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        (p.coeff i : ZMod (l ^ ν)) * ((1 + (l : ZMod (l ^ ν)) ^ c) ^ E) ^ i := by
    rw [eval_eq_sum_range]
    push_cast
    rfl
  rw [hE, hR, Finset.sum_mul]
  simp_rw [hL1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← hS i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring
