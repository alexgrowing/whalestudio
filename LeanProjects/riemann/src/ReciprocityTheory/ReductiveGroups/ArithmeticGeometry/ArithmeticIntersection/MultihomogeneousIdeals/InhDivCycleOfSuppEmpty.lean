import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Len

variable {R : Type*} [CommRing R]

theorem inh_length_locQuot (W : Ideal R) [W.IsPrime] (J : Ideal R) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  have := IsLocalization.linearMap_compatibleSMul W.primeCompl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    ((J : Submodule R R).toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap R (Localization.AtPrime W)))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).restrictScalars (Localization.AtPrime W)
  rw [← e.length_eq, Ideal.localized'_eq_map]

theorem inh_length_quot_maximal (W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ W.map (algebraMap R (Localization.AtPrime W))) = 1 := by
  rw [Localization.AtPrime.map_eq_maximalIdeal, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom]
  exact Ideal.isMaximal_def.mp inferInstance

theorem inh_length_pow [IsDomain R] (x : R) (hx : x ≠ 0) [(Ideal.span {x}).IsPrime] (m : ℕ) :
    Module.length (Localization.AtPrime (Ideal.span {x}))
      (Localization.AtPrime (Ideal.span {x}) ⧸
        (Ideal.span {x ^ m}).map (algebraMap R (Localization.AtPrime (Ideal.span {x})))) = m := by
  set A := Localization.AtPrime (Ideal.span {x})
  have hinj : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A (Ideal.span {x}).primeCompl_le_nonZeroDivisors
  have : IsDomain A := inferInstance
  have hx' : algebraMap R A x ∈ nonZeroDivisors A :=
    mem_nonZeroDivisors_of_ne_zero fun h => hx (hinj (by rw [h, map_zero]))
  rw [Ideal.map_span, Set.image_singleton, map_pow]
  change Ring.ord A (algebraMap R A x ^ m) = m
  rw [Ring.ord_pow hx', Ring.ord, ← Set.image_singleton, ← Ideal.map_span,
    inh_length_quot_maximal]
  simp

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem inh_multAt_self (W : Ideal (MRingOver R ι)) [hW : W.IsPrime] : multAt W W = 1 := by
  rw [multAt, dif_pos hW, inh_length_locQuot, inh_length_quot_maximal]
  rfl

theorem inh_multAt_pow [IsDomain R] (x : MRingOver R ι) (hx : x ≠ 0) [hW : (Ideal.span {x}).IsPrime]
    (m : ℕ) : multAt (Ideal.span {x ^ m}) (Ideal.span {x}) = m := by
  rw [multAt, dif_pos hW, inh_length_locQuot, inh_length_pow x hx]
  simp

end Len

section Div

variable {R : Type*} [CommRing R]

theorem inh_minimalPrimes_eq {I Q : Ideal R} [hQ : Q.IsPrime] (hIQ : I ≤ Q)
    (hmin : ∀ q : Ideal R, q.IsPrime → I ≤ q → Q ≤ q) : I.minimalPrimes = {Q} := by
  ext W
  simp only [Ideal.minimalPrimes, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    exact le_antisymm (h.2 ⟨hQ, hIQ⟩ (hmin W h.1.1 h.1.2)) (hmin W h.1.1 h.1.2)
  · rintro rfl
    exact ⟨⟨hQ, hIQ⟩, fun y hy _ => hmin y hy.1 hy.2⟩

theorem inh_minimalPrimes_top : (⊤ : Ideal R).minimalPrimes = ∅ := by
  ext W
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨⟨hp, hle⟩, -⟩ := h
  exact hp.ne_top (top_le_iff.mp hle)

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

theorem inh_divCycle_of_supp (P : Ideal (MRingOver F ι)) (s : MRingOver F ι) (Q : Ideal (MRingOver F ι))
    (hsupp : divSupp P s = {Q}) :
    divCycle P s = Finsupp.single Q (multAt (P ⊔ Ideal.span {s}) Q) := by
  classical
  ext W
  rw [divCycle, Finsupp.ofSupportFinite_coe, Finsupp.single_apply, hsupp, Set.mem_singleton_iff]
  by_cases h : W = Q
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem inh_divCycle_of_supp_empty (P : Ideal (MRingOver F ι)) (s : MRingOver F ι)
    (hsupp : divSupp P s = ∅) : divCycle P s = 0 := by
  classical
  ext W
  rw [divCycle, Finsupp.ofSupportFinite_coe, hsupp]
  simp

theorem inh_divCycle_one (P : Ideal (MRingOver F ι)) : divCycle P 1 = 0 := by
  apply inh_divCycle_of_supp_empty
  ext W
  simp [divSupp, Ideal.span_singleton_one, inh_minimalPrimes_top]

theorem inh_divCycle_prime (P : Ideal (MRingOver F ι)) (s : MRingOver F ι) (Q : Ideal (MRingOver F ι))
    [Q.IsPrime] (hQ : P ⊔ Ideal.span {s} = Q) (hrel : IsRelevant Q) :
    divCycle P s = Finsupp.single Q 1 := by
  rw [inh_divCycle_of_supp P s Q, hQ, inh_multAt_self]
  ext W
  simp only [divSupp, hQ, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
    Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, hrel⟩

theorem inh_divCycle_irrel (P : Ideal (MRingOver F ι)) (s : MRingOver F ι) (Q : Ideal (MRingOver F ι))
    [Q.IsPrime] (hQ : P ⊔ Ideal.span {s} = Q) (hrel : ¬ IsRelevant Q) : divCycle P s = 0 := by
  apply inh_divCycle_of_supp_empty
  ext W
  simp only [divSupp, hQ, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl; exact hrel

theorem inh_divCycle_pow (x : MRingOver F ι) (hx : x ≠ 0) [(Ideal.span {x}).IsPrime]
    (hrel : IsRelevant (Ideal.span {x})) (m : ℕ) :
    divCycle ⊥ (x ^ m) = Finsupp.single (Ideal.span {x}) m := by
  rcases m with _ | m
  · simp [inh_divCycle_one]
  have hm : (⊥ ⊔ Ideal.span {x ^ (m + 1)}).minimalPrimes = {Ideal.span {x}} := by
    rw [bot_sup_eq]
    apply inh_minimalPrimes_eq
    · rw [Ideal.span_singleton_le_span_singleton]; exact dvd_pow_self x (Nat.succ_ne_zero m)
    · intro q hq hle
      rw [Ideal.span_singleton_le_iff_mem] at hle ⊢
      exact hq.mem_of_pow_mem _ hle
  rw [inh_divCycle_of_supp ⊥ _ (Ideal.span {x}), bot_sup_eq, inh_multAt_pow x hx]
  ext W
  simp only [divSupp, hm, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, hrel⟩

theorem inh_cycEval_single (J : Ideal (MRingOver F ι) → ℤ) (W : Ideal (MRingOver F ι)) (m : ℤ) :
    cycEval J (Finsupp.single W m) = m * J W := by
  rw [cycEval, Finsupp.sum_single_index (zero_mul _)]

end Div

section Kill

variable {σ : Type*} (F : Type*) [Field F] [DecidableEq σ] (S : Finset σ)

def inhKill : MvPolynomial σ F →ₐ[F] MvPolynomial {s // s ∉ S} F :=
  aeval fun s => if h : s ∈ S then 0 else X ⟨s, h⟩

theorem inhKill_X_mem {s : σ} (h : s ∈ S) : inhKill F S (X s) = 0 := by
  simp [inhKill, h]

theorem inhKill_X_nmem {s : σ} (h : s ∉ S) : inhKill F S (X s) = X ⟨s, h⟩ := by
  simp [inhKill, h]

abbrev inhV : Ideal (MvPolynomial σ F) := Ideal.span ((fun s => (X s : MvPolynomial σ F)) '' (S : Set σ))

theorem inhV_kill {f : MvPolynomial σ F} (hf : f ∈ inhV F S) : inhKill F S f = 0 := by
  refine Submodule.span_induction (p := fun f _ => inhKill F S f = 0) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨s, hs, rfl⟩; exact inhKill_X_mem F S hs
  · simp
  · intro a b _ _ ha hb; simp [ha, hb]
  · intro a b _ hb; simp [smul_eq_mul, hb]

def inhQuotEquiv : (MvPolynomial σ F ⧸ inhV F S) ≃ₐ[F] MvPolynomial {s // s ∉ S} F :=
  AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ (inhV F S) (inhKill F S) fun _ ha => inhV_kill F S ha)
    ((Ideal.Quotient.mkₐ F (inhV F S)).comp (rename Subtype.val))
    (by
      apply MvPolynomial.algHom_ext
      intro s
      show inhKill F S (rename Subtype.val (X s)) = X s
      rw [rename_X, inhKill_X_nmem F S s.2])
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro s
      show Ideal.Quotient.mk _ (rename Subtype.val (inhKill F S (X s))) = Ideal.Quotient.mk _ (X s)
      by_cases h : s ∈ S
      · rw [inhKill_X_mem F S h, map_zero, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_image_of_mem _ (Finset.mem_coe.mpr h)))).symm
      · rw [inhKill_X_nmem F S h, rename_X])

theorem inhV_mem_iff (f : MvPolynomial σ F) : f ∈ inhV F S ↔ inhKill F S f = 0 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have : inhKill F S f = inhQuotEquiv F S (Ideal.Quotient.mk _ f) := rfl
  rw [this, map_eq_zero_iff _ (inhQuotEquiv F S).injective]

theorem inhV_X_nmem {s : σ} (h : s ∉ S) : (X s : MvPolynomial σ F) ∉ inhV F S := by
  rw [inhV_mem_iff, inhKill_X_nmem F S h]
  exact X_ne_zero _

theorem inhV_X_mem {s : σ} (h : s ∈ S) : (X s : MvPolynomial σ F) ∈ inhV F S :=
  Ideal.subset_span ⟨s, h, rfl⟩

instance inhV_isPrime : (inhV F S).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact (inhQuotEquiv F S).toRingEquiv.toMulEquiv.isDomain

theorem inhV_dim [Finite σ] :
    ringKrullDim (MvPolynomial σ F ⧸ inhV F S) = (Nat.card {s // s ∉ S} : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (inhQuotEquiv F S).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

theorem inhV_insert (p : σ) : inhV F S ⊔ Ideal.span {X p} = inhV F (insert p S) := by
  simp only [inhV, Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert]
  exact sup_comm _ _

theorem inhV_singleton (p : σ) : inhV F {p} = Ideal.span {X p} := by
  simp [inhV]

theorem inhV_empty : inhV F (∅ : Finset σ) = ⊥ := by
  simp [inhV]

end Kill

section Homog

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*}
  [Field F]

theorem inh_homog_X_pow (p : Σ k, ι k) (m : ℕ) :
    IsMultiHomog (X p ^ m : MRingOver F ι) (Pi.single p.1 m) := by
  classical
  intro n hn k
  rw [support_X_pow, Finset.mem_singleton] at hn
  subst hn
  obtain ⟨k', i'⟩ := p
  by_cases hk : k = k'
  · subst hk
    rw [Finset.sum_eq_single i']
    · simp
    · intro b _ hb; rw [Finsupp.single_apply, if_neg]; intro h; exact hb (sigma_mk_injective h).symm
    · simp
  · rw [Pi.single_apply, if_neg hk]
    apply Finset.sum_eq_zero
    intro b _
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h).symm

theorem inh_homog_X (p : Σ k, ι k) : IsMultiHomog (X p : MRingOver F ι) (Pi.single p.1 1) := by
  simpa using inh_homog_X_pow (F := F) p 1

theorem inh_homog_one : IsMultiHomog (1 : MRingOver F ι) 0 := by
  intro n hn k
  rw [support_one, Finset.mem_singleton] at hn
  subst hn
  simp

variable [DecidableEq (Σ k, ι k)]

theorem inhV_homogIdeal (S : Finset (Σ k, ι k)) : IsMultiHomogIdeal (inhV F S) :=
  ⟨_, by rintro _ ⟨p, _, rfl⟩; exact ⟨_, inh_homog_X p⟩, rfl⟩

theorem inhV_relevant (S : Finset (Σ k, ι k)) (h : ∀ k, ∃ i, (⟨k, i⟩ : Σ k, ι k) ∉ S) :
    IsRelevant (inhV F S) :=
  fun k => let ⟨i, hi⟩ := h k; ⟨i, inhV_X_nmem F S hi⟩

theorem inhV_projVar (S : Finset (Σ k, ι k)) (d : ℕ) (h : ∀ k, ∃ i, (⟨k, i⟩ : Σ k, ι k) ∉ S)
    (hc : Nat.card {s // s ∉ S} = d + Fintype.card K) : IsProjVarF (inhV F S) d :=
  ⟨⟨inferInstance, inhV_homogIdeal S, inhV_relevant S h⟩, by rw [inhV_dim, hc]⟩

end Homog

section Fin1

variable {σ : Type*} {F : Type*} [Field F]

theorem inh_finrank_quot (I : Ideal (MvPolynomial σ F)) (c : σ → F)
    (hI : I ≤ RingHom.ker (eval c)) (hX : ∀ s, X s - C (c s) ∈ I) :
    Module.finrank F (MvPolynomial σ F ⧸ I) = 1 := by
  have hne : I ≠ ⊤ := by
    intro h
    have := hI (h ▸ Submodule.mem_top : (1 : MvPolynomial σ F) ∈ I)
    simp at this
  have := Ideal.Quotient.nontrivial_iff.mpr hne
  have hmk : (Ideal.Quotient.mk I) = (algebraMap F (MvPolynomial σ F ⧸ I)).comp (eval c) := by
    apply MvPolynomial.ringHom_ext
    · intro r; rw [RingHom.comp_apply, eval_C]; rfl
    · intro s
      rw [RingHom.comp_apply, eval_X,
        show algebraMap F _ (c s) = Ideal.Quotient.mk I (C (c s)) from rfl]
      exact Ideal.Quotient.eq.mpr (hX s)
  rw [finrank_eq_one_iff_of_nonzero' (1 : MvPolynomial σ F ⧸ I) one_ne_zero]
  intro w
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨eval c f, ?_⟩
  rw [Algebra.smul_def, mul_one, hmk, RingHom.comp_apply]

end Fin1

end ReciprocityTheory.ChartRestriction.G.AI.I1
