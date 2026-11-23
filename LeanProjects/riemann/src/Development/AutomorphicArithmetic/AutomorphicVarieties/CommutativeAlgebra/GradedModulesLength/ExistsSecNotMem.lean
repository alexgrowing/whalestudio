import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)

private theorem coe_sec_eq_monomial_single (i : Fin k) (f : A) (hf : f ∈ N i) :
    (sec N i f hf : MvPolynomial (Fin k) A) = MvPolynomial.monomial (Finsupp.single i 1) f := rfl

private theorem toDeg_single_one (i : Fin k) : toDeg (Finsupp.single i 1) = e i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [toDeg, e]
  · simp [toDeg, e, h, Finsupp.single_apply, Ne.symm h]

private theorem exists_sec_notMem {p : Ideal (rees N)} (hp : ¬ Irr (reesGr N) ≤ p) (i : Fin k) :
    ∃ (f : A) (hf : f ∈ N i), sec N i f hf ∉ p := by
  by_contra hcon
  push_neg at hcon
  apply hp
  have hle : Ideal.span (reesGr N (e i) : Set (rees N)) ≤ p := by
    rw [Ideal.span_le]
    intro q hq
    have hc : MvPolynomial.coeff (Finsupp.single i 1) (q : MvPolynomial (Fin k) A) ∈ N i := by
      have := q.2 (Finsupp.single i 1)
      rwa [lat_single] at this
    have hq' : q = sec N i _ hc := by
      apply Subtype.ext
      rw [coe_sec_eq_monomial_single]
      ext m
      rw [MvPolynomial.coeff_monomial]
      split_ifs with hm
      · rw [hm]
      · apply hq m
        intro hd
        apply hm
        apply toDeg_injective
        rw [hd, toDeg_single_one]
    rw [hq']
    exact hcon _ hc
  exact le_trans (le_trans Ideal.prod_le_inf (Finset.inf_le (Finset.mem_univ i))) hle

private theorem sec_mul_sec (i j : Fin k) {f g : A} (hf : f ∈ N i) (hg : g ∈ N i) (hf' : f ∈ N j) (hg' : g ∈ N j) :
    sec N i f hf * sec N j g hg' = sec N i g hg * sec N j f hf' := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, coe_sec_eq_monomial_single, MvPolynomial.monomial_mul]
  rw [mul_comm f g]

end SlopeTestRemainingChoices

private theorem algebraMap_mul_sec_mul_sec_eq_of_mul_eq {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (c : B) (i j : Fin k) {x y x' y' : A} (hx : x ∈ N i) (hy : y ∈ N j)
    (hx' : x' ∈ N i) (hy' : y' ∈ N j) (h : algebraMap B A c * x * y = x' * y') :
    algebraMap B (rees N) c * (sec N i x hx * sec N j y hy) = sec N i x' hx' * sec N j y' hy' := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, coe_sec_eq_monomial_single, MvPolynomial.algebraMap_apply,
    MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial]
  rw [← h, mul_assoc]

theorem UpperTheory.V.Alg.M.zi_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ p : Ideal (mR Q), p.IsPrime → ¬ Irr (mGr Q) ≤ p → secs (ts Q) ≤ p → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ p) →
      (∀ b : 𝒜 0, (b : A) ∈ Q.ideal → algebraMap (𝒜 0) (mR Q) b ∈ p) ∧
      ∀ i, sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F i ^ 2) (sq_mem_neg 𝒜 (Q.hF i)) ∈ p := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q P hP hIrr hts hZ
  have hmul : ∀ {i j l : ℤ} {a b : A}, i + j = l → a ∈ 𝒜 i → b ∈ 𝒜 j → a * b ∈ 𝒜 l := by
    rintro i j l a b rfl ha hb
    exact SetLike.mul_mem_graded ha hb
  have m0 : ∀ {a : A}, a ∈ 𝒜 (-2) → a ∈ mN 𝒜 (Q.F (Fin.last r)) 0 := fun h => h
  have m1 : ∀ {a : A}, a ∈ 𝒜 2 → a ∈ mN 𝒜 (Q.F (Fin.last r)) 1 := fun h => h
  have m2 : ∀ {a : A}, a ∈ mN 𝒜 (Q.F (Fin.last r)) 2 → a ∈ 𝒜 (-2) := by
    intro a ha
    have hle : ((𝒜 0) ∙ Q.F (Fin.last r) ^ 2 ⊔ oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 : Submodule (𝒜 0) A)
        ≤ oz 𝒜 (-2) := by
      apply sup_le
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact sq_mem_neg 𝒜 (Q.hF _)
      · apply Submodule.mul_le.2
        intro u hu v hv
        have hu' : u ∈ oz 𝒜 (-4) :=
          (Submodule.mul_le.2 (fun a ha b hb => hmul (i := -2) (j := -2) (by norm_num) ha hb) :
            oz 𝒜 (-2) * oz 𝒜 (-2) ≤ oz 𝒜 (-4)) hu
        exact hmul (i := -4) (j := 2) (by norm_num) hu' hv
    exact hle ha
  have hF2 : Q.F (Fin.last r) ^ 2 ∈ mN 𝒜 (Q.F (Fin.last r)) 2 :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have hmem : ∀ {d : Deg 3} {u : mR Q}, (d, u) ∈ ts Q → u ∈ P := fun h => hts (Ideal.subset_span ⟨_, h⟩)
  obtain ⟨g0, hg0, hg0P⟩ := exists_sec_notMem _ hIrr 0
  obtain ⟨f1, hf1, hf1P⟩ := exists_sec_notMem _ hIrr 1
  obtain ⟨h2, hh2, hh2P⟩ := exists_sec_notMem _ hIrr 2
  have hFlast : sec (mN 𝒜 (Q.F (Fin.last r))) 2 (Q.F (Fin.last r) ^ 2) hF2 ∈ P :=
    hmem (d := e 2) (by simp [ts, tsR])
  have hsq : ∀ i, sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F i ^ 2) (sq_mem_neg 𝒜 (Q.hF i)) ∈ P := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have heq := sec_mul_sec (mN 𝒜 (Q.F (Fin.last r))) 0 2 (sq_mem_neg 𝒜 (Q.hF (Fin.last r)))
        (m0 (m2 hh2)) hF2 hh2
      have hin : sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F (Fin.last r) ^ 2) (sq_mem_neg 𝒜 (Q.hF (Fin.last r))) *
          sec (mN 𝒜 (Q.F (Fin.last r))) 2 h2 hh2 ∈ P := by
        rw [heq]
        exact P.mul_mem_left _ hFlast
      exact (hP.mem_or_mem hin).resolve_right hh2P
    · exact hmem (d := e 0) (by simp [ts, tsF, List.mem_ofFn])
  refine ⟨?_, hsq⟩
  set u := sec (mN 𝒜 (Q.F (Fin.last r))) 0 g0 hg0 * sec (mN 𝒜 (Q.F (Fin.last r))) 1 f1 hf1 with hu_def
  have hu : u ∉ P := fun h => (hP.mem_or_mem h).elim hg0P hf1P
  have key : ∀ w : 𝒜 0, algebraMap (𝒜 0) (mR Q) w * u ∈ P → algebraMap (𝒜 0) (mR Q) w ∈ P :=
    fun w h => (hP.mem_or_mem h).resolve_right hu
  have keysq : ∀ w : 𝒜 0, algebraMap (𝒜 0) (mR Q) (w * w) * u ∈ P → algebraMap (𝒜 0) (mR Q) w ∈ P := by
    intro w h
    have := key _ h
    rw [map_mul] at this
    exact (hP.mem_or_mem this).elim id id
  have hgen : ∀ (d : ℤ) (g : A) (hg : g ∈ 𝒜 d),
      (∀ (j : ℤ) (hj : j + d = 0) (c : A) (hc : c ∈ 𝒜 j),
        algebraMap (𝒜 0) (mR Q) ⟨c * g, hmul hj hc hg⟩ ∈ P) →
      ∀ a : A, algebraMap (𝒜 0) (mR Q) (DirectSum.decompose 𝒜 (a * g) 0) ∈ P := by
    intro d g hg hc a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous j a =>
      by_cases hj : j + d = 0
      · have h0 := hc j hj a a.2
        convert h0 using 2
        apply Subtype.ext
        exact DirectSum.decompose_of_mem_same 𝒜 (hmul hj a.2 hg)
      · have h0 : DirectSum.decompose 𝒜 ((a : A) * g) 0 = 0 :=
          Subtype.ext (DirectSum.decompose_of_mem_ne 𝒜 (hmul rfl a.2 hg) hj)
        rw [h0, map_zero]
        exact P.zero_mem
    | add a a' ha ha' =>
      rw [add_mul, DirectSum.decompose_add, DirectSum.add_apply, map_add]
      exact P.add_mem ha ha'
  intro b hb
  have hall : ∀ y ∈ Q.ideal, ∀ a : A, algebraMap (𝒜 0) (mR Q) (DirectSum.decompose 𝒜 (a * y) 0) ∈ P := by
    intro y hy
    unfold Eqns.ideal at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · refine hgen (-1) _ (Q.hF i) ?_
        intro j hj c hc
        obtain rfl : j = 1 := by omega
        apply keysq
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1 (sq_mem_neg 𝒜 (Q.hF i))
          (m1 (hmul (i := 0) (j := 2) (by norm_num) (hmul (i := 2) (j := -2) (by norm_num)
            (hmul (i := 1) (j := 1) (by norm_num) hc hc) hg0) hf1)) (by change c * Q.F i * (c * Q.F i) * g0 * f1 = _; ring)]
        exact P.mul_mem_right _ (hsq i)
      · refine hgen (-2) _ (Q.hG i) ?_
        intro j hj c hc
        obtain rfl : j = 2 := by omega
        apply key
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1 (Q.hG i)
          (m1 (hmul (i := 0) (j := 2) (by norm_num) (hmul (i := 2) (j := -2) (by norm_num) hc hg0) hf1))
          (by change c * Q.G i * g0 * f1 = _; ring)]
        exact P.mul_mem_right _ (hmem (d := e 0) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 1 _ (Q.hE i) ?_
        intro j hj c hc
        obtain rfl : j = -1 := by omega
        apply keysq
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1
          (m0 (hmul (i := -4) (j := 2) (by norm_num) (hmul (i := -2) (j := -2) (by norm_num)
            (hmul (i := -1) (j := -1) (by norm_num) hc hc) hg0) hf1)) (sq_mem_pos 𝒜 (Q.hE i))
          (by change c * Q.E i * (c * Q.E i) * g0 * f1 = _; ring)]
        exact P.mul_mem_left _ (hmem (d := e 1) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 2 _ (Q.hE' i) ?_
        intro j hj c hc
        obtain rfl : j = -2 := by omega
        apply key
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1
          (m0 (hmul (i := -4) (j := 2) (by norm_num) (hmul (i := -2) (j := -2) (by norm_num) hc hg0) hf1))
          (Q.hE' i) (by change c * Q.E' i * g0 * f1 = _; ring)]
        exact P.mul_mem_left _ (hmem (d := e 1) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 0 _ (Q.hZ i).1 ?_
        intro j hj c hc
        obtain rfl : j = 0 := by omega
        have : (⟨c * Q.Z i, hmul hj hc (Q.hZ i).1⟩ : 𝒜 0) = ⟨c, hc⟩ * ⟨Q.Z i, (Q.hZ i).1⟩ := rfl
        rw [this, map_mul]
        exact P.mul_mem_left _ (hZ i)
    | zero => intro a; simp
    | add y z _ _ hy hz =>
      intro a
      rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, map_add]
      exact P.add_mem (hy a) (hz a)
    | smul c y _ hy =>
      intro a
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (a * c)
  have h1 := hall _ hb 1
  rw [one_mul] at h1
  convert h1 using 2
  apply Subtype.ext
  exact (DirectSum.decompose_of_mem_same 𝒜 b.2).symm
