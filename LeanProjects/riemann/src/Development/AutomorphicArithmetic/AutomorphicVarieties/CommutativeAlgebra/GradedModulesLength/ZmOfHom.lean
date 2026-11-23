import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ExistsSecNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NsPoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FtHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.OzTwoMulEqPow

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

namespace UpperTheory.V.Alg.M

section Abs

variable {O A R : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R]

private def zmJ (ι : ℕ → A →+ R) (p : Ideal R) : Ideal A where
  carrier := {a | ∀ h n, ι n (h * a) ∈ p}
  add_mem' {a b} ha hb h n := by rw [mul_add, map_add]; exact add_mem (ha h n) (hb h n)
  zero_mem' h n := by simp
  smul_mem' c a ha h n := by rw [smul_eq_mul, ← mul_assoc]; exact ha _ n

variable (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (ι : ℕ → A →+ R) (p : Ideal R)

private theorem zm_of_hom (h0 : ∀ (n : ℕ) j a, a ∈ 𝒜 j → j ≠ -(2 * n) → ι n a = 0) {j : ℤ} {g : A} (hg : g ∈ 𝒜 j)
    (H : ∀ (n : ℕ) h, h ∈ 𝒜 (-(2 * n) - j) → ι n (h * g) ∈ p) : g ∈ zmJ ι p := by
  classical
  show ∀ h n, ι n (h * g) ∈ p
  intro h n
  rw [← DirectSum.sum_support_decompose 𝒜 h, Finset.sum_mul, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  by_cases hi : i = -(2 * (n : ℤ)) - j
  · subst hi
    exact H n _ (SetLike.coe_mem _)
  · rw [h0 n (i + j) _ (SetLike.GradedMul.mul_mem (SetLike.coe_mem _) hg) (by omega)]
    exact p.zero_mem

private theorem zm_abs (hp : p.IsPrime) (h0 : ∀ (n : ℕ) j a, a ∈ 𝒜 j → j ≠ -(2 * n) → ι n a = 0)
    (hm : ∀ (n m : ℕ) a b, a ∈ 𝒜 (-(2 * n)) → b ∈ 𝒜 (-(2 * m)) → ι (n + m) (a * b) = ι n a * ι m b)
    {f : A} (hf : f ∈ 𝒜 (-2)) (hfp : ι 1 f ∉ p) :
    (∀ j g, g ∈ 𝒜 j → g ^ 2 ∈ zmJ ι p → g ∈ zmJ ι p) ∧ (∀ j g, g ∈ 𝒜 j → f * g ∈ zmJ ι p → g ∈ zmJ ι p) ∧
    (∀ b, b ∈ 𝒜 0 → ι 0 b ∈ p → b ∈ zmJ ι p) ∧ (∀ b, b ∈ 𝒜 (-2) → ι 1 b ∈ p → b ∈ zmJ ι p) ∧
    (∀ b (n : ℕ), b ∈ 𝒜 0 → ι 0 b ∉ p → b * f ^ n ∉ zmJ ι p) := by
  have mul' : ∀ {i j k : ℤ} {a b : A}, a ∈ 𝒜 i → b ∈ 𝒜 j → i + j = k → a * b ∈ 𝒜 k :=
    fun ha hb h => h ▸ SetLike.GradedMul.mul_mem ha hb
  have hf1 : f ∈ 𝒜 (-(2 * ((1 : ℕ) : ℤ))) := by simpa using hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j g hg hg2
    refine zm_of_hom 𝒜 ι p h0 hg fun n h hh => ?_
    have hu : h * g ∈ 𝒜 (-(2 * (n : ℤ))) := mul' hh hg (by ring)
    have h2 := (show ∀ h n, ι n (h * g ^ 2) ∈ p from hg2) (h ^ 2) (n + n)
    rw [show h ^ 2 * g ^ 2 = (h * g) * (h * g) by ring, hm n n _ _ hu hu] at h2
    exact (hp.mem_or_mem h2).elim id id
  · intro j g hg hfg
    refine zm_of_hom 𝒜 ι p h0 hg fun n h hh => ?_
    have hu : h * g ∈ 𝒜 (-(2 * (n : ℤ))) := mul' hh hg (by ring)
    have h2 := (show ∀ h n, ι n (h * (f * g)) ∈ p from hfg) h (1 + n)
    rw [show h * (f * g) = f * (h * g) by ring, hm 1 n _ _ hf1 hu] at h2
    exact (hp.mem_or_mem h2).resolve_left hfp
  · intro b hb hbp
    refine zm_of_hom 𝒜 ι p h0 hb fun n h hh => ?_
    have hh' : h ∈ 𝒜 (-(2 * (n : ℤ))) := by simpa using hh
    have e := hm n 0 h b hh' (by simpa using hb)
    rw [add_zero] at e
    rw [e]
    exact p.mul_mem_left _ hbp
  · intro b hb hbp
    refine zm_of_hom 𝒜 ι p h0 hb fun n h hh => ?_
    have hfh : f * h ∈ 𝒜 (-(2 * (n : ℤ))) := mul' hf hh (by ring)
    have e1 := hm n 1 (f * h) b hfh (by simpa using hb)
    have e2 := hm 1 n f (h * b) hf1 (mul' hh hb (by ring))
    rw [mul_assoc, add_comm, e2] at e1
    have h3 : ι 1 f * ι n (h * b) ∈ p := e1 ▸ p.mul_mem_left _ hbp
    exact (hp.mem_or_mem h3).resolve_left hfp
  · intro b n hb hbp hmem
    have key : ∀ m : ℕ, b * f ^ m ∈ 𝒜 (-(2 * (m : ℤ))) ∧ ι m (b * f ^ m) = ι 0 b * ι 1 f ^ m := by
      intro m
      induction m with
      | zero => simpa using hb
      | succ m ih =>
        have e := hm m 1 (b * f ^ m) f ih.1 hf1
        refine ⟨?_, ?_⟩
        · rw [pow_succ, ← mul_assoc]
          exact mul' ih.1 hf (by push_cast; ring)
        · rw [pow_succ, ← mul_assoc, e, ih.2, pow_succ, mul_assoc]
    have h2 := (show ∀ c k, ι k (c * (b * f ^ n)) ∈ p from hmem) 1 n
    rw [one_mul, (key n).2] at h2
    rcases hp.mem_or_mem h2 with h | h
    · exact hbp h
    · exact hfp (hp.mem_of_pow_mem _ h)

end Abs

private theorem zm_lat {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)
    (i : Fin k) (n : ℕ) : lat N (Finsupp.single i n) = N i ^ n := by
  simp [lat, Finsupp.prod_single_index, Finsupp.single_apply]

private theorem zm_iota {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
    (F : A) (hpow : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n) :
    ∃ ι : ℕ → A →+ rees (mN 𝒜 F), (∀ (n : ℕ) j a, a ∈ 𝒜 j → j ≠ -(2 * n) → ι n a = 0) ∧
      ∀ (n : ℕ) a, a ∈ 𝒜 (-(2 * n)) → (ι n a).1 = MvPolynomial.monomial (Finsupp.single 0 n) a := by
  classical
  have hmem : ∀ (n : ℕ) (b : A), b ∈ 𝒜 (-(2 * (n : ℤ))) → b ∈ lat (mN 𝒜 F) (Finsupp.single 0 n) := by
    intro n b hb
    rw [zm_lat, show mN 𝒜 F 0 = oz 𝒜 (-2) from rfl, ← hpow, mem_oz]
    exact hb
  let ι : ℕ → A →+ rees (mN 𝒜 F) := fun n =>
    { toFun := fun a => mono (mN 𝒜 F) (Finsupp.single 0 n) (DirectSum.decompose 𝒜 a (-(2 * (n : ℤ))) : A)
        (hmem n _ (SetLike.coe_mem _))
      map_zero' := by
        apply Subtype.ext
        show MvPolynomial.monomial _ _ = _
        simp
      map_add' := fun a b => by
        apply Subtype.ext
        show MvPolynomial.monomial _ _ = MvPolynomial.monomial _ _ + MvPolynomial.monomial _ _
        simp [map_add] }
  refine ⟨ι, ?_, ?_⟩
  · intro n j a ha hj
    apply Subtype.ext
    show MvPolynomial.monomial _ _ = _
    rw [DirectSum.decompose_of_mem_ne 𝒜 ha hj]
    simp
  · intro n a ha
    show MvPolynomial.monomial _ _ = _
    rw [DirectSum.decompose_of_mem_same 𝒜 ha]

private theorem zm_f {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)
    (p : Ideal (rees N)) (hp : ¬ Irr (reesGr N) ≤ p) (i : Fin k) : ∃ f, ∃ hf : f ∈ N i, sec N i f hf ∉ p := by
  classical
  have hdeg : toDeg (Finsupp.single i 1) = e i := by
    unfold toDeg e
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
  have hle : Irr (reesGr N) ≤ Ideal.span (reesGr N (e i) : Set (rees N)) := by
    unfold Irr
    exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))
  by_contra hcon
  push_neg at hcon
  apply hp
  refine hle.trans (Ideal.span_le.mpr ?_)
  intro s hs
  have hs' : ∀ m : Fin k →₀ ℕ, toDeg m ≠ e i → MvPolynomial.coeff m s.1 = 0 := hs
  have hc : MvPolynomial.coeff (Finsupp.single i 1) s.1 ∈ N i := by
    rw [← lat_single N i]
    exact s.2 _
  have hval : s = sec N i _ hc := by
    apply Subtype.ext
    show s.1 = MvPolynomial.monomial (Finsupp.single i 1) _
    ext m
    rw [MvPolynomial.coeff_monomial]
    by_cases hm : Finsupp.single i 1 = m
    · rw [if_pos hm, hm]
    · rw [if_neg hm]
      apply hs'
      intro h
      exact hm (toDeg_injective (hdeg.trans h.symm))
  rw [hval]
  exact hcon _ hc

end UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.zm_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ p : Ideal (mR Q), p.IsPrime → ¬ Irr (mGr Q) ≤ p → secs (ts Q) ≤ p → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ p) →
      (idD 𝒜).map (algebraMap (𝒜 0) (mR Q)) ≤ p → ∀ σ : 𝒜 0 →ₐ[O] K, RingHom.ker σ = p.comap (algebraMap (𝒜 0) (mR Q)) →
      ∃ ξ : A →ₐ[O] K, OnS Q.ideal ξ ∧ PosZero 𝒜 ξ ∧ ¬ NegZero 𝒜 ξ ∧ res0 𝒜 ξ = σ := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q p hp hirr hts hZ hD σ hσ
  classical
  set F := Q.F (Fin.last r) with hFdef
  have hpow := fun n : ℕ => oz_two_mul_eq_pow O A 𝒜 x hW n
  obtain ⟨ι, h0, h1⟩ := zm_iota 𝒜 F (fun n => (hpow n).1)
  have hm : ∀ (n k : ℕ) a b, a ∈ 𝒜 (-(2 * (n : ℤ))) → b ∈ 𝒜 (-(2 * (k : ℤ))) →
      ι (n + k) (a * b) = ι n a * ι k b := by
    intro n k a b ha hb
    apply Subtype.ext
    have hab : a * b ∈ 𝒜 (-(2 * ((n + k : ℕ) : ℤ))) := by
      have := SetLike.GradedMul.mul_mem ha hb
      convert this using 2
      push_cast
      ring
    rw [Subalgebra.coe_mul, h1 _ _ hab, h1 _ _ ha, h1 _ _ hb, MvPolynomial.monomial_mul, Finsupp.single_add]
  obtain ⟨f, hfN, hfp⟩ := zm_f (mN 𝒜 F) p hirr 0
  have hf : f ∈ 𝒜 (-2) := (mem_oz 𝒜).1 hfN
  have hf1 : f ∈ 𝒜 (-(2 * ((1 : ℕ) : ℤ))) := by simpa using hf
  have hfp' : ι 1 f ∉ p := by
    have e : ι 1 f = sec (mN 𝒜 F) 0 f hfN := by
      apply Subtype.ext
      rw [h1 1 f hf1]
      rfl
    rw [e]
    exact hfp
  obtain ⟨A1, A2, A3, A4, A5⟩ := zm_abs 𝒜 ι p hp h0 hm hf hfp'
  have hι0 : ∀ b : 𝒜 0, ι 0 (b : A) = algebraMap (𝒜 0) (mR Q) b := by
    intro b
    apply Subtype.ext
    rw [h1 0 b (by simpa using b.2)]
    show _ = algebraMap (𝒜 0) (MvPolynomial (Fin 3) A) b
    rw [Finsupp.single_zero, ← MvPolynomial.C_apply, MvPolynomial.algebraMap_apply]
    rfl
  have hJ0 : ∀ b : 𝒜 0, algebraMap (𝒜 0) (mR Q) b ∈ p → (b : A) ∈ zmJ ι p := by
    intro b hb
    apply A3 b b.2
    rw [hι0]
    exact hb
  have h2 : ∀ g ∈ 𝒜 2, g ∈ zmJ ι p := by
    intro g hg
    apply A2 2 g hg
    have hfg : f * g ∈ 𝒜 0 := by
      have := SetLike.GradedMul.mul_mem hf hg
      simpa using this
    have hmem : (⟨f * g, hfg⟩ : 𝒜 0) ∈ idD 𝒜 := Ideal.subset_span ⟨f, hf, g, hg, rfl⟩
    exact hJ0 ⟨f * g, hfg⟩ (hD (Ideal.mem_map_of_mem _ hmem))
  have hpos : ∀ j > (0 : ℤ), ∀ g ∈ 𝒜 j, g ∈ zmJ ι p := by
    intro j hj g hg
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = ((n + 1 : ℕ) : ℤ) := ⟨(j - 1).toNat, by omega⟩
    apply A1 _ g hg
    have hg2 : g ^ 2 ∈ oz 𝒜 2 ^ (n + 1) := by
      rw [← (hpow (n + 1)).2, mem_oz]
      have := SetLike.pow_mem_graded 2 hg
      convert this using 2
      rw [nsmul_eq_mul]
      push_cast
      ring
    have hle : oz 𝒜 2 ^ (n + 1) ≤ (zmJ ι p).restrictScalars (𝒜 0) := by
      rw [pow_succ, Submodule.mul_le]
      intro a _ b hb
      exact (zmJ ι p).mul_mem_left a (h2 b ((mem_oz 𝒜).1 hb))
    exact hle hg2
  have hF : ∀ i, Q.F i ∈ zmJ ι p := by
    intro i
    apply A1 (-1) _ (Q.hF i)
    have hsq := sq_mem_neg 𝒜 (Q.hF i)
    apply A4 _ hsq
    have := (zi_holds O A 𝒜 x hW r s r' s' m Q p hp hirr hts hZ).2 i
    convert this using 1
    apply Subtype.ext
    rw [h1 1 _ (by simpa using hsq)]
    rfl
  have hG : ∀ i, Q.G i ∈ zmJ ι p := by
    intro i
    apply A4 _ (Q.hG i)
    have hmem : sec (mN 𝒜 F) 0 (Q.G i) ((mem_oz 𝒜).2 (Q.hG i)) ∈ p := by
      apply hts
      apply Ideal.subset_span
      refine ⟨e 0, ?_⟩
      show _ ∈ tsF Q ++ tsR Q
      refine List.mem_append.2 (Or.inr ?_)
      refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl ?_)))))
      rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    convert hmem using 1
    apply Subtype.ext
    rw [h1 1 _ (by simpa using Q.hG i)]
    rfl
  have hI : Q.ideal ≤ zmJ ι p := by
    unfold Eqns.ideal
    rw [Ideal.span_le]
    rintro a ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact hF i
    · exact hG i
    · exact hpos 1 one_pos _ (Q.hE i)
    · exact hpos 2 two_pos _ (Q.hE' i)
    · exact hJ0 ⟨Q.Z i, (Q.hZ i).1⟩ (hZ i)
  have ha : ∀ b : 𝒜 0, σ b = 0 → algebraMap (𝒜 0) A b ∈ zmJ ι p := by
    intro b hb
    have hk : b ∈ RingHom.ker σ := by
      rw [RingHom.mem_ker]
      exact hb
    rw [hσ, Ideal.mem_comap] at hk
    exact hJ0 b hk
  have hb' : ∀ (b : 𝒜 0) (n : ℕ), σ b ≠ 0 → algebraMap (𝒜 0) A b * f ^ n ∉ zmJ ι p := by
    intro b n hb
    apply A5 b n b.2
    intro hmem
    apply hb
    have hk : b ∈ RingHom.ker σ := by
      rw [hσ, Ideal.mem_comap, ← hι0]
      exact hmem
    rw [RingHom.mem_ker] at hk
    exact hk
  haveI := (ft_holds O A 𝒜 x hW).1
  obtain ⟨ξ, hξ1, hξ2, hξ3⟩ := ns_holds O (𝒜 0) A K σ (zmJ ι p) f ha hb'
  refine ⟨ξ, ?_, ?_, ?_, ?_⟩
  · show ∀ g ∈ Q.ideal, ξ g = 0
    intro g hg
    exact hξ2 g (hI hg)
  · show ∀ j > 0, ∀ g ∈ 𝒜 j, ξ g = 0
    intro j hj g hg
    exact hξ2 g (hpos j hj g hg)
  · intro hneg
    exact hξ3 (hneg (-2) (by norm_num) f hf)
  · apply AlgHom.ext
    intro b
    exact hξ1 b
