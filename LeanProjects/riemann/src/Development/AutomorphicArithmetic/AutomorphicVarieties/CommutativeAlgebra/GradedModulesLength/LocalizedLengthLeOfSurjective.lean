import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.OzTwoMulEqPow

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem localized_length_le_of_surjective {O B K : Type} [CommRing O] [CommRing B] [Algebra O B] [Field K] [Algebra O K]
    (σ : B →ₐ[O] K) {L M N : Type} [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (φ : L →ₗ[B] M) (ψ : L →ₗ[B] N) (hφ : Function.Surjective φ)
    (h : ∀ x, ψ x = 0 → ∃ t : B, σ t ≠ 0 ∧ t • φ x = 0) : locLen σ M ≤ locLen σ N := by
  haveI : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
  unfold locLen
  set S := (RingHom.ker σ).primeCompl
  have hs : Function.Surjective (LocalizedModule.map S φ) := LocalizedModule.map_surjective S φ hφ
  have hk : LinearMap.ker (LocalizedModule.map S ψ) ≤ LinearMap.ker (LocalizedModule.map S φ) := by
    intro y hy
    induction y using LocalizedModule.induction_on with
    | h x s =>
      rw [LinearMap.mem_ker, LocalizedModule.map_mk] at hy ⊢
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hy ⊢
      obtain ⟨u, hu⟩ := hy
      have h1 : ψ ((u : B) • x) = 0 := by simpa [Submonoid.smul_def] using hu
      obtain ⟨t, ht, h2⟩ := h _ h1
      refine ⟨⟨t, ht⟩ * u, ?_⟩
      simpa [Submonoid.smul_def, mul_smul] using h2
  have hs2 : Function.Surjective ((LinearMap.ker (LocalizedModule.map S ψ)).liftQ (LocalizedModule.map S φ) hk) := by
    intro y
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  refine (Module.length_le_of_surjective _ hs2).trans ?_
  exact Module.length_le_of_injective ((LinearMap.ker (LocalizedModule.map S ψ)).liftQ (LocalizedModule.map S ψ) le_rfl)
    (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))

section

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

private def u4w (μ : Fin 3 →₀ ℕ) : ℤ := 2 * ((μ 1 : ℤ) - μ 0 - μ 2)

private theorem weight_submodule_mul_le (i j : ℤ) : oz 𝒜 i * oz 𝒜 j ≤ oz 𝒜 (i + j) :=
  Submodule.mul_le.2 fun _ ha _ hb => (mem_oz 𝒜).2 (SetLike.GradedMul.mul_mem ((mem_oz 𝒜).1 ha) ((mem_oz 𝒜).1 hb))

private theorem weight_submodule_pow_le {P : Submodule (𝒜 0) A} {i : ℤ} (h : P ≤ oz 𝒜 i) (n : ℕ) : P ^ n ≤ oz 𝒜 (n * i) := by
  induction n with
  | zero =>
    rw [pow_zero, Submodule.one_le]
    simpa using (SetLike.GradedOne.one_mem : (1 : A) ∈ 𝒜 0)
  | succ n ih =>
    rw [pow_succ]
    refine (mul_le_mul' ih h).trans ((weight_submodule_mul_le 𝒜 _ _).trans (le_of_eq ?_))
    congr 1; push_cast; ring

private theorem lattice_le_weight_submodule {F : A} (hF : F ∈ 𝒜 (-1)) (μ : Fin 3 →₀ ℕ) : lat (mN 𝒜 F) μ ≤ oz 𝒜 (u4w μ) := by
  have h2 : mN 𝒜 F 2 ≤ oz 𝒜 (-2) := by
    show Submodule.span (𝒜 0) {F ^ 2} ⊔ oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 ≤ _
    refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (sq_mem_neg 𝒜 hF)) ?_
    exact (mul_le_mul' (weight_submodule_mul_le 𝒜 _ _) le_rfl).trans (weight_submodule_mul_le 𝒜 _ _)
  have h0 : mN 𝒜 F 0 ≤ oz 𝒜 (-2) := le_rfl
  have h1 : mN 𝒜 F 1 ≤ oz 𝒜 2 := le_rfl
  rw [lat, Fin.prod_univ_three]
  refine (mul_le_mul' ((mul_le_mul' (weight_submodule_pow_le 𝒜 h0 _) (weight_submodule_pow_le 𝒜 h1 _)).trans (weight_submodule_mul_le 𝒜 _ _))
    (weight_submodule_pow_le 𝒜 h2 _)).trans ((weight_submodule_mul_le 𝒜 _ _).trans (le_of_eq ?_))
  congr 1; unfold u4w; ring

private theorem power_mul_mem_lattice (hp : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n ∧ oz 𝒜 (2 * n) = oz 𝒜 2 ^ n)
    (F : A) {f g : A} (hf : f ∈ 𝒜 (-2)) (hg : g ∈ 𝒜 2) (μ : Fin 3 →₀ ℕ) {a : A} (ha : a ∈ 𝒜 (u4w μ)) :
    ∃ n : ℕ, (f * g) ^ n * a ∈ lat (mN 𝒜 F) μ := by
  have hl : oz 𝒜 (-2) ^ (μ 0 + 2 * μ 2) * oz 𝒜 2 ^ (μ 1 + μ 2) ≤ lat (mN 𝒜 F) μ := by
    have h2 : oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 ≤ mN 𝒜 F 2 := le_sup_right
    rw [lat, Fin.prod_univ_three]
    refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl (pow_le_pow_left' h2 (μ 2)))
    show _ = oz 𝒜 (-2) ^ μ 0 * oz 𝒜 2 ^ μ 1 * _
    ring
  have hfg : ∀ n : ℕ, (f * g) ^ n ∈ oz 𝒜 (-2) ^ n * oz 𝒜 2 ^ n := fun n => by
    rw [mul_pow]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow (oz 𝒜 (-2)) hf n) (Submodule.pow_mem_pow (oz 𝒜 2) hg n)
  rcases le_total (μ 0 + 2 * μ 2) (μ 1 + μ 2) with h | h
  · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le h
    refine ⟨μ 0 + 2 * μ 2, hl ?_⟩
    have ha' : a ∈ oz 𝒜 2 ^ c := by
      rw [← (hp c).2, mem_oz]
      have : u4w μ = 2 * c := by unfold u4w; omega
      rwa [this] at ha
    rw [hc, pow_add (oz 𝒜 2) _ c, ← mul_assoc]
    exact Submodule.mul_mem_mul (hfg _) ha'
  · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le h
    refine ⟨μ 1 + μ 2, hl ?_⟩
    have ha' : a ∈ oz 𝒜 (-2) ^ c := by
      rw [← (hp c).1, mem_oz]
      have : u4w μ = -(2 * c) := by unfold u4w; omega
      rwa [this] at ha
    rw [hc, pow_add (oz 𝒜 (-2)) _ c, mul_right_comm]
    exact Submodule.mul_mem_mul (hfg _) ha'

private def u4K (F : A) (b : 𝒜 0) (J : Ideal (rees (mN 𝒜 F))) (μ : Fin 3 →₀ ℕ) : AddSubmonoid A where
  carrier := {a | ∃ n : ℕ, ∃ p ∈ J, p.1 = MvPolynomial.monomial μ ((b : A) ^ n * a)}
  zero_mem' := ⟨0, 0, J.zero_mem, by simp⟩
  add_mem' := by
    rintro a a' ⟨n, p, hp, e⟩ ⟨n', p', hp', e'⟩
    refine ⟨n + n', b ^ n' • p + b ^ n • p',
      J.add_mem (Submodule.smul_of_tower_mem _ _ hp) (Submodule.smul_of_tower_mem _ _ hp'), ?_⟩
    show b ^ n' • p.1 + b ^ n • p'.1 = _
    rw [e, e', MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, ← map_add]
    congr 1
    show ((b ^ n' : 𝒜 0) : A) * _ + ((b ^ n : 𝒜 0) : A) * _ = _
    simp only [SetLike.GradeZero.coe_pow]
    ring

private theorem generated_component_mem (hp : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n ∧ oz 𝒜 (2 * n) = oz 𝒜 2 ^ n)
    (F : A) {f g : A} (hf : f ∈ 𝒜 (-2)) (hg : g ∈ 𝒜 2) (b : 𝒜 0) (hb : (b : A) = f * g)
    (J : Ideal (rees (mN 𝒜 F))) (μ ν : Fin 3 →₀ ℕ) (hν : ν ≤ μ) {y : A} (hy : y ∈ 𝒜 (u4w ν))
    (q : rees (mN 𝒜 F)) (hq : q ∈ J) (e : q.1 = MvPolynomial.monomial ν y) (c : A) :
    (DirectSum.decompose 𝒜 (c * y) (u4w μ) : A) ∈ u4K 𝒜 F b J μ := by
  obtain ⟨ν', rfl⟩ := exists_add_of_le hν
  have hw : u4w (ν + ν') = u4w ν' + u4w ν := by
    simp only [u4w, Finsupp.add_apply]; push_cast; ring
  rw [hw, DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hy]
  obtain ⟨n, hn⟩ := power_mul_mem_lattice 𝒜 hp F hf hg ν' (DirectSum.decompose 𝒜 c (u4w ν')).2
  refine ⟨n, mono _ ν' _ hn * q, J.mul_mem_left _ hq, ?_⟩
  show MvPolynomial.monomial ν' _ * q.1 = _
  rw [e, MvPolynomial.monomial_mul, add_comm, hb, mul_assoc]

end

theorem UpperTheory.V.Alg.M.locLen_mQ_gr_le_locLen_aPiece :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ J : Ideal (mR Q), secs (ts Q) ≤ J → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ J) →
    ∀ σ : 𝒜 0 →ₐ[O] K, ¬ idD 𝒜 ≤ RingHom.ker σ → ∀ d : Deg 3, 1 ≤ d →
      locLen σ ((mQ Q J).gr d) ≤ locLen σ (aPiece 𝒜 (ideal2 Q) (2 * (d 1 - d 0 - d 2))) := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q J hJ hZ σ hσ d hd
  have hp := oz_two_mul_eq_pow O A 𝒜 x hW
  obtain ⟨b, ⟨f, hf, g, hg, hb⟩, hbσ⟩ : ∃ b : 𝒜 0, (∃ f ∈ 𝒜 (-2), ∃ g ∈ 𝒜 2, (b : A) = f * g) ∧ σ b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hσ (Ideal.span_le.2 fun b ⟨f, hf, g, hg, hb⟩ => hcon b ⟨f, hf, g, hg, hb⟩)
  obtain ⟨μ, rfl⟩ : ∃ μ : Fin 3 →₀ ℕ, toDeg μ = d :=
    ⟨Finsupp.equivFunOnFinite.symm fun i => (d i).toNat, funext fun i => by
      have : (1 : ℤ) ≤ d i := hd i
      simp only [toDeg, Finsupp.equivFunOnFinite_symm_apply_apply]
      omega⟩
  have hμ : ∀ i, Finsupp.single i 1 ≤ μ := fun i => by
    have : (1 : ℤ) ≤ (μ i : ℤ) := hd i
    rw [Finsupp.single_le_iff]; omega
  have hsec : ∀ (i : Fin 3) (y : A) (hy : y ∈ mN 𝒜 (Q.F (Fin.last r)) i), (e i, sec _ i y hy) ∈ ts Q →
      ∀ c : A, (DirectSum.decompose 𝒜 (c * y) (u4w μ) : A) ∈ u4K 𝒜 _ b J μ := fun i y hy hm =>
    generated_component_mem 𝒜 hp _ hf hg b hb J μ _ (hμ i)
      (lattice_le_weight_submodule 𝒜 (Q.hF (Fin.last r)) _ (by rw [lat_single]; exact hy)) _ (hJ (Ideal.subset_span ⟨_, hm⟩)) rfl
  have hI : ∀ y ∈ ideal2 Q, ∀ c : A, (DirectSum.decompose 𝒜 (c * y) (u4w μ) : A) ∈ u4K 𝒜 _ b J μ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
      · induction i using Fin.lastCases with
        | last =>
          exact hsec 2 _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
            (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)))
        | cast i =>
          exact hsec 0 _ (sq_mem_neg 𝒜 (Q.hF _)) (List.mem_append_left _ (List.mem_ofFn.2 ⟨i, rfl⟩))
      · exact hsec 0 _ (Q.hG i) (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_ofFn.2 ⟨i, rfl⟩)))))
      · exact hsec 1 _ (sq_mem_pos 𝒜 (Q.hE i)) (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.2 ⟨i, rfl⟩)))))
      · exact hsec 1 _ (Q.hE' i) (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_ofFn.2 ⟨i, rfl⟩))))
      · exact generated_component_mem 𝒜 hp _ hf hg b hb J μ 0 bot_le (Q.hZ i).1 _ (hZ i) rfl
    | zero => intro c; simp
    | add y z _ _ h1 h2 =>
      intro c
      rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact add_mem (h1 c) (h2 c)
    | smul a y _ h1 =>
      intro c
      rw [smul_eq_mul, ← mul_assoc]
      exact h1 _
  let φ0 : lat (mN 𝒜 (Q.F (Fin.last r))) μ →ₗ[𝒜 0] mR Q :=
    { toFun := fun h => mono _ μ h.1 h.2
      map_add' := fun h h' => Subtype.ext (map_add (MvPolynomial.monomial μ) h.1 h'.1)
      map_smul' := fun c h => Subtype.ext (MvPolynomial.smul_monomial c).symm }
  let φ : lat (mN 𝒜 (Q.F (Fin.last r))) μ →ₗ[𝒜 0] (mQ Q J).gr (toDeg μ) :=
    LinearMap.codRestrict _ ((J.mkQ.restrictScalars (𝒜 0)) ∘ₗ φ0) fun h => ⟨φ0 h, mono_mem _ μ h.1 h.2, rfl⟩
  let ψ : lat (mN 𝒜 (Q.F (Fin.last r))) μ →ₗ[𝒜 0] aPiece 𝒜 (ideal2 Q) (u4w μ) :=
    LinearMap.codRestrict _ ((Ideal.Quotient.mkₐ (𝒜 0) (ideal2 Q)).toLinearMap ∘ₗ Submodule.subtype _) fun h =>
      ⟨h.1, lattice_le_weight_submodule 𝒜 (Q.hF (Fin.last r)) μ h.2, rfl⟩
  refine localized_length_le_of_surjective σ φ ψ ?_ ?_
  · rintro ⟨_, p, hp', rfl⟩
    refine ⟨⟨MvPolynomial.coeff μ p.1, p.2 μ⟩, Subtype.ext ?_⟩
    show J.mkQ (mono _ μ _ (p.2 μ)) = J.mkQ p
    congr 1
    apply Subtype.ext
    ext ν
    show MvPolynomial.coeff ν (MvPolynomial.monomial μ _) = _
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · rw [h]
    · exact (hp' ν fun h' => h (toDeg_injective h').symm).symm
  · intro h h0
    have h1 : h.1 ∈ ideal2 Q := Ideal.Quotient.eq_zero_iff_mem.1 (congrArg Subtype.val h0)
    have h2 := hI _ h1 1
    rw [one_mul, DirectSum.decompose_of_mem_same 𝒜 (lattice_le_weight_submodule 𝒜 (Q.hF (Fin.last r)) μ h.2)] at h2
    obtain ⟨n, p, hpJ, e⟩ := h2
    refine ⟨b ^ n, by rw [map_pow]; exact pow_ne_zero _ hbσ, ?_⟩
    rw [← map_smul]
    apply Subtype.ext
    show J.mkQ (φ0 (b ^ n • h)) = 0
    have : φ0 (b ^ n • h) = p := by
      apply Subtype.ext
      rw [e]
      show MvPolynomial.monomial μ (((b ^ n : 𝒜 0) : A) * h.1) = _
      rw [SetLike.GradeZero.coe_pow]
    rw [this]
    exact (Submodule.Quotient.mk_eq_zero _).2 hpJ
