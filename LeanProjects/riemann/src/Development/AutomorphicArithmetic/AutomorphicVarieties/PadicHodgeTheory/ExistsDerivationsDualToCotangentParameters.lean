import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
open IsLocalRing UpperTheory.V.Alg

theorem UpperTheory.exists_derivations_dual_to_cotangent_parameters :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (I : Ideal R) (x : R →ₐ[O] O), I ≤ RingHom.ker x → ∃ (n : ℕ) (D : Fin n → (R →ₗ[O] E)) (t : Fin n → R) (c : O), c ≠ 0 ∧ (∀ i a b, D i (a * b) = algebraMap O E (x a) * D i b + algebraMap O E (x b) * D i a) ∧ (∀ i, ∀ a ∈ I, D i a = 0) ∧ (∀ i, x (t i) = 0) ∧ (∀ i j, D j (t i) = if j = i then algebraMap O E c else 0) ∧ ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I := by
  intro O E _ _ _ _ _ R _ _ _ I x hI
  classical
  set p : Ideal R := RingHom.ker x with hp
  have hmem : ∀ a, a ∈ p ↔ x a = 0 := fun a => RingHom.mem_ker
  let J : Ideal R := p ^ 2 ⊔ I
  have hJp : J ≤ p := sup_le (Ideal.pow_le_self two_ne_zero) hI
  let N : Submodule O R := Submodule.span O {(1 : R)} ⊔ J.restrictScalars O
  let f : (R ⧸ N) →ₗ[O] TensorProduct O E (R ⧸ N) := TensorProduct.mk O E (R ⧸ N) 1
  let π : R →ₗ[O] TensorProduct O E (R ⧸ N) := f ∘ₗ N.mkQ
  have hπN : ∀ a ∈ N, π a = 0 := by
    intro a ha
    have : N.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero N).2 ha
    simp only [π, LinearMap.comp_apply, this, map_zero]
  have hJN : ∀ a ∈ J, a ∈ N := fun a ha => Submodule.mem_sup_right (by simpa using ha)
  have h1N : (1 : R) ∈ N := Submodule.mem_sup_left (Submodule.subset_span rfl)
  have hsub : ∀ a : R, a - x a • (1 : R) ∈ p := by
    intro a
    rw [hmem]
    simp
  have hder : ∀ a b, π (a * b) = x a • π b + x b • π a := by
    intro a b
    have h1 : (a - x a • (1 : R)) * (b - x b • (1 : R)) ∈ N := by
      apply hJN
      apply Submodule.mem_sup_left
      rw [pow_two]
      exact Ideal.mul_mem_mul (hsub a) (hsub b)
    have h2 : a * b = (a - x a • (1 : R)) * (b - x b • (1 : R)) - (x a * x b) • (1 : R)
        + (x a • b + x b • a) := by
      simp only [Algebra.smul_def, map_mul]
      ring
    rw [h2, map_add, hπN _ (N.sub_mem h1 (N.smul_mem _ h1N))]
    simp
  have hker : ∀ a, x a = 0 → π a = 0 → ∃ e : O, e ≠ 0 ∧ e • a ∈ J := by
    intro a ha h
    have h' : f (N.mkQ a) = 0 := h
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O) f).1 h'
    refine ⟨s, nonZeroDivisors.coe_ne_zero s, ?_⟩
    have h3 : (s : O) • a ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero N]
      simpa [Submonoid.smul_def] using hs
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h3
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have hv' : v ∈ J := by simpa using hv
    have hxv : x v = 0 := (hmem v).1 (hJp hv')
    have := congrArg x huv
    simp [hxv, ha] at this
    rw [← huv, this]
    simpa using hv'
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian p)
  have hgp : ∀ i, x (g i) = 0 := fun i => (hmem _).1 (hg ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span E (Set.range (π ∘ g)) = ⊤ := by
    have key : ∀ a ∈ p, π a ∈ Submodule.span E (Set.range (π ∘ g)) := by
      intro a ha
      rw [← hg] at ha
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha
      rw [map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_eq_mul, hder, hgp, zero_smul, add_zero, ← IsScalarTower.algebraMap_smul E]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have key2 : ∀ a, π a ∈ Submodule.span E (Set.range (π ∘ g)) := by
      intro a
      have := key _ (hsub a)
      rwa [map_sub, hπN _ (N.smul_mem _ h1N), sub_zero] at this
    rw [eq_top_iff]
    rintro v -
    induction v with
    | zero => exact Submodule.zero_mem _
    | add u v hu hv => exact Submodule.add_mem _ hu hv
    | tmul e q =>
      obtain ⟨a, rfl⟩ := N.mkQ_surjective q
      have : e ⊗ₜ[O] N.mkQ a = e • π a := by
        simp [π, f, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (key2 a)
  obtain ⟨κ, a, hainj, hsp, hli⟩ := exists_linearIndependent' E (π ∘ g)
  haveI : Finite κ := Finite.of_injective a hainj
  obtain ⟨n, ⟨ε⟩⟩ := Finite.exists_equiv_fin κ
  let b0 : Module.Basis κ E (TensorProduct O E (R ⧸ N)) :=
    Module.Basis.mk hli (by rw [hsp, hspan])
  let b := b0.reindex ε
  let t : Fin n → R := fun i => g (a (ε.symm i))
  have hbt : ∀ i, π (t i) = b i := by
    intro i
    simp [b, b0, t]
  refine ⟨n, fun i => ((b.coord i).restrictScalars O) ∘ₗ π, t, 1, one_ne_zero, ?_, ?_, ?_, ?_, ?_⟩
  · intro i u v
    rw [LinearMap.comp_apply, hder, map_add, map_smul, map_smul, Algebra.smul_def, Algebra.smul_def]
    rfl
  · intro i u hu
    simp [hπN u (hJN u (Submodule.mem_sup_right hu))]
  · intro i
    exact hgp _
  · intro i j
    simp [hbt, Finsupp.single_apply, eq_comm]
  · intro u hu
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      (fun i => b.repr (π u) i)
    choose o ho using hd
    have h0 : π ((d : O) • u - ∑ i, o i • t i) = 0 := by
      rw [map_sub, map_smul, map_sum, sub_eq_zero]
      conv_lhs => rw [← b.sum_repr (π u), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hbt, ← IsScalarTower.algebraMap_smul E (o i), ho, smul_assoc]
    obtain ⟨e, he, hJ⟩ := hker _ (by simp [hu, t, hgp]) h0
    refine ⟨e * d, fun i => e * o i, mul_ne_zero he (nonZeroDivisors.coe_ne_zero d), ?_⟩
    simpa [smul_sub, Finset.smul_sum, mul_smul] using hJ
