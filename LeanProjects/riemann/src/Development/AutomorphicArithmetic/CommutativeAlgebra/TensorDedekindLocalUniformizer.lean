import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.AutomorphicArithmetic.CommutativeAlgebra.SpecializationTensorRingHomProperties
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPsi
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private lemma exists_psi (L T : Type) [Field L] [IsAlgClosed L] [CommRing T] [Algebra L T]
    [Algebra.FiniteType L T] (m : Ideal T) (hm : m.IsMaximal) :
    ∃ ψ : T →ₐ[L] L, ∀ x, ψ x = 0 ↔ x ∈ m :=
  _root_.UpperTheory.Reformulated.B.Qi48.exists_psi L T m hm

private lemma exists_unif (T : Type) [CommRing T] [IsDedekindDomain T] (hT : ¬ IsField T)
    (m : Ideal T) (hm : m.IsMaximal) :
    ∃ π ∈ m, π ≠ 0 ∧ ∀ c : T, c ≠ 0 →
      ∃ (s t : T) (e : ℕ), s ∉ m ∧ t ∉ m ∧ c * s = t * π ^ e := by
  have hbot : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm hT
  haveI := hm.isPrime
  let D := Localization.AtPrime m
  haveI : IsDiscreteValuationRing D :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain T hbot D
  have hinj : Function.Injective (algebraMap T D) :=
    IsLocalization.injective D m.primeCompl_le_nonZeroDivisors
  have hunit : ∀ x : T, IsUnit (algebraMap T D x) ↔ x ∉ m := fun x =>
    IsLocalization.AtPrime.isUnit_to_map_iff D m x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj m.primeCompl ϖ
  have hq : IsUnit (algebraMap T D q) := IsLocalization.map_units D q
  have hirr : Irreducible (algebraMap T D p) := by
    have h := hpq
    simp only at h
    rw [← h]
    exact (irreducible_mul_isUnit hq).mpr hϖ
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hirr
    exact not_irreducible_zero hirr
  have hpm : p ∈ m := by
    by_contra h
    exact hirr.not_isUnit ((hunit p).mpr h)
  refine ⟨p, hpm, hp0, fun c hc => ?_⟩
  have hc' : algebraMap T D c ≠ 0 := fun h => hc (hinj (by rw [h, map_zero]))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc' hirr
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.surj m.primeCompl (u : D)
  have hts' : (u : D) * algebraMap T D s = algebraMap T D t := hts
  have ht : t ∉ m := by
    rw [← hunit, ← hts']
    exact u.isUnit.mul (IsLocalization.map_units D s)
  refine ⟨t, s, n, ht, s.2, hinj ?_⟩
  rw [map_mul, map_mul, map_pow, ← hts', ← mul_assoc, hu, mul_comm]

private lemma val_unif {k B : Type} [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
    (Y : Set B) (hY : Algebra.adjoin k Y = ⊤) (χ : B →ₐ[k] k)
    (P : IsDedekindDomain.HeightOneSpectrum B) (hP : ∀ x, x ∈ P.asIdeal ↔ χ x = 0)
    (π₀ : B) (hπ : π₀ ∈ P.asIdeal)
    (h : ∀ y ∈ Y, ∃ r w : B, r ∉ P.asIdeal ∧ r * (y - algebraMap k B (χ y)) = w * π₀) :
    P.intValuation π₀ = WithZero.exp (-1 : ℤ) := by
  set I : Ideal B := Ideal.span ((fun y => y - algebraMap k B (χ y)) '' Y) with hIdef
  have hgen : ∀ y ∈ Y, P.intValuation (y - algebraMap k B (χ y)) ≤ P.intValuation π₀ := by
    intro y hy
    obtain ⟨r, w, hr, hrw⟩ := h y hy
    have h1 : P.intValuation r = 1 :=
      P.intValuation_eq_one_iff_mem_primeCompl r |>.mpr hr
    have h2 := congrArg P.intValuation hrw
    rw [map_mul, map_mul, h1, one_mul] at h2
    rw [h2]
    exact mul_le_of_le_one_left' (P.intValuation_le_one w)
  have hI : ∀ x ∈ I, P.intValuation x ≤ P.intValuation π₀ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact hgen y hy
    | zero => simp
    | add x y _ _ hx hy => exact (P.intValuation.map_add_le hx hy)
    | smul a x _ hx =>
      rw [smul_eq_mul, map_mul]
      exact (mul_le_of_le_one_left' (P.intValuation_le_one a)).trans hx
  have hdec : ∀ x : B, x - algebraMap k B (χ x) ∈ I := by
    intro x
    have hx : x ∈ Algebra.adjoin k Y := by rw [hY]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Ideal.subset_span ⟨x, hx, rfl⟩
    | algebraMap c => simp
    | add x y _ _ hx hy =>
      have : x + y - algebraMap k B (χ (x + y)) =
          (x - algebraMap k B (χ x)) + (y - algebraMap k B (χ y)) := by
        rw [map_add, map_add]; ring
      rw [this]
      exact I.add_mem hx hy
    | mul x y _ _ hx hy =>
      have : x * y - algebraMap k B (χ (x * y)) =
          x * (y - algebraMap k B (χ y)) + algebraMap k B (χ y) * (x - algebraMap k B (χ x)) := by
        rw [map_mul, map_mul]; ring
      rw [this]
      exact I.add_mem (I.mul_mem_left _ hy) (I.mul_mem_left _ hx)
  obtain ⟨ϖ, hϖ⟩ := P.intValuation_exists_uniformizer
  have hϖP : ϖ ∈ P.asIdeal := by
    rw [← P.intValuation_lt_one_iff_mem, hϖ]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hϖI : ϖ ∈ I := by
    have := hdec ϖ
    rwa [(hP ϖ).mp hϖP, map_zero, sub_zero] at this
  apply le_antisymm
  · have := (P.intValuation_le_pow_iff_mem π₀ 1).mpr (by simpa using hπ)
    simpa using this
  · rw [← hϖ]
    exact hI ϖ hϖI

private lemma spz_eval {k L B : Type} [Field k] [Field L] [Algebra k L] [CommRing B] [Algebra k B]
    (R : Subalgebra k L) (φ : R →ₐ[k] k) (ψ : L ⊗[k] B →ₐ[L] L) (ρ : B →ₐ[k] R)
    (hρ : ∀ x, ((ρ x : R) : L) = ψ ((1 : L) ⊗ₜ[k] x)) (y : L ⊗[k] B) (y₀ : B)
    (h : Spz R φ y y₀) : ∃ hy : ψ y ∈ R, φ ⟨ψ y, hy⟩ = φ (ρ y₀) := by
  obtain ⟨y', rfl, rfl⟩ := h
  let Ψ : R ⊗[k] B →ₐ[k] R := Algebra.TensorProduct.productMap (AlgHom.id k R) ρ
  have c1 : ∀ y' : R ⊗[k] B,
      ψ (Algebra.TensorProduct.map R.val (AlgHom.id k B) y') = ((Ψ y' : R) : L) := by
    intro y'
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | tmul r b =>
      have : ((r : L) ⊗ₜ[k] b : L ⊗[k] B) = (r : L) • ((1 : L) ⊗ₜ[k] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [Ψ, this, hρ]
    | add x y hx hy => simp [hx, hy]
  have c2 : ∀ y' : R ⊗[k] B, φ (Ψ y') =
      φ (ρ (Algebra.TensorProduct.lid k B
        (Algebra.TensorProduct.map φ (AlgHom.id k B) y'))) := by
    intro y'
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | tmul r b => simp [Ψ]
    | add x y hx hy => simp [hx, hy]
  have hy : ψ (Algebra.TensorProduct.map R.val (AlgHom.id k B) y') ∈ R := by
    rw [c1]; exact (Ψ y').2
  refine ⟨hy, ?_⟩
  rw [← c2]
  congr 1
  exact Subtype.ext (c1 y')

theorem UpperTheory.tensor_dedekind_local_uniformizer :
    ∀ (k L B : Type) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] [IsDedekindDomain (L ⊗[k] B)], ¬ IsField B → ¬ IsField (L ⊗[k] B) → ∀ m : Ideal (L ⊗[k] B), m.IsMaximal → ∀ a b : L ⊗[k] B, a ≠ 0 → b ≠ 0 → ∃ (π s t s' t' : L ⊗[k] B) (e e' : ℕ), π ≠ 0 ∧ s ∉ m ∧ t ∉ m ∧ s' ∉ m ∧ t' ∉ m ∧ a * s = t * π ^ e ∧ b * s' = t' * π ^ e' ∧ ∃ S : Finset L, ∀ R : Subalgebra k L, (S : Set L) ⊆ R → ∀ (φ : R →ₐ[k] k) (a₀ b₀ : B), Spz R φ a a₀ → Spz R φ b b₀ → ∃ P : IsDedekindDomain.HeightOneSpectrum B, P.intValuation a₀ = WithZero.exp (-(e : ℤ)) ∧ P.intValuation b₀ = WithZero.exp (-(e' : ℤ)) := by
  classical
  intro k L B _ _ _ _ _ _ _ _ _ _ hB hT m hm a b ha hb
  obtain ⟨hS, hE, -⟩ := UpperTheory.specialization_tensor_ring_hom_properties k L B
  obtain ⟨ψ, hψ⟩ := exists_psi L (L ⊗[k] B) m hm
  obtain ⟨π, hπm, hπ0, hdec⟩ := exists_unif (L ⊗[k] B) hT m hm
  obtain ⟨s, t, e, hs, ht, hst⟩ := hdec a ha
  obtain ⟨s', t', e', hs', ht', hst'⟩ := hdec b hb
  let ι : B → L := fun y => ψ ((1 : L) ⊗ₜ[k] y)
  let z : B → L ⊗[k] B := fun y => (1 : L) ⊗ₜ[k] y - ι y ⊗ₜ[k] (1 : B)
  have hzm : ∀ y, z y ∈ m := by
    intro y
    refine (hψ _).mp ?_
    have h1 : (ι y ⊗ₜ[k] (1 : B) : L ⊗[k] B) = algebraMap L (L ⊗[k] B) (ι y) := rfl
    simp only [z, map_sub, h1, AlgHom.commutes]
    simp [ι]
  have hz : ∀ y, ∃ r w : L ⊗[k] B, r ∉ m ∧ r * z y = w * π := by
    intro y
    by_cases h0 : z y = 0
    · exact ⟨1, 0, (Ideal.ne_top_iff_one m).mp hm.ne_top, by simp [h0]⟩
    obtain ⟨r, u, n, hr, hu, hru⟩ := hdec _ h0
    cases n with
    | zero =>
      exfalso
      apply hu
      rw [pow_zero, mul_one] at hru
      rw [← hru]
      exact m.mul_mem_right _ (hzm y)
    | succ n => exact ⟨r, u * π ^ n, hr, by rw [mul_comm, hru, pow_succ, mul_assoc]⟩
  choose r w hr hrw using hz
  obtain ⟨Y, hY⟩ := (inferInstance : Algebra.FiniteType k B).out
  let U : Finset (L ⊗[k] B) := {s, t, s', t'} ∪ Y.image r
  let E : Finset (L ⊗[k] B) := U ∪ {π} ∪ Y.image w
  have hUm : ∀ x ∈ U, x ∉ m := by
    intro x hx
    simp only [U, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hx
    rcases hx with ((rfl | rfl | rfl | rfl) | ⟨y, -, rfl⟩)
    · exact hs
    · exact ht
    · exact hs'
    · exact ht'
    · exact hr y
  choose f hf using hE
  refine ⟨π, s, t, s', t', e, e', hπ0, hs, ht, hs', ht', hst, hst',
    Y.image ι ∪ U.image (fun x => (ψ x)⁻¹) ∪ E.biUnion f, ?_⟩
  intro R hR φ a₀ b₀ ha₀ hb₀
  have hιY : ∀ y ∈ Y, ι y ∈ R := fun y hy =>
    hR (by simp only [Finset.coe_union, Finset.coe_image]
           exact Or.inl (Or.inl ⟨y, hy, rfl⟩))
  have hinv : ∀ x ∈ U, (ψ x)⁻¹ ∈ R := fun x hx =>
    hR (by simp only [Finset.coe_union, Finset.coe_image]
           exact Or.inl (Or.inr ⟨x, hx, rfl⟩))
  have hex : ∀ x ∈ E, ∃ x₀, Spz R φ x x₀ := fun x hx =>
    hf x R (fun l hl => hR (by
      simp only [Finset.coe_union, Finset.coe_biUnion]
      exact Or.inr (Set.mem_biUnion hx hl))) φ
  let ψ₀ : B →ₐ[k] L := (ψ.restrictScalars k).comp Algebra.TensorProduct.includeRight
  have hιR : ∀ x, ψ₀ x ∈ R := by
    have hle : Algebra.adjoin k (Y : Set B) ≤ R.comap ψ₀ :=
      Algebra.adjoin_le fun y hy => hιY y hy
    intro x
    have : x ∈ Algebra.adjoin k (Y : Set B) := by rw [hY]; trivial
    exact hle this
  let ρ : B →ₐ[k] R := ψ₀.codRestrict R hιR
  have hρ : ∀ x, ((ρ x : R) : L) = ψ ((1 : L) ⊗ₜ[k] x) := fun x => rfl
  let χ : B →ₐ[k] k := φ.comp ρ
  have hχ : Function.Surjective χ := fun c => ⟨algebraMap k B c, by simp⟩
  have hmax : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hχ
  let P : IsDedekindDomain.HeightOneSpectrum B :=
    ⟨RingHom.ker χ, hmax.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hmax hB⟩
  have hP : ∀ x, x ∈ P.asIdeal ↔ χ x = 0 := fun x => RingHom.mem_ker
  obtain ⟨hu, har, hc, -⟩ := hS R φ
  have hev := fun y y₀ h => spz_eval R φ ψ ρ hρ y y₀ h
  have hnot : ∀ x ∈ U, ∀ x₀, Spz R φ x x₀ → x₀ ∉ P.asIdeal := by
    intro x hx x₀ hs₀ hmem
    obtain ⟨hxR, hφ⟩ := hev x x₀ hs₀
    have h0 : φ ⟨ψ x, hxR⟩ = 0 := hφ.trans ((hP x₀).mp hmem)
    have hne : ψ x ≠ 0 := fun h => hUm x hx ((hψ x).mp h)
    have h1 : (⟨ψ x, hxR⟩ : R) * ⟨(ψ x)⁻¹, hinv x hx⟩ = 1 :=
      Subtype.ext (mul_inv_cancel₀ hne)
    have h2 := congrArg φ h1
    rw [map_mul, h0, zero_mul, map_one] at h2
    exact zero_ne_one h2
  obtain ⟨π₀, hπ₀⟩ := hex π (by simp [E])
  have hπ₀P : π₀ ∈ P.asIdeal := by
    obtain ⟨hxR, hφ⟩ := hev π π₀ hπ₀
    refine (hP π₀).mpr ?_
    have h0 : (⟨ψ π, hxR⟩ : R) = 0 := Subtype.ext ((hψ π).mpr hπm)
    rw [h0, map_zero] at hφ
    exact hφ.symm
  have hone : Spz R φ (1 : L ⊗[k] B) (1 : B) := by
    have := hc 1 1
    simpa [Algebra.TensorProduct.one_def] using this
  have hy : ∀ y : B, Spz R φ ((1 : L) ⊗ₜ[k] y) y := by
    intro y
    have := hc 1 y
    simpa using this
  have hval : P.intValuation π₀ = WithZero.exp (-1 : ℤ) := by
    refine val_unif (k := k) (Y : Set B) hY χ P hP π₀ hπ₀P ?_
    intro y hyY
    obtain ⟨r₀, hr₀⟩ := hex (r y) (by
      simp only [E, U, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨y, hyY, rfl⟩)))
    obtain ⟨w₀, hw₀⟩ := hex (w y) (by
      simp only [E, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨y, hyY, rfl⟩)
    have hrU : r y ∈ U := by
      simp only [U, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨y, hyY, rfl⟩
    refine ⟨r₀, w₀, hnot (r y) hrU r₀ hr₀, ?_⟩
    have hι : Spz R φ (ι y ⊗ₜ[k] (1 : B)) (algebraMap k B (χ y)) := by
      have := hc (ρ y) 1
      rw [Algebra.algebraMap_eq_smul_one]
      exact this
    have hzs : Spz R φ (z y) (y - algebraMap k B (χ y)) := (har _ _ _ _ (hy y) hι).2.2
    have h1 := (har _ _ _ _ hr₀ hzs).2.1
    have h2 := (har _ _ _ _ hw₀ hπ₀).2.1
    rw [hrw y] at h1
    exact hu _ _ _ h1 h2
  have hpow : ∀ n : ℕ, Spz R φ (π ^ n) (π₀ ^ n) := by
    intro n
    induction n with
    | zero => simpa using hone
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (har _ _ _ _ ih hπ₀).2.1
  have key : ∀ (c x u : L ⊗[k] B) (c₀ : B) (n : ℕ), Spz R φ c c₀ → x ∈ U → u ∈ U →
      c * x = u * π ^ n → P.intValuation c₀ = WithZero.exp (-(n : ℤ)) := by
    intro c x u c₀ n hc₀ hxU huU hrel
    have hUE : ∀ v ∈ U, v ∈ E := fun v hv => by
      simp only [E, Finset.mem_union]
      exact Or.inl (Or.inl hv)
    obtain ⟨x₀, hx₀⟩ := hex x (hUE x hxU)
    obtain ⟨u₀, hu₀⟩ := hex u (hUE u huU)
    have h1 := (har _ _ _ _ hc₀ hx₀).2.1
    have h2 := (har _ _ _ _ hu₀ (hpow n)).2.1
    rw [hrel] at h1
    have h3 : c₀ * x₀ = u₀ * π₀ ^ n := hu _ _ _ h1 h2
    have hvx : P.intValuation x₀ = 1 :=
      (P.intValuation_eq_one_iff_mem_primeCompl x₀).mpr (hnot x hxU x₀ hx₀)
    have hvu : P.intValuation u₀ = 1 :=
      (P.intValuation_eq_one_iff_mem_primeCompl u₀).mpr (hnot u huU u₀ hu₀)
    have h4 := congrArg P.intValuation h3
    rw [map_mul, map_mul, map_pow, hvx, hvu, hval, mul_one, one_mul] at h4
    rw [h4, ← WithZero.exp_nsmul]
    simp
  have hmemU : s ∈ U ∧ t ∈ U ∧ s' ∈ U ∧ t' ∈ U := by simp [U]
  exact ⟨P, key a s t a₀ e ha₀ hmemU.1 hmemU.2.1 hst,
    key b s' t' b₀ e' hb₀ hmemU.2.2.1 hmemU.2.2.2 hst'⟩
