import Mathlib

open NumberField Matrix

namespace GlobalTheory.PrimAnnih

theorem exists_unit_coeff {W V ι : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [AddCommGroup V] [Module W V] [NoZeroSMulDivisors W V] [Fintype ι] (u : ι → V) (w : ι → W)
    (hw : w ≠ 0) (h : ∑ i, w i • u i = 0) :
    ∃ v : ι → W, (∃ i, IsUnit (v i)) ∧ ∑ i, v i • u i = 0 := by
  classical
  let I : Ideal W := Ideal.span (Set.range w)
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal I).principal
  have hdvd : ∀ i, c ∣ w i := fun i => by
    have : w i ∈ I := Ideal.subset_span ⟨i, rfl⟩
    rw [hc] at this
    exact Ideal.mem_span_singleton.1 this
  choose v hv using hdvd
  have hcI : c ∈ I := by rw [hc]; exact Submodule.mem_span_singleton_self c
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hcI
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hw; funext i; rw [hv i, zero_mul]; rfl
  have hsum : ∑ i, a i * v i = 1 := by
    apply mul_left_cancel₀ hc0
    rw [mul_one, Finset.mul_sum]
    conv_rhs => rw [← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hv i]; ring
  refine ⟨v, ?_, ?_⟩
  · by_contra hnu
    push_neg at hnu
    have h1 : (1 : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [← hsum]
      exact Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu i))
    exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · have h2 : c • ∑ i, v i • u i = 0 := by
      rw [Finset.smul_sum, ← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← hv i]
    exact (smul_eq_zero.1 h2).resolve_left hc0

theorem exists_vecMul_eq_zero {W Ω ι κ : Type} [CommRing W] [IsDomain W] [Field Ω] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (f : W →+* Ω) (hf : Function.Injective f)
    (A : Matrix ι κ W) (x : ι → Ω) (hx : x ≠ 0) (h : x ᵥ* A.map f = 0) :
    ∃ w : ι → W, w ≠ 0 ∧ w ᵥ* A = 0 := by
  classical
  by_contra H
  push_neg at H
  let L := FractionRing W
  let g : L →+* Ω := IsFractionRing.lift hf
  have hg : ∀ r, g (algebraMap W L r) = f r := fun r => IsFractionRing.lift_algebraMap hf r
  let AL : Matrix ι κ L := A.map (algebraMap W L)
  have hker : LinearMap.ker AL.vecMulLinear = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro l hl
    obtain ⟨⟨c, hc⟩, hint⟩ :=
      IsLocalization.exist_integer_multiples (nonZeroDivisors W) Finset.univ l
    choose w hw using fun i => RingHom.mem_rangeS.1 (hint i (Finset.mem_univ i))
    have hl' : l ᵥ* AL = 0 := hl
    have h1 : w ᵥ* A = 0 := by
      funext j
      apply IsFractionRing.injective W L
      rw [RingHom.map_vecMul, Pi.zero_apply, map_zero]
      have e : (algebraMap W L ∘ w) = fun i => algebraMap W L c * l i := by
        funext i; simpa [Algebra.smul_def] using hw i
      rw [e]
      have := congrFun hl' j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this ⊢
      simp only [mul_assoc, ← Finset.mul_sum, this, mul_zero, AL]
    have hw0 : w = 0 := by
      by_contra hw0; exact H w hw0 h1
    funext i
    have e1 := hw i
    rw [hw0, Pi.zero_apply, map_zero, Algebra.smul_def] at e1
    have hc0 : algebraMap W L c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
    exact (mul_eq_zero.1 e1.symm).resolve_left hc0
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective AL.vecMulLinear hker
  let P := LinearMap.toMatrix' G
  have hP : AL * P.transpose = 1 := by
    ext i j
    have := congrArg (fun φ => φ (Pi.single i 1) j) hG
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [← LinearMap.toMatrix'_mulVec G] at this
    rw [Matrix.mul_apply, Matrix.one_apply,
      show (if i = j then (1:L) else 0) = (Pi.single i (1:L) : ι → L) j by simp [Pi.single_apply, eq_comm], ← this]
    simp [Matrix.mulVec, dotProduct, P, mul_comm, Matrix.vecMulLinear_apply]
  have hAf : AL.map g = A.map f := by ext i j; simp [AL, hg]
  have hP' : A.map f * (P.transpose.map g) = 1 := by
    rw [← hAf, ← Matrix.map_mul, hP, Matrix.map_one _ (map_zero g) (map_one g)]
  apply hx
  rw [← Matrix.vecMul_one x, ← hP', ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]

end GlobalTheory.PrimAnnih

namespace GlobalTheory.PrimAnnih

theorem exists_extend (F Ω : Type) [Field F] [NumberField F] [Field Ω] [CharZero Ω]
    (σ : 𝓞 F →+* Ω) : ∃ σ' : F →ₐ[ℚ] Ω, ∀ a : 𝓞 F, σ' (algebraMap (𝓞 F) F a) = σ a := by
  have hk : RingHom.ker σ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [RingHom.comap_ker, show σ.comp (algebraMap ℤ (𝓞 F)) = Int.castRingHom Ω from
      RingHom.ext_int _ _]
    exact (RingHom.injective_iff_ker_eq_bot _).1 Int.cast_injective
  have hinj : Function.Injective σ := (RingHom.injective_iff_ker_eq_bot σ).2 hk
  exact ⟨(IsFractionRing.lift hinj : F →+* Ω).toRatAlgHom,
    fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem exists_primitive_annihilator : ∀ (F : Type) [Field F] [NumberField F] (W Ω : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (f : W →+* Ω), Function.Injective f → ∀ (n : ℕ) (M : 𝓞 F →+* Matrix (Fin n) (Fin n) W) (σ : 𝓞 F →+* Ω), (∀ c : Fin n → Ω, (∀ a, ((M a).map f).mulVec c = σ a • c) → c = 0) → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)), ∃ w : ι → W, (∃ i, IsUnit (w i)) ∧ ∑ i, w i • M (b i) = 0 := by
  intro F _ _ W Ω _ _ _ _ _ _ f hf n M σ hσ ι _ b
  classical
  let b' : Module.Basis ι ℚ F := Module.Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) F b
  have hb' : ∀ i, b' i = algebraMap (𝓞 F) F (b i) := fun i =>
    Module.Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) F b i
  obtain ⟨σ', hσ'⟩ := exists_extend F Ω σ
  have hcard : Fintype.card ι = Fintype.card (F →ₐ[ℚ] Ω) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis b']
  let q := Fintype.equivOfCardEq hcard
  let P := Algebra.embeddingsMatrixReindex ℚ Ω b' q
  have hPij : ∀ i j, P i j = q j (b' i) := fun i j => by
    simp [P, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  have hP : P.det ≠ 0 := by
    have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω b' q
    intro h0
    rw [h0, zero_pow two_ne_zero, map_eq_zero] at hd
    exact Algebra.discr_not_zero_of_basis ℚ b' hd
  have inj : ∀ z : ι → Ω, (∀ τ : F →ₐ[ℚ] Ω, ∑ i, z i * τ (b' i) = 0) → z = 0 := by
    intro z hz
    refine Matrix.eq_zero_of_vecMul_eq_zero hP (funext fun j => ?_)
    simpa [Matrix.vecMul, dotProduct, hPij] using hz (q j)
  let y : ι → Ω := fun j => if q j = σ' then 1 else 0
  let x : ι → Ω := y ᵥ* P⁻¹
  have hx : ∀ τ, ∑ i, x i * τ (b' i) = if τ = σ' then 1 else 0 := by
    intro τ
    have h1 : x ᵥ* P = y := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP),
        Matrix.vecMul_one]
    have := congrFun h1 (q.symm τ)
    simpa [Matrix.vecMul, dotProduct, hPij, y] using this

  let Φ : 𝓞 F →+* Matrix (Fin n) (Fin n) Ω := f.mapMatrix.comp M
  have hΦ : ∀ a, Φ a = (M a).map f := fun a => rfl
  have hcoef : ∀ (a : 𝓞 F) j, ∑ i, x i * (b.repr (a * b i) j : Ω) = σ a * x j := by
    intro a
    have hrep : ∀ i (τ : F →ₐ[ℚ] Ω), ∑ j, (b.repr (a * b i) j : Ω) * τ (b' j) =
        τ (algebraMap (𝓞 F) F a) * τ (b' i) := by
      intro i τ
      have e := congrArg (fun t : 𝓞 F => τ (algebraMap (𝓞 F) F t)) (b.sum_repr (a * b i))
      simp only [map_sum, map_zsmul, map_mul, zsmul_eq_mul] at e
      simpa [hb'] using e
    have := inj (fun j => ∑ i, x i * (b.repr (a * b i) j : Ω) - σ a * x j) (fun τ => by
      have key : ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j) =
          τ (algebraMap (𝓞 F) F a) * ∑ i, x i * τ (b' i) := by
        calc ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j)
            = ∑ j, ∑ i, x i * ((b.repr (a * b i) j : Ω) * τ (b' j)) := by
              simp only [Finset.sum_mul, mul_assoc]
          _ = ∑ i, x i * ∑ j, (b.repr (a * b i) j : Ω) * τ (b' j) := by
              rw [Finset.sum_comm]; simp only [Finset.mul_sum]
          _ = ∑ i, x i * (τ (algebraMap (𝓞 F) F a) * τ (b' i)) := by simp only [hrep]
          _ = τ (algebraMap (𝓞 F) F a) * ∑ i, x i * τ (b' i) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω) - σ a * x j) * τ (b' j) =
          ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j) -
            σ a * ∑ j, x j * τ (b' j) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      rw [e2, key, hx]
      split_ifs with hτ
      · subst hτ; rw [hσ']; ring
      · ring)
    intro j
    exact sub_eq_zero.1 (congrFun this j)
  let N : Matrix (Fin n) (Fin n) Ω := ∑ i, x i • Φ (b i)
  have hN : ∀ a, Φ a * N = σ a • N := by
    intro a
    calc Φ a * N = ∑ i, x i • Φ (a * b i) := by
          simp only [N, Finset.mul_sum, Matrix.mul_smul, map_mul]
      _ = ∑ i, x i • ∑ j, (b.repr (a * b i) j : Ω) • Φ (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← b.sum_repr (a * b i)]
          simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
      _ = ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) • Φ (b j) := by
          simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
      _ = ∑ j, (σ a * x j) • Φ (b j) := by simp only [hcoef]
      _ = σ a • N := by simp only [N, Finset.smul_sum, smul_smul]
  have hN0 : N = 0 := by
    ext j k
    have := hσ (fun j => N j k) (fun a => by
      funext r
      have e := congrFun (congrFun (hN a) r) k
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hΦ] using e)
    simpa using congrFun this j
  let A : Matrix ι (Fin n × Fin n) W := Matrix.of fun i p => M (b i) p.1 p.2
  have hx0 : x ≠ 0 := by
    intro h0
    have := hx σ'
    simp [h0] at this
  have hxA : x ᵥ* A.map f = 0 := by
    funext p
    have := congrFun (congrFun hN0 p.1) p.2
    simpa [Matrix.vecMul, dotProduct, A, N, hΦ, Matrix.sum_apply, mul_comm] using this
  obtain ⟨w, hw0, hwA⟩ := exists_vecMul_eq_zero f hf A x hx0 hxA
  haveI : NoZeroSMulDivisors W (Matrix (Fin n) (Fin n) W) :=
    inferInstanceAs (NoZeroSMulDivisors W (Fin n → Fin n → W))
  refine exists_unit_coeff (fun i => M (b i)) w hw0 ?_
  ext j k
  have := congrFun hwA (j, k)
  simpa [Matrix.vecMul, dotProduct, A, Matrix.sum_apply, mul_comm] using this

end GlobalTheory.PrimAnnih
