import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped TensorProduct

namespace GlobalTheory.HTFaith

lemma approx (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (w : M ⊗[ℤ] ℤ_[p]) :
    ∃ a : M, ∃ z : M ⊗[ℤ] ℤ_[p], w = a ⊗ₜ 1 + (p : ℤ) • z := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a s =>
    obtain ⟨t, ht⟩ : ∃ t : ℤ_[p], s - (PadicInt.appr s 1 : ℤ_[p]) = (p : ℤ_[p]) * t := by
      have := PadicInt.appr_spec 1 s
      rw [pow_one, Ideal.mem_span_singleton] at this
      obtain ⟨t, ht⟩ := this
      exact ⟨t, ht⟩
    refine ⟨(PadicInt.appr s 1 : ℤ) • a, a ⊗ₜ t, ?_⟩
    have hs : s = (PadicInt.appr s 1 : ℤ) • (1 : ℤ_[p]) + (p : ℤ) • t := by
      rw [zsmul_eq_mul, zsmul_eq_mul, _root_.mul_one]; push_cast; rw [← ht]; ring
    conv_lhs => rw [hs]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add w1 w2 h1 h2 =>
    obtain ⟨a1, z1, rfl⟩ := h1
    obtain ⟨a2, z2, rfl⟩ := h2
    exact ⟨a1 + a2, z1 + z2, by rw [TensorProduct.add_tmul, smul_add]; abel⟩

lemma kernel (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] [Module.Free ℤ M] (x : M)
    (z : M ⊗[ℤ] ℤ_[p]) (h : x ⊗ₜ 1 = (p : ℤ) • z) : ∃ u : M, x = (p : ℤ) • u := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  have hd : ∀ i, (p : ℤ) ∣ b.repr x i := by
    intro i
    let f : M ⊗[ℤ] ℤ_[p] →ₗ[ℤ] ℤ_[p] :=
      (TensorProduct.lid ℤ ℤ_[p]).toLinearMap ∘ₗ TensorProduct.map (b.coord i) LinearMap.id
    have h1 : f (x ⊗ₜ 1) = f ((p : ℤ) • z) := by rw [h]
    have h0 : f (x ⊗ₜ 1) = ((b.repr x i : ℤ) : ℤ_[p]) := by
      show (TensorProduct.lid ℤ ℤ_[p]) (TensorProduct.map (b.coord i) LinearMap.id (x ⊗ₜ[ℤ] (1 : ℤ_[p]))) = _
      rw [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, Module.Basis.coord_apply,
        zsmul_eq_mul, _root_.mul_one]
    rw [map_zsmul, h0, zsmul_eq_mul] at h1
    have h3 : ‖((b.repr x i : ℤ) : ℤ_[p])‖ < 1 := by
      rw [h1]; push_cast
      rw [norm_mul, PadicInt.norm_p]
      have := PadicInt.norm_le_one (f z)
      have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      calc (p:ℝ)⁻¹ * ‖f z‖ ≤ (p:ℝ)⁻¹ * 1 := by gcongr
        _ < 1 := by rw [_root_.mul_one]; exact inv_lt_one_of_one_lt₀ hp
    exact (PadicInt.norm_int_lt_one_iff_dvd _).1 h3
  choose c hc using hd
  refine ⟨∑ i ∈ (b.repr x).support, c i • b i, ?_⟩
  conv_lhs => rw [← b.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, smul_smul]

lemma saturate (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (x : M) (hx : x ≠ 0) :
    ∃ k : ℕ, ∃ x' : M, x = ((p : ℤ) ^ k) • x' ∧ ¬ ∃ u : M, x' = (p : ℤ) • u := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  let N : M → ℕ := fun x => ∑ i, (b.repr x i).natAbs
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hNpos : ∀ u : M, u ≠ 0 → 0 < N u := by
    intro u hu
    by_contra h
    push_neg at h
    apply hu
    have h0 : ∀ i, b.repr u i = 0 := fun i =>
      Int.natAbs_eq_zero.1 (Nat.eq_zero_of_le_zero ((Finset.single_le_sum (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)).trans h))
    exact b.repr.injective (by ext i; simp [h0 i])
  have hNs : ∀ u : M, N ((p : ℤ) • u) = p * N u := by
    intro u
    simp only [N, map_zsmul, Finsupp.smul_apply, smul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast,
      Finset.mul_sum]
  induction hN : N x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  by_cases h : ∃ u, x = (p : ℤ) • u
  · obtain ⟨u, rfl⟩ := h
    have hu : u ≠ 0 := by rintro rfl; simp at hx
    have hlt : N u < n := by
      rw [← hN, hNs]
      have := hNpos u hu
      nlinarith
    obtain ⟨k, x', hk, h'⟩ := ih _ hlt u hu rfl
    exact ⟨k + 1, x', by rw [hk, smul_smul, pow_succ'], h'⟩
  · exact ⟨0, x, by simp, h⟩

lemma integral (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (c : 𝓞 D.F)
    (h : ∀ y : D.La, ∃ z : D.La, algebraMap (𝓞 D.F) D.O c • y = (p : ℤ) • z) :
    ∃ c' : 𝓞 D.F, c = (p : ℤ) • c' := by
  classical
  haveI := D.freeLa; haveI := D.finLa
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hfaith : ∀ q : 𝓞 D.F, (∀ y : D.La, algebraMap (𝓞 D.F) D.O q • y = 0) → q = 0 := by
    intro q hq
    by_contra hq0
    have hI : Ideal.span {q} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hq0
    have hne : Ideal.absNorm (Ideal.span {q}) ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {q}))
    haveI : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := ℤ) (by
      rw [D.rankLa]
      have := D.m_pos; have := D.n_pos
      have := Module.finrank_pos (R := ℚ) (M := D.F)
      positivity)
    obtain ⟨y, hy⟩ := exists_ne (0 : D.La)
    apply hy
    have h1 : algebraMap (𝓞 D.F) D.O (r * q) • y = 0 := by rw [map_mul, mul_smul, hq, smul_zero]
    rw [hr, map_natCast, Nat.cast_smul_eq_nsmul] at h1
    have h2 : ((Ideal.absNorm (Ideal.span {q}) : ℕ) : ℤ) • y = 0 := by rw [natCast_zsmul]; exact h1
    exact (smul_eq_zero.1 h2).resolve_left (by exact_mod_cast hne)
  choose z hz using h
  have hadd : ∀ y1 y2, z (y1 + y2) = z y1 + z y2 := by
    intro y1 y2
    apply smul_right_injective D.La hp0
    show (p : ℤ) • z (y1 + y2) = (p : ℤ) • (z y1 + z y2)
    rw [← hz, smul_add, smul_add, ← hz, ← hz]
  let g : D.La →ₗ[ℤ] D.La := (AddMonoidHom.mk' z hadd).toIntLinearMap
  have hg : ∀ y, g y = z y := fun y => rfl
  obtain ⟨P, hPm, hP⟩ := LinearMap.isIntegral g
  let ψ : 𝓞 D.F →+* Module.End ℤ D.La :=
    (Module.toModuleEnd ℤ (S := D.O) D.La).comp (algebraMap (𝓞 D.F) D.O)
  have hψ : ∀ q y, ψ q y = algebraMap (𝓞 D.F) D.O q • y := fun q y => rfl
  have hψc : ψ c = (p : ℤ) • g := by
    ext y; rw [hψ, hz, LinearMap.smul_apply, hg]
  set d := P.natDegree
  have hQ : Polynomial.aeval (ψ c) (P.scaleRoots (p : ℤ)) = 0 := by
    rw [hψc, Polynomial.aeval_eq_sum_range, Polynomial.natDegree_scaleRoots]
    have h1 : ∀ i ∈ Finset.range (d + 1), (P.scaleRoots (p : ℤ)).coeff i • ((p : ℤ) • g) ^ i
        = (p : ℤ) ^ d • (P.coeff i • g ^ i) := by
      intro i hi
      rw [Polynomial.coeff_scaleRoots, smul_pow, smul_smul, smul_smul]
      congr 1
      rw [_root_.mul_assoc, pow_sub_mul_pow _ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)), _root_.mul_comm]
    rw [Finset.sum_congr rfl h1, ← Finset.smul_sum, ← Polynomial.aeval_eq_sum_range, Polynomial.aeval_def, hP, smul_zero]
  have hQ0 : Polynomial.aeval c (P.scaleRoots (p : ℤ)) = 0 := by
    apply hfaith
    have h2 : ψ (Polynomial.aeval c (P.scaleRoots (p : ℤ))) = Polynomial.aeval (ψ c) (P.scaleRoots (p : ℤ)) :=
      (Polynomial.aeval_algHom_apply ψ.toIntAlgHom c _).symm
    intro y
    rw [← hψ, h2, hQ, LinearMap.zero_apply]
  have hQF : Polynomial.aeval (c : D.F) (P.scaleRoots (p : ℤ)) = 0 := by
    have h3 := congrArg (algebraMap (𝓞 D.F) D.F) hQ0
    rwa [← Polynomial.aeval_algebraMap_apply, map_zero] at h3
  set gam : D.F := (c : D.F) / (p : D.F)
  have hpF : (p : D.F) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hgam : Polynomial.aeval gam P = 0 := by
    have h4 := Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap ℤ D.F) gam (p : ℤ)
    have h5 : algebraMap ℤ D.F (p : ℤ) * gam = (c : D.F) := by
      simp only [gam, map_natCast, eq_intCast, Int.cast_natCast]; field_simp
    rw [h5, ← Polynomial.aeval_def, hQF, ← Polynomial.aeval_def] at h4
    have h6 : algebraMap ℤ D.F (p : ℤ) ^ P.natDegree ≠ 0 := by
      apply pow_ne_zero; simpa using hpF
    exact (mul_eq_zero.1 h4.symm).resolve_left h6
  have hint : IsIntegral ℤ gam := ⟨P, hPm, by rw [← Polynomial.aeval_def]; exact hgam⟩
  refine ⟨⟨gam, (mem_integralClosure_iff ℤ D.F).2 hint⟩, ?_⟩
  apply RingOfIntegers.ext
  change (c : D.F) = (p : ℤ) • gam
  rw [zsmul_eq_mul, Int.cast_natCast]
  simp only [gam]
  field_simp

end GlobalTheory.HTFaith

theorem GlobalTheory.HTFaith.faithful : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O), (∀ y : D.La, x • y = 0) → x = 0 := by
  intro p _ D x hx
  classical
  haveI := D.freeO; haveI := D.finO; haveI := D.freeLa; haveI := D.finLa
  by_contra hne
  obtain ⟨k, x', rfl, hx'⟩ := GlobalTheory.HTFaith.saturate p D.O x hne
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx'0 : ∀ y : D.La, x' • y = 0 := by
    intro y
    have := hx y
    rw [smul_assoc] at this
    exact (smul_eq_zero.1 this).resolve_left (pow_ne_zero _ hp0)
  obtain ⟨φ⟩ := D.splitP
  let J : Ideal (𝓞 D.F ⊗[ℤ] ℤ_[p]) := Ideal.span {((p : ℤ) : 𝓞 D.F ⊗[ℤ] ℤ_[p])}
  let π : (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* (𝓞 D.F ⊗[ℤ] ℤ_[p]) ⧸ J := Ideal.Quotient.mk J
  have hπ : ∀ r, π ((p : ℤ) • r) = 0 := by
    intro r
    rw [zsmul_eq_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  let Φ : D.O →+* Matrix (Fin D.m) (Fin D.m) ((𝓞 D.F ⊗[ℤ] ℤ_[p]) ⧸ J) :=
    π.mapMatrix.comp (φ.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom)
  have hΦ : ∀ a, Φ a = (φ (a ⊗ₜ 1)).map π := fun a => rfl
  have hker : ∀ a : D.O, Φ a = 0 → ∃ u, a = (p : ℤ) • u := by
    intro a ha
    have hr : ∀ i j, ∃ r, φ (a ⊗ₜ 1) i j = (p : ℤ) • r := by
      intro i j
      have h1 := congrFun (congrFun ha i) j
      rw [hΦ, Matrix.map_apply, Matrix.zero_apply] at h1
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
      exact ⟨r, by rw [← hr, zsmul_eq_mul, mul_comm]⟩
    choose r hr using hr
    apply GlobalTheory.HTFaith.kernel p D.O a (φ.symm (Matrix.of r))
    rw [← map_zsmul φ.symm, ← φ.symm_apply_apply (a ⊗ₜ 1)]
    congr 1
    ext i j
    rw [hr, Matrix.smul_apply, Matrix.of_apply]
  have hsurj : ∀ A : Matrix (Fin D.m) (Fin D.m) ((𝓞 D.F ⊗[ℤ] ℤ_[p]) ⧸ J), ∃ a, Φ a = A := by
    intro A
    choose B hB using fun i j => Ideal.Quotient.mk_surjective (I := J) (A i j)
    obtain ⟨a, z, hz⟩ := GlobalTheory.HTFaith.approx p D.O (φ.symm (Matrix.of B))
    refine ⟨a, ?_⟩
    have h1 : φ (a ⊗ₜ 1) = Matrix.of B - (p : ℤ) • φ z := by
      rw [← map_zsmul, ← φ.apply_symm_apply (Matrix.of B), hz, map_add]; abel
    ext i j
    rw [hΦ, h1, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, map_sub, hπ, sub_zero, Matrix.of_apply]
    exact hB i j
  have hsurjF : ∀ r : (𝓞 D.F ⊗[ℤ] ℤ_[p]) ⧸ J, ∃ c : 𝓞 D.F, π (c ⊗ₜ 1) = r := by
    intro r
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨c, z, hz⟩ := GlobalTheory.HTFaith.approx p (𝓞 D.F) s
    exact ⟨c, by rw [hz, map_add, hπ, add_zero]⟩
  have hscal : ∀ c : 𝓞 D.F, Φ (algebraMap _ _ c) = Matrix.scalar _ (π (c ⊗ₜ 1)) := by
    intro c
    rw [hΦ]
    have h1 : φ (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1) = Matrix.scalar _ (c ⊗ₜ (1 : ℤ_[p])) := φ.commutes c
    rw [h1]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]
  have hne' : Φ x' ≠ 0 := fun h => hx' (hker x' h)
  obtain ⟨i, j, hij⟩ : ∃ i j, Φ x' i j ≠ 0 := by
    by_contra h; push_neg at h; exact hne' (Matrix.ext h)
  choose E hE using fun k l => hsurj (Matrix.single k l 1)
  let y := ∑ k, E k i * x' * E j k
  have hy : Φ y = Matrix.scalar _ (Φ x' i j) := by
    simp only [y, map_sum, map_mul, hE, Matrix.single_mul_mul_single, _root_.one_mul, _root_.mul_one]
    ext a b
    rw [Matrix.sum_apply]
    by_cases hab : a = b
    · subst hab
      rw [Finset.sum_eq_single a (fun k _ hk => by simp [Matrix.single_apply, hk]) (by simp)]
      simp [Matrix.single_apply]
    · rw [Finset.sum_eq_zero (fun k _ => by simp [Matrix.single_apply]; intro h1 h2; exact absurd (h1.symm.trans h2) hab)]
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, hab]
  obtain ⟨c, hc⟩ := hsurjF (Φ x' i j)
  have h0 : Φ (y - algebraMap _ _ c) = 0 := by rw [map_sub, hy, hscal, hc, sub_self]
  obtain ⟨u, hu⟩ := hker _ h0
  have hyk : ∀ v : D.La, y • v = 0 := by
    intro v
    simp only [y, Finset.sum_smul, mul_smul, hx'0, smul_zero, Finset.sum_const_zero]
  have hc' : ∀ v : D.La, ∃ w, algebraMap (𝓞 D.F) D.O c • v = (p : ℤ) • w := by
    intro v
    refine ⟨-(u • v), ?_⟩
    have : algebraMap (𝓞 D.F) D.O c = y - (p : ℤ) • u := by rw [← hu]; abel
    rw [this, sub_smul, hyk, smul_assoc, zero_sub, smul_neg]
  obtain ⟨c', rfl⟩ := GlobalTheory.HTFaith.integral p D c hc'
  apply hij
  rw [← hc, ← TensorProduct.smul_tmul', hπ]
