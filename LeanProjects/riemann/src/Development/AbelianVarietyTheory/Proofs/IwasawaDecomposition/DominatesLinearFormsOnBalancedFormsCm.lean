import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq

noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan Matrix Polynomial
namespace GlobalTheory.DomBal

private theorem exists_nat_mul_rat_eq_int_iwasawa_decomposition {J : Type} [Fintype J] (q : J → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ z : J → ℤ, ∀ j, (N : ℚ) * q j = z j := by
  classical
  refine ⟨∏ i, (q i).den, Finset.prod_pos (fun i _ => (q i).den_pos),
    fun j => (q j).num * (((∏ i, (q i).den) / (q j).den : ℕ) : ℤ), fun j => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ j)
  beta_reduce
  rw [hm, Nat.mul_div_cancel_left m (q j).den_pos]
  have h := Rat.mul_den_eq_num (q j)
  push_cast
  linear_combination (m : ℚ) * h

private theorem star_dotProduct_mulVec_eq_sum {R : Type} [CommRing R] [StarRing R] [TrivialStar R] {J : Type} [Fintype J]
    (A : Matrix J J R) (x : J → R) : star x ⬝ᵥ (A *ᵥ x) = ∑ j, ∑ k, x j * x k * A j k := by
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

private theorem star_dotProduct_add_transpose_mulVec_eq_two_mul_sum {R : Type} [CommRing R] [StarRing R] [TrivialStar R] {J : Type} [Fintype J]
    (A : Matrix J J R) (x : J → R) : star x ⬝ᵥ ((A + Aᵀ) *ᵥ x) = 2 * ∑ j, ∑ k, x j * x k * A j k := by
  rw [star_dotProduct_mulVec_eq_sum]
  simp only [Matrix.add_apply, Matrix.transpose_apply, mul_add, Finset.sum_add_distrib, two_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem quad_nonneg_real {J : Type} [Fintype J] (P : Matrix J J ℤ)
    (hP : ∀ z : J → ℤ, 0 ≤ ∑ j, ∑ k, z j * z k * P j k) (s : J → ℝ) :
    0 ≤ ∑ j, ∑ k, s j * s k * (P j k : ℝ) := by
  have hrat : ∀ q : J → ℚ, 0 ≤ ∑ j, ∑ k, (q j : ℝ) * (q k : ℝ) * (P j k : ℝ) := by
    intro q
    obtain ⟨N, hN, z, hz⟩ := exists_nat_mul_rat_eq_int_iwasawa_decomposition q
    have hzR : ∀ j, (N : ℝ) * (q j : ℝ) = (z j : ℝ) := fun j => by exact_mod_cast hz j
    have key : (N : ℝ) ^ 2 * ∑ j, ∑ k, (q j : ℝ) * (q k : ℝ) * (P j k : ℝ) =
        ∑ j, ∑ k, (z j : ℝ) * (z k : ℝ) * (P j k : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hzR j, ← hzR k]; ring
    have hz0 : (0 : ℝ) ≤ ∑ j, ∑ k, (z j : ℝ) * (z k : ℝ) * (P j k : ℝ) := by exact_mod_cast hP z
    have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    rw [← key] at hz0
    exact (mul_nonneg_iff_of_pos_left hNpos).mp hz0
  have hd : DenseRange (fun q : J → ℚ => fun j => (q j : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hc : IsClosed {s : J → ℝ | 0 ≤ ∑ j, ∑ k, s j * s k * (P j k : ℝ)} :=
    isClosed_le continuous_const (by fun_prop)
  exact isClosed_property hd hc hrat s

theorem quad_pos_real {J : Type} [Fintype J] (P : Matrix J J ℤ)
    (hP : ∀ z : J → ℤ, z ≠ 0 → 0 < ∑ j, ∑ k, z j * z k * P j k) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : J → ℝ, c * ‖s‖ ^ 2 ≤ ∑ j, ∑ k, s j * s k * (P j k : ℝ) := by
  classical
  set Q : (J → ℝ) → ℝ := fun s => ∑ j, ∑ k, s j * s k * (P j k : ℝ) with hQ
  have hcont : Continuous Q := by fun_prop
  have hnn : ∀ s, 0 ≤ Q s := quad_nonneg_real P (fun z => by
    by_cases hz : z = 0
    · subst hz; simp
    · exact (hP z hz).le)
  have hpos : ∀ s : J → ℝ, s ≠ 0 → 0 < Q s := by
    intro s hs
    rcases (hnn s).lt_or_eq with h | h
    · exact h
    exfalso
    set PR : Matrix J J ℝ := P.map (Int.cast : ℤ → ℝ) with hPR
    have hdot : ∀ x : J → ℝ, star x ⬝ᵥ ((PR + PRᵀ) *ᵥ x) = 2 * Q x := fun x => by
      rw [star_dotProduct_add_transpose_mulVec_eq_two_mul_sum]
      simp [hQ, hPR]
    have hpsd : (PR + PRᵀ).PosSemidef := by
      refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
      · ext i j
        simp [Matrix.conjTranspose_apply, add_comm]
      · rw [hdot]; exact mul_nonneg zero_le_two (hnn x)
    have h0 : (PR + PRᵀ) *ᵥ s = 0 := by
      rw [← Matrix.PosSemidef.dotProduct_mulVec_zero_iff hpsd, hdot, ← h, mul_zero]
    have hdetR : (PR + PRᵀ).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨s, hs, h0⟩
    have hmap : PR + PRᵀ = (Int.castRingHom ℝ).mapMatrix (P + Pᵀ) := by
      ext i j; simp [hPR]
    have hdetZ : (P + Pᵀ).det = 0 := by
      have := (Int.castRingHom ℝ).map_det (P + Pᵀ)
      rw [← hmap, hdetR] at this
      simpa using this
    obtain ⟨z, hz, hSz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetZ
    have h2 := star_dotProduct_add_transpose_mulVec_eq_two_mul_sum P z
    rw [hSz, dotProduct_zero] at h2
    have := hP z hz
    omega
  obtain hE | hne := (Metric.sphere (0 : J → ℝ) 1).eq_empty_or_nonempty
  · refine ⟨1, one_pos, fun s => ?_⟩
    by_cases hs : s = 0
    · subst hs; simp
    · exfalso
      have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs
      have hmem : ‖s‖⁻¹ • s ∈ Metric.sphere (0 : J → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      rw [hE] at hmem; exact hmem
  · obtain ⟨s0, hs0, hmin⟩ := (isCompact_sphere (0 : J → ℝ) 1).exists_isMinOn hne hcont.continuousOn
    have hs0ne : s0 ≠ 0 := by
      rintro rfl; simp at hs0
    refine ⟨Q s0, hpos s0 hs0ne, fun s => ?_⟩
    by_cases hs : s = 0
    · subst hs; simp [hQ]
    · have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs
      have hmem : ‖s‖⁻¹ • s ∈ Metric.sphere (0 : J → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 : Q s0 ≤ Q (‖s‖⁻¹ • s) := hmin hmem
      have hscale : Q (‖s‖⁻¹ • s) = (‖s‖⁻¹) ^ 2 * Q s := by
        simp only [hQ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      rw [hscale] at h1
      calc Q s0 * ‖s‖ ^ 2 ≤ (‖s‖⁻¹) ^ 2 * Q s * ‖s‖ ^ 2 := by gcongr
        _ = Q s := by field_simp

theorem exists_poly_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    ∃ p : ℝ[X], aeval A p * aeval A p = A := by
  classical
  have hsa : IsSelfAdjoint A := hA.1
  have hspec : spectrum ℝ A = Set.range hA.1.eigenvalues := hA.1.spectrum_real_eq_range_eigenvalues
  have hfin : (spectrum ℝ A).Finite := hspec ▸ Set.finite_range _
  have hnn : ∀ x ∈ spectrum ℝ A, 0 ≤ x := by
    intro x hx; rw [hspec] at hx; obtain ⟨i, rfl⟩ := hx; exact hA.eigenvalues_nonneg i
  let p : ℝ[X] := Lagrange.interpolate hfin.toFinset id (fun x => Real.sqrt x)
  have hp : ∀ x ∈ spectrum ℝ A, p.eval x = Real.sqrt x := by
    intro x hx
    exact Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) (hfin.mem_toFinset.mpr hx)
  refine ⟨p, ?_⟩
  rw [← cfc_polynomial p A hsa, ← cfc_mul (fun x => p.eval x) (fun x => p.eval x) A]
  rw [cfc_congr (g := id) (fun x hx => by simp only [id]; rw [hp x hx]; exact Real.mul_self_sqrt (hnn x hx))]
  exact cfc_id ℝ A hsa

theorem mul_aeval_of_mul_eq {n : ℕ} {A T T' : Matrix (Fin n) (Fin n) ℝ} (h : A * T = T' * A) (p : ℝ[X]) :
    A * aeval T p = aeval T' p * A := by
  have hpow : ∀ k : ℕ, A * T ^ k = T' ^ k * A := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc]
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, hpow, smul_mul_assoc]

theorem transpose_aeval {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (p : ℝ[X]) : (aeval T p)ᵀ = aeval Tᵀ p := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_smul, Matrix.transpose_pow]

theorem exists_poly_sqrt {n : ℕ} (G B : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (hB : B.PosSemidef) :
    ∃ p : ℝ[X], (aeval (G⁻¹ * B) p)ᵀ * G * aeval (G⁻¹ * B) p = B := by
  classical
  have hGu : IsUnit G.det := (hG.det_pos).ne'.isUnit
  have hGt : Gᵀ = G := by
    have := hG.1; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hBt : Bᵀ = B := by
    have := hB.1; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  obtain ⟨q, hq⟩ := exists_poly_sq G hG.posSemidef
  set R := aeval G q with hRdef
  have hRt : Rᵀ = R := by rw [hRdef, transpose_aeval, hGt]
  have hRu : IsUnit R.det := by
    have h : R.det * R.det = G.det := by rw [← Matrix.det_mul, hq]
    rw [← h] at hGu
    exact isUnit_of_mul_isUnit_left hGu
  have hRinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
  have hRinv' : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
  set C := R⁻¹ * B * R⁻¹ with hCdef
  have hC : C.PosSemidef := by
    have h := hB.conjTranspose_mul_mul_same R⁻¹
    have hRi : (R⁻¹)ᴴ = R⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_eq_transpose_of_trivial, hRt]
    rwa [hRi] at h
  obtain ⟨p, hp⟩ := exists_poly_sq C hC
  set N := G⁻¹ * B with hNdef
  have hGinv : G⁻¹ = R⁻¹ * R⁻¹ := by rw [← hq, Matrix.mul_inv_rev]
  have hRN : R * N = C * R := by
    calc R * N = (R * R⁻¹) * R⁻¹ * B := by simp only [hNdef, hGinv, Matrix.mul_assoc]
      _ = R⁻¹ * B := by rw [hRinv, Matrix.one_mul]
      _ = R⁻¹ * B * (R⁻¹ * R) := by rw [hRinv', Matrix.mul_one]
      _ = C * R := by simp only [hCdef, Matrix.mul_assoc]
  have h1 := mul_aeval_of_mul_eq hRN p
  have hPM : aeval N p * aeval N p = N := by
    have e : R * (aeval N p * aeval N p) = R * N := by
      calc R * (aeval N p * aeval N p) = (R * aeval N p) * aeval N p := (Matrix.mul_assoc _ _ _).symm
        _ = (aeval C p * R) * aeval N p := by rw [h1]
        _ = aeval C p * (R * aeval N p) := Matrix.mul_assoc _ _ _
        _ = aeval C p * (aeval C p * R) := by rw [h1]
        _ = (aeval C p * aeval C p) * R := (Matrix.mul_assoc _ _ _).symm
        _ = C * R := by rw [hp]
        _ = R * N := hRN.symm
    calc aeval N p * aeval N p = (R⁻¹ * R) * (aeval N p * aeval N p) := by rw [hRinv', Matrix.one_mul]
      _ = R⁻¹ * (R * (aeval N p * aeval N p)) := Matrix.mul_assoc _ _ _
      _ = R⁻¹ * (R * N) := by rw [e]
      _ = N := by rw [← Matrix.mul_assoc, hRinv', Matrix.one_mul]
  have e1 : G * N = B := by
    rw [hNdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hGu, Matrix.one_mul]
  have e2 : Nᵀ * G = B := by
    rw [hNdef, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hGt, hBt, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul G hGu, Matrix.mul_one]
  have h2 := mul_aeval_of_mul_eq (e1.trans e2.symm) p
  refine ⟨p, ?_⟩
  rw [transpose_aeval, ← h2, Matrix.mul_assoc, hPM, e1]

theorem exists_real_ext {n : ℕ} (L : Matrix (Fin n) (Fin n) ℤ →ₗ[ℤ] ℤ) :
    ∃ Λ : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ, ∀ Y : Matrix (Fin n) (Fin n) ℤ, Λ (Y.map (Int.cast : ℤ → ℝ)) = (L Y : ℝ) := by
  classical
  have hsingle : ∀ (i j : Fin n) (c : ℤ), L (Matrix.single i j c) = c * L (Matrix.single i j 1) := by
    intro i j c
    rw [← smul_eq_mul, ← L.map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  refine ⟨{ toFun := fun X => ∑ i, ∑ j, X i j * (L (Matrix.single i j 1) : ℝ),
            map_add' := fun X Y => by simp [add_mul, Finset.sum_add_distrib],
            map_smul' := fun c X => by simp [Finset.mul_sum, mul_assoc] }, fun Y => ?_⟩
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply]
  conv_rhs => rw [Matrix.matrix_eq_sum_single Y]
  rw [map_sum]; push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]; push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsingle i j (Y i j)]; push_cast; ring

theorem main_matrix {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hGs : Gᵀ = G)
    (hG : ∀ z : Fin n → ℤ, z ≠ 0 → 0 < ∑ j, ∑ k, z j * z k * G j k)
    (𝓡 : Subalgebra ℤ (Matrix (Fin n) (Fin n) ℤ)) (L M : Matrix (Fin n) (Fin n) ℤ →ₗ[ℤ] ℤ)
    (hL : ∀ A ∈ 𝓡, A ≠ 0 → 0 < L (Aᵀ * G * A)) :
    ∃ C : ℕ, ∀ B : Matrix (Fin n) (Fin n) ℤ, Bᵀ = B → (∀ z : Fin n → ℤ, 0 ≤ ∑ j, ∑ k, z j * z k * B j k) →
      G.adjugate * B ∈ 𝓡 → M B ≤ C * L B := by
  classical
  obtain ⟨r, b⟩ := Submodule.basisOfPid (Module.Free.chooseBasis ℤ (Matrix (Fin n) (Fin n) ℤ))
    (Subalgebra.toSubmodule 𝓡)
  let e : Fin r → Matrix (Fin n) (Fin n) ℤ := fun i => (b i : Matrix (Fin n) (Fin n) ℤ)
  have he : ∀ i, e i ∈ 𝓡 := fun i => (b i).2
  let cR : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℝ := (Int.castRingHom ℝ).mapMatrix
  have hcR : ∀ Y, cR Y = Y.map (Int.cast : ℤ → ℝ) := fun Y => rfl
  let Pm : Matrix (Fin r) (Fin r) ℤ := fun i j => L ((e i)ᵀ * G * e j)
  let Qm : Matrix (Fin r) (Fin r) ℤ := fun i j => M ((e i)ᵀ * G * e j)
  have hexp : ∀ (z : Fin r → ℤ), (∑ i, z i • e i)ᵀ * G * (∑ i, z i • e i) =
      ∑ i, ∑ j, (z i * z j) • ((e i)ᵀ * G * e j) := by
    intro z
    rw [Matrix.transpose_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hPpos : ∀ z : Fin r → ℤ, z ≠ 0 → 0 < ∑ i, ∑ j, z i * z j * Pm i j := by
    intro z hz
    have hY : ∑ i, z i • e i ∈ 𝓡 := Subalgebra.sum_mem _ fun i _ => Subalgebra.zsmul_mem _ (he i) _
    have hY0 : ∑ i, z i • e i ≠ 0 := by
      intro h0
      apply hz
      funext i
      have h' : ∑ i, z i • b i = 0 := by
        apply Subtype.ext
        simpa [e] using h0
      exact Fintype.linearIndependent_iff.mp b.linearIndependent z h' i
    have := hL _ hY hY0
    rw [hexp] at this
    refine lt_of_lt_of_eq this ?_
    simp only [map_sum, map_zsmul, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by simp only [Pm]
  obtain ⟨c, hc0, hc⟩ := quad_pos_real Pm hPpos
  obtain ⟨Λ, hΛ⟩ := exists_real_ext L
  obtain ⟨Μ, hΜ⟩ := exists_real_ext M
  set K : ℝ := ∑ i, ∑ j, |(Qm i j : ℝ)| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨⌈K / c⌉₊, fun B hBs hBnn hBR => ?_⟩
  have hGR : (cR G).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
    · ext i j
      have := congrFun (congrFun hGs i) j
      simpa [cR, Matrix.conjTranspose_apply] using this
    · rw [star_dotProduct_mulVec_eq_sum]
      obtain ⟨c', hc', hG'⟩ := quad_pos_real G hG
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      calc (0 : ℝ) < c' * ‖x‖ ^ 2 := by positivity
        _ ≤ _ := hG' x
        _ = _ := by simp [cR]
  have hBR' : (cR B).PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
    · ext i j
      have := congrFun (congrFun hBs i) j
      simpa [cR, Matrix.conjTranspose_apply] using this
    · rw [star_dotProduct_mulVec_eq_sum]
      have := quad_nonneg_real B hBnn x
      simpa [cR] using this
  obtain ⟨p, hp⟩ := exists_poly_sqrt (cR G) (cR B) hGR hBR'
  set Esp := Submodule.span ℝ (Set.range fun i => cR (e i))
  have hcR𝓡 : ∀ Y ∈ 𝓡, cR Y ∈ Esp := by
    intro Y hY
    have hrepr := b.sum_repr ⟨Y, hY⟩
    have hY' : Y = ∑ i, b.repr ⟨Y, hY⟩ i • e i := by
      have h := congrArg Subtype.val hrepr
      rw [Submodule.coe_sum] at h
      simp only [Submodule.coe_smul] at h
      exact h.symm
    rw [hY', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : cR (b.repr ⟨Y, hY⟩ i • e i) = ((b.repr ⟨Y, hY⟩ i : ℤ) : ℝ) • cR (e i) := by
      rw [map_zsmul, Int.cast_smul_eq_zsmul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdet : (cR G).det = (G.det : ℝ) := by
    have := (Int.castRingHom ℝ).map_det G
    simpa [cR] using this.symm
  have hadj : (cR G).adjugate = cR G.adjugate := (RingHom.map_adjugate (Int.castRingHom ℝ) G).symm
  have hinv : (cR G)⁻¹ * cR B = ((G.det : ℝ))⁻¹ • cR (G.adjugate * B) := by
    rw [Matrix.inv_def, hdet, hadj, map_mul, Matrix.smul_mul, Ring.inverse_eq_inv']
  have hA : aeval ((cR G)⁻¹ * cR B) p ∈ Esp := by
    rw [hinv, aeval_eq_sum_range]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [_root_.smul_pow, ← map_pow]
    exact Submodule.smul_mem _ _ (hcR𝓡 _ (Subalgebra.pow_mem _ hBR k))
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hA
  have hT : ∀ i j, cR ((e i)ᵀ * G * e j) = (cR (e i))ᵀ * cR G * cR (e j) := by
    intro i j
    rw [map_mul, map_mul]
    congr 2
  have hBexp : cR B = ∑ i, ∑ j, (s i * s j) • cR ((e i)ᵀ * G * e j) := by
    rw [← hp, ← hs, Matrix.transpose_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT, Matrix.transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hLB : (L B : ℝ) = ∑ i, ∑ j, s i * s j * (Pm i j : ℝ) := by
    rw [← hΛ B, ← hcR, hBexp]
    simp only [map_sum, map_smul, smul_eq_mul, hcR, hΛ, Pm]
  have hMB : (M B : ℝ) = ∑ i, ∑ j, s i * s j * (Qm i j : ℝ) := by
    rw [← hΜ B, ← hcR, hBexp]
    simp only [map_sum, map_smul, smul_eq_mul, hcR, hΜ, Qm]
  have hs_le : ∀ i, |s i| ≤ ‖s‖ := fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm s i
  have hbound : (M B : ℝ) ≤ ‖s‖ ^ 2 * K := by
    rw [hMB, hK, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc s i * s j * (Qm i j : ℝ) ≤ |s i * s j * (Qm i j : ℝ)| := le_abs_self _
      _ = |s i| * |s j| * |(Qm i j : ℝ)| := by rw [abs_mul, abs_mul]
      _ ≤ ‖s‖ * ‖s‖ * |(Qm i j : ℝ)| := by
          gcongr
          · exact hs_le i
          · exact hs_le j
      _ = ‖s‖ ^ 2 * |(Qm i j : ℝ)| := by ring
  have hLc : c * ‖s‖ ^ 2 ≤ (L B : ℝ) := by rw [hLB]; exact hc s
  have hL0 : (0 : ℝ) ≤ L B := le_trans (by positivity) hLc
  have hfin : (M B : ℝ) ≤ (⌈K / c⌉₊ : ℝ) * (L B : ℝ) := by
    calc (M B : ℝ) ≤ ‖s‖ ^ 2 * K := hbound
      _ = K / c * (c * ‖s‖ ^ 2) := by field_simp
      _ ≤ K / c * (L B : ℝ) := by gcongr
      _ ≤ (⌈K / c⌉₊ : ℝ) * (L B : ℝ) := by gcongr; exact Nat.le_ceil _
  exact_mod_cast hfin

private theorem coe_bar_eq_complexConj {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) :
    ((H.bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E) := H.bar_eq a

theorem trace_mul_bar_pos {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (z : 𝓞 E) (hz : z ≠ 0) :
    0 < Algebra.trace ℤ (𝓞 E) (z * H.bar z) := by
  classical
  have hzE : (z : E) ≠ 0 := by exact_mod_cast hz
  have h1 : ((Algebra.trace ℤ (𝓞 E) (z * H.bar z) : ℤ) : ℚ) =
      Algebra.trace ℚ E ((z : E) * IsCMField.complexConj E (z : E)) := by
    rw [Algebra.coe_trace_int]
    push_cast [coe_bar_eq_complexConj]
    rfl
  have h2 := _root_.trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ)
    (x := (z : E) * IsCMField.complexConj E (z : E))
  have h3 : ∀ σ : E →ₐ[ℚ] ℂ, σ ((z : E) * IsCMField.complexConj E (z : E)) = ((Complex.normSq (σ z) : ℝ) : ℂ) := by
    intro σ
    rw [map_mul]
    have := IsCMField.complexEmbedding_complexConj E σ.toRingHom (z : E)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, Complex.mul_conj]
  simp only [h3] at h2
  rw [← Complex.ofReal_sum] at h2
  have hpos : 0 < ∑ σ : E →ₐ[ℚ] ℂ, Complex.normSq (σ z) := by
    obtain ⟨σ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    refine Finset.sum_pos' (fun τ _ => Complex.normSq_nonneg _) ⟨σ.toRatAlgHom, Finset.mem_univ _, ?_⟩
    rw [Complex.normSq_pos]
    exact (map_ne_zero_iff _ σ.injective).mpr hzE
  have h4 : ((Algebra.trace ℚ E ((z : E) * IsCMField.complexConj E (z : E)) : ℚ) : ℝ) =
      ∑ σ : E →ₐ[ℚ] ℂ, Complex.normSq (σ z) := by
    apply Complex.ofReal_injective
    rw [← h2]
    simp
  rw [← h1] at h4
  have : (0 : ℝ) < ((Algebra.trace ℤ (𝓞 E) (z * H.bar z) : ℤ) : ℝ) := by
    rw [show ((Algebra.trace ℤ (𝓞 E) (z * H.bar z) : ℤ) : ℝ) = (((Algebra.trace ℤ (𝓞 E) (z * H.bar z) : ℤ) : ℚ) : ℝ) by push_cast; rfl, h4]
    exact hpos
  exact_mod_cast this

theorem trace_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (z : 𝓞 E) :
    Algebra.trace ℤ (𝓞 E) (H.bar z) = Algebra.trace ℤ (𝓞 E) z := by
  let e : 𝓞 E ≃ₐ[ℤ] 𝓞 E := AlgEquiv.ofRingEquiv (f := H.bar) (fun x => by simp)
  exact Algebra.trace_eq_of_algEquiv e z

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (z : 𝓞 E) : H.bar (H.bar z) = z := by
  apply RingOfIntegers.ext
  rw [coe_bar_eq_complexConj, coe_bar_eq_complexConj, IsCMField.complexConj_apply_apply]

theorem exists_pos_form {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] :
    ∃ g : LinearMap.BilinForm ℤ X, g ∈ balForms H.bar X ∧ ∀ x, x ≠ 0 → 0 < g x x := by
  classical
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) X
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hs_inj : Function.Injective s := by
    intro x y h
    have hx := LinearMap.congr_fun hs x
    have hy := LinearMap.congr_fun hs y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
    rw [← hx, ← hy, h]
  let f : X → X → ℤ := fun x y => ∑ i, Algebra.trace ℤ (𝓞 E) (s x i * H.bar (s y i))
  let g : LinearMap.BilinForm ℤ X := LinearMap.mk₂ ℤ f
    (fun x x' y => by simp [f, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp only [f, map_zsmul, Pi.smul_apply, smul_mul_assoc, Finset.smul_sum])
    (fun x y y' => by simp [f, mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp only [f, map_zsmul, Pi.smul_apply, mul_smul_comm, Finset.smul_sum])
  have hg : ∀ x y, g x y = f x y := fun x y => rfl
  have hterm : ∀ a b : 𝓞 E, Algebra.trace ℤ (𝓞 E) (a * H.bar b) = Algebra.trace ℤ (𝓞 E) (b * H.bar a) := by
    intro a b
    rw [← trace_bar H (a * H.bar b), map_mul, bar_bar, mul_comm]
  refine ⟨g, ⟨fun x y => ?_, fun a x y => ?_⟩, fun x hx => ?_⟩
  · rw [hg, hg]
    exact Finset.sum_congr rfl fun i _ => hterm _ _
  · rw [hg, hg]
    simp only [f, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, bar_bar]
    exact Finset.sum_congr rfl fun i _ => by ring_nf
  · rw [hg]
    have hsx : s x ≠ 0 := by
      intro h0; apply hx; apply hs_inj; rw [h0, map_zero]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hsx
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, trace_mul_bar_pos H _ hi⟩
    by_cases hj : s x j = 0
    · simp [hj]
    · exact (trace_mul_bar_pos H _ hj).le

theorem sum_toMatrix {X : Type} [AddCommGroup X] {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (β : LinearMap.BilinForm ℤ X)
    (z : Fin n → ℤ) : ∑ j, ∑ k, z j * z k * LinearMap.BilinForm.toMatrix b β j k = β (∑ j, z j • b j) (∑ j, z j • b j) := by
  simp only [LinearMap.BilinForm.toMatrix_apply, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

def commutant (O X : Type) [CommRing O] [AddCommGroup X] [Module O X] : Subalgebra ℤ (Module.End ℤ X) where
  carrier := {a | ∀ (c : O) x, a (c • x) = c • a x}
  mul_mem' := fun {a a'} h h' c x => by
    change a (a' (c • x)) = c • a (a' x)
    rw [h' c x, h c _]
  add_mem' := fun {a a'} h h' c x => by simp only [LinearMap.add_apply, h c x, h' c x, smul_add]
  algebraMap_mem' := fun n c x => by
    simp only [Module.algebraMap_end_apply, smul_comm n c x]

theorem dominates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X := by
  intro E _ _ _ H X _ _ _ _
  classical
  obtain ⟨g, hgbal, hgpos⟩ := exists_pos_form H X
  have hgsym : ∀ x y, g x y = g y x := hgbal.1
  have hgbal' : ∀ (a : 𝓞 E) x y, g (a • x) y = g x (H.bar a • y) := hgbal.2
  have hg0 : ∀ x, g x x = 0 → x = 0 := by
    intro x h; by_contra hx; exact (hgpos x hx).ne' h
  have hgnn : ∀ x, 0 ≤ g x x := by
    intro x; by_cases hx : x = 0
    · simp [hx]
    · exact (hgpos x hx).le
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.IsTorsionFree ℤ X := ⟨fun c hc x y hxy => by
    change c • x = c • y at hxy
    have hc0 : c ≠ 0 := hc.ne_zero
    have h0 : c • (x - y) = 0 := by rw [smul_sub]; exact sub_eq_zero.mpr hxy
    have h1 : g (c • (x - y)) (c • (x - y)) = c * c * g (x - y) (x - y) := by
      simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul]; ring
    simp only [h0, map_zero, LinearMap.zero_apply] at h1
    have h2 : g (x - y) (x - y) = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact absurd (mul_self_eq_zero.mp h) hc0
      · exact h
    exact sub_eq_zero.mp (hg0 _ h2)⟩
  let b := Module.finBasis ℤ X
  let G : Matrix (Fin (Module.finrank ℤ X)) (Fin (Module.finrank ℤ X)) ℤ := LinearMap.BilinForm.toMatrix b g
  have hGs : Gᵀ = G := by
    ext i j; simp [G, LinearMap.BilinForm.toMatrix_apply, hgsym]
  have hGpos : ∀ z : Fin (Module.finrank ℤ X) → ℤ, z ≠ 0 → 0 < ∑ j, ∑ k, z j * z k * G j k := by
    intro z hz
    rw [sum_toMatrix]
    apply hgpos
    intro h0
    exact hz (funext fun i => Fintype.linearIndependent_iff.mp b.linearIndependent z h0 i)
  let 𝓡 : Subalgebra ℤ (Matrix (Fin (Module.finrank ℤ X)) (Fin (Module.finrank ℤ X)) ℤ) :=
    (commutant (𝓞 E) X).map (LinearMap.toMatrixAlgEquiv b).toAlgHom
  have htm : ∀ a : Module.End ℤ X, (LinearMap.toMatrixAlgEquiv b).toAlgHom a = LinearMap.toMatrix b b a := by
    intro a; ext i j
    change LinearMap.toMatrixAlgEquiv b a i j = _
    rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have hcompM : ∀ a l : Module.End ℤ X, LinearMap.BilinForm.toMatrix b (g.comp a l) =
      (LinearMap.toMatrix b b a)ᵀ * G * LinearMap.toMatrix b b l := fun a l =>
    LinearMap.BilinForm.toMatrix_comp b b g a l
  intro ℓ μ hℓ
  let Lm := ℓ ∘ₗ (Matrix.toBilin b).toLinearMap
  let Mm := μ ∘ₗ (Matrix.toBilin b).toLinearMap
  have hLpos : ∀ A ∈ 𝓡, A ≠ 0 → 0 < Lm (Aᵀ * G * A) := by
    intro A hA hA0
    obtain ⟨a, ha, rfl⟩ := Subalgebra.mem_map.mp hA
    have hac : ∀ (c : 𝓞 E) (x : X), a (c • x) = c • a x := ha
    rw [htm a] at hA0 ⊢
    have he : Lm ((LinearMap.toMatrix b b a)ᵀ * G * LinearMap.toMatrix b b a) = ℓ (g.comp a a) := by
      simp only [Lm, LinearMap.comp_apply, LinearEquiv.coe_coe, ← hcompM, Matrix.toBilin_toMatrix]
    rw [he]
    apply hℓ
    · refine ⟨fun y z => ?_, fun c y z => ?_⟩
      · simp only [LinearMap.BilinForm.comp_apply]; exact hgsym _ _
      · simp only [LinearMap.BilinForm.comp_apply]; rw [hac, hac, hgbal']
    · intro y; simp only [LinearMap.BilinForm.comp_apply]; exact hgnn _
    · intro h0
      apply hA0
      have : a = 0 := by
        ext y
        have := LinearMap.congr_fun₂ h0 y y
        simp only [LinearMap.BilinForm.comp_apply, LinearMap.zero_apply] at this
        simpa using hg0 _ this
      rw [this, map_zero]
  obtain ⟨C, hC⟩ := main_matrix G hGs hGpos 𝓡 Lm Mm hLpos
  refine ⟨C, fun β hβ hβnn => ?_⟩
  have hβs : ∀ y z, β y z = β z y := hβ.1
  have hβb : ∀ (a : 𝓞 E) y z, β (a • y) z = β y (H.bar a • z) := hβ.2
  set B := LinearMap.BilinForm.toMatrix b β with hBdef
  have hBs : Bᵀ = B := by
    ext i j; simp [B, LinearMap.BilinForm.toMatrix_apply, hβs]
  have hBnn : ∀ z : Fin (Module.finrank ℤ X) → ℤ, 0 ≤ ∑ j, ∑ k, z j * z k * B j k := fun z => by
    rw [hBdef, sum_toMatrix]; exact hβnn _
  let T := Matrix.toLin b b (G.adjugate * B)
  have hTm : LinearMap.toMatrix b b T = G.adjugate * B := LinearMap.toMatrix_toLin b b _
  have key : g.comp LinearMap.id T = G.det • β := by
    apply (LinearMap.BilinForm.toMatrix b).injective
    rw [hcompM, LinearMap.toMatrix_id, hTm, Matrix.transpose_one, Matrix.one_mul, ← Matrix.mul_assoc,
      Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul, map_smul]
  have hkey : ∀ u v, g u (T v) = G.det * β u v := by
    intro u v
    have := LinearMap.congr_fun₂ key u v
    simpa using this
  have hTc : ∀ (c : 𝓞 E) (x : X), T (c • x) = c • T x := by
    intro c x
    apply sub_eq_zero.mp
    apply hg0
    have h1 : ∀ u, g u (c • T x) = G.det * β u (c • x) := by
      intro u
      calc g u (c • T x) = g (c • T x) u := hgsym _ _
        _ = g (T x) (H.bar c • u) := hgbal' _ _ _
        _ = g (H.bar c • u) (T x) := hgsym _ _
        _ = G.det * β (H.bar c • u) x := hkey _ _
        _ = G.det * β u (c • x) := by rw [hβb, bar_bar]
    rw [map_sub, hkey, h1, sub_self]
  have hBR : G.adjugate * B ∈ 𝓡 := Subalgebra.mem_map.mpr ⟨T, hTc, by rw [htm, hTm]⟩
  have hfin := hC B hBs hBnn hBR
  simpa [Lm, Mm, B, Matrix.toBilin_toMatrix] using hfin

end GlobalTheory.DomBal
