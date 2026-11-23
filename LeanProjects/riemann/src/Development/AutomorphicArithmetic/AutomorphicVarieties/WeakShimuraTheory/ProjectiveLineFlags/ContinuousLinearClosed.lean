import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair

section
open IsLocalRing Matrix Polynomial UpperTheory.V.W

end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem eq_zero_of_smul_mul_eq_mul_of_isNilpotent_constantCoeff {K : Type} [Field K] {n : ℕ} (A Y : Matrix (Fin n) (Fin n) (PowerSeries K)) (e c : PowerSeries K)
    (hN : IsNilpotent ((A - c • (1 : Matrix (Fin n) (Fin n) (PowerSeries K))).map PowerSeries.constantCoeff))
    (he : PowerSeries.constantCoeff e ≠ 1) (hc : PowerSeries.constantCoeff c ≠ 0)
    (hY : e • (A * Y) = Y * A) : Y = 0 := by
  set N := A - c • (1 : Matrix (Fin n) (Fin n) (PowerSeries K)) with hNdef
  set V := e • A - c • (1 : Matrix (Fin n) (Fin n) (PowerSeries K)) with hVdef
  have hYN : Y * N = V * Y := by
    rw [hNdef, hVdef, mul_sub, sub_mul, ← hY, Matrix.mul_smul, mul_one, Matrix.smul_mul, Matrix.smul_mul, one_mul]
  have hpow : ∀ k : ℕ, Y * N ^ k = V ^ k * Y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, hYN, ← mul_assoc]
  obtain ⟨m, hm⟩ := hN
  let cc := (PowerSeries.constantCoeff : PowerSeries K →+* K).mapMatrix (m := Fin n)
  have hm' : cc (N ^ m) = 0 := by
    rw [map_pow]
    exact hm
  have hdvd : ∀ i j, (PowerSeries.X : PowerSeries K) ∣ (N ^ m) i j := by
    intro i j
    rw [PowerSeries.X_dvd_iff]
    have := congrFun (congrFun hm' i) j
    simpa [cc] using this
  choose Q hQ using hdvd
  have hNm : N ^ m = (PowerSeries.X : PowerSeries K) • Matrix.of Q := by
    ext i j
    simp [hQ i j]
  have hcV : cc V = ((PowerSeries.constantCoeff e - 1) * PowerSeries.constantCoeff c) • (1 : Matrix (Fin n) (Fin n) K) + PowerSeries.constantCoeff e • cc N := by
    ext i j
    simp only [cc, hVdef, hNdef, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp <;> ring
  have hV : IsUnit V := by
    rw [Matrix.isUnit_iff_isUnit_det, PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, ← Matrix.isUnit_iff_isUnit_det]
    change IsUnit (cc V)
    rw [hcV]
    apply IsNilpotent.isUnit_add_left_of_commute
    · exact ⟨m, by rw [_root_.smul_pow, show cc N ^ m = 0 by rw [← map_pow]; exact hm', smul_zero]⟩
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (isUnit_iff_ne_zero.mpr (mul_ne_zero (sub_ne_zero.mpr he) hc)).pow _
    · exact (Commute.one_right _).smul_right _
  have hVm : V ^ m * Y = (PowerSeries.X : PowerSeries K) • (Y * Matrix.of Q) := by
    rw [← hpow, hNm, Matrix.mul_smul]
  let W : Matrix (Fin n) (Fin n) (PowerSeries K) := ((hV.unit ^ m)⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries K))ˣ)
  have hWV : W * V ^ m = 1 := by
    have h1 : ((hV.unit ^ m : (Matrix (Fin n) (Fin n) (PowerSeries K))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries K)) = V ^ m := by
      simp
    rw [← h1]
    exact Units.inv_mul _
  have hYeq : Y = (PowerSeries.X : PowerSeries K) • (W * Y * Matrix.of Q) := by
    calc Y = W * (V ^ m * Y) := by rw [← mul_assoc, hWV, one_mul]
      _ = _ := by rw [hVm, Matrix.mul_smul, mul_assoc]
  have hk : ∀ k : ℕ, ∃ Z : Matrix (Fin n) (Fin n) (PowerSeries K), Y = ((PowerSeries.X : PowerSeries K) ^ k) • Z := by
    intro k
    induction k with
    | zero => exact ⟨Y, by simp⟩
    | succ k ih =>
      obtain ⟨Z, hZ⟩ := ih
      refine ⟨W * Z * Matrix.of Q, ?_⟩
      conv_lhs => rw [hYeq]
      rw [hZ, Matrix.mul_smul, Matrix.smul_mul, smul_smul, pow_succ']
  ext i j d
  obtain ⟨Z, hZ⟩ := hk (d + 1)
  have hdv : (PowerSeries.X : PowerSeries K) ^ (d + 1) ∣ Y i j := ⟨Z i j, by rw [hZ]; simp⟩
  rw [PowerSeries.X_pow_dvd_iff] at hdv
  simpa using hdv d (Nat.lt_succ_self d)

private theorem charpoly_mat_map_constantCoeff_eq_prod_X_sub_C {l : ℕ} [Fact (Nat.Prime l)] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (x : W.Point r) (g : F.G₀) :
    Matrix.charpoly ((W.mat x.ρ g).map PowerSeries.constantCoeff) = ∏ i, (Polynomial.X - Polynomial.C (algebraMap (ResidueField O) x.K (r.chib i g : ResidueField O))) := by
  have h := congrArg (fun D : W.GDet n x.K F.G₀ => D.D (Polynomial x.K) (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single g 1)) x.red
  simp only [W.GDet.map, W.GDet.ofRep, W.Resid.Dbar, MonoidHom.coe_comp, Function.comp_apply, map_sub, W.GDet.repAlg, MonoidAlgebra.lift_single] at h
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, MonoidAlgebra.lift_single, map_one, Matrix.coe_detMonoidHom, MonoidHom.coe_comp, Function.comp_apply, one_smul] at h
  rw [← Matrix.det_diagonal, Matrix.charpoly]
  convert h using 2
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.charmatrix_apply, Matrix.one_apply]
      rfl
    · simp [Matrix.charmatrix_apply, Matrix.one_apply, hij]
      rfl
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [W.diagRep, Matrix.one_apply]
      rfl
    · simp [W.diagRep, Matrix.one_apply, hij]

theorem UpperTheory.V.Ws.P1.n4V0 :
    ∀ (l : ℕ) [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : W.Resid F O n), r.V0ok → ∀ x : W.Point r, x.N4 := by
  intro l _ F O _ _ _ n r hV0 x X hX
  obtain ⟨_, hD0, g, hg, hεg⟩ := hV0
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Subsingleton.elim _ _
  let i0 : Fin n := ⟨0, hn⟩
  let A : Matrix (Fin n) (Fin n) x.A := W.mat x.ρ g
  let e : x.A := algebraMap O x.A (algebraMap ℤ_[l] O ((F.ε (g : F.Γ) : ℤ_[l]ˣ) : ℤ_[l]))
  let χ : ResidueField O := (r.chib i0 g : ResidueField O)
  let c : x.A := PowerSeries.C (algebraMap (ResidueField O) x.K χ)
  obtain ⟨⟨b, hb⟩, hbY⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors x.A) (fun p : Fin n × Fin n => X p.1 p.2)
  choose Yf hYf using fun p => RingHom.mem_rangeS.mp (hbY p)
  let Y : Matrix (Fin n) (Fin n) x.A := Matrix.of fun i j => Yf (i, j)
  let φ := (algebraMap x.A x.Fr).mapMatrix (m := Fin n)
  have hφinj : Function.Injective φ := Matrix.map_injective (IsFractionRing.injective x.A x.Fr)
  have hφY : φ Y = algebraMap x.A x.Fr b • X := by
    ext i j
    simp only [φ, Y, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply]
    rw [hYf (i, j), Algebra.smul_def, smul_eq_mul]
  have hφA : φ A = W.mat x.ρF g := rfl
  have hφe : algebraMap x.A x.Fr e = ((F.eps O x.Fr g : x.Frˣ) : x.Fr) := rfl
  have hY : e • (A * Y) = Y * A := by
    apply hφinj
    have hX' := hX g hg
    rw [← hφe] at hX'
    rw [map_mul, hφY, hφA]
    have h1 : φ (e • (A * Y)) = algebraMap x.A x.Fr e • (φ A * φ Y) := by
      ext i j
      simp [φ, Matrix.smul_apply, Matrix.mul_apply, map_sum]
    rw [h1, hφY, hφA, Matrix.mul_smul, smul_comm, hX', Matrix.smul_mul]
  have hall : ∀ i, (r.chib i g : ResidueField O) = χ := fun i => congrArg Units.val (hD0 g hg i i0)
  have hcp := charpoly_mat_map_constantCoeff_eq_prod_X_sub_C x g
  simp only [hall] at hcp
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcp
  have hCH := Matrix.aeval_self_charpoly (A.map PowerSeries.constantCoeff)
  rw [hcp] at hCH
  simp only [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
  have hNm : (A - c • (1 : Matrix (Fin n) (Fin n) x.A)).map PowerSeries.constantCoeff = A.map PowerSeries.constantCoeff - algebraMap x.K (Matrix (Fin n) (Fin n) x.K) (algebraMap (ResidueField O) x.K χ) := by
    ext i j
    simp [c, Matrix.one_apply, Algebra.algebraMap_eq_smul_one]
    split_ifs <;> simp
  have hnil : IsNilpotent ((A - c • (1 : Matrix (Fin n) (Fin n) x.A)).map PowerSeries.constantCoeff) := ⟨n, by rw [hNm]; exact hCH⟩
  have he : PowerSeries.constantCoeff e ≠ 1 := by
    intro h
    apply hεg
    ext
    apply (algebraMap (ResidueField O) x.K).injective
    rw [Units.val_one, map_one, ← h]
    simp only [e, PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C, IsScalarTower.algebraMap_apply O (ResidueField O) x.K]
    rfl
  have hc : PowerSeries.constantCoeff c ≠ 0 := by
    simp only [c, PowerSeries.constantCoeff_C]
    exact (_root_.map_ne_zero _).mpr (Units.ne_zero _)
  have hY0 := eq_zero_of_smul_mul_eq_mul_of_isNilpotent_constantCoeff A Y e c hnil he hc hY
  ext i j
  have h2 : Yf (i, j) = 0 := by
    have := congrFun (congrFun hY0 i) j
    simpa [Y] using this
  have h1 : algebraMap x.A x.Fr b * X i j = 0 := by
    rw [← Algebra.smul_def]
    have h3 := hYf (i, j)
    rw [h2, map_zero] at h3
    exact h3.symm
  have hb' : algebraMap x.A x.Fr b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  rw [Matrix.zero_apply]
  exact (mul_eq_zero.mp h1).resolve_left hb'
