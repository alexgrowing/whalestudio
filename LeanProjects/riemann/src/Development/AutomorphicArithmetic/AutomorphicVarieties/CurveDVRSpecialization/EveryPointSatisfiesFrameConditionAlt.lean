import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition

open IsLocalRing Matrix Polynomial UpperTheory.V.W

private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  rw [← Matrix.charpoly_map]
  simp only [GDet.chi, GDet.map, GDet.ofRep]
  rw [Matrix.charpoly]
  simp only [MonoidHom.comp_apply, MonoidHom.coe_coe, Matrix.coe_detMonoidHom]
  congr 1
  simp only [MonoidAlgebra.mapRingHom_single, map_one, GDet.repAlg, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_sub, MonoidAlgebra.lift_single]
  refine Matrix.ext fun i k => ?_
  simp [Matrix.charmatrix_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [Matrix.diagonal_apply]
  rfl

private theorem aeval_mapM {n : ℕ} {A K : Type} [CommRing A] [CommRing K] (f : A →+* K)
    (M : Matrix (Fin n) (Fin n) A) (q : A[X]) :
    f.mapMatrix (aeval M q) = aeval (f.mapMatrix M) (q.map f) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, Polynomial.map_monomial, map_mul, map_pow]
    congr 1
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, RingHom.mapMatrix_apply, apply_ite f]

private theorem aeval_inter {n : ℕ} {K : Type} [CommRing K] (M N Y : Matrix (Fin n) (Fin n) K)
    (h : N * Y = Y * M) (q : K[X]) : aeval N q * Y = Y * aeval M q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, mul_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial]
    have hpow : N ^ k * Y = Y * M ^ k := by
      induction k with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc]
    rw [mul_assoc, hpow, ← mul_assoc, ← mul_assoc, Algebra.commutes]

private theorem key {n : ℕ} {A K F : Type} [CommRing A] [Field K] [Field F] (f : A →+* K) (j : A →+* F)
    (hj : Function.Injective j) (M : Matrix (Fin n) (Fin n) A) (x : A) (c : K) (hc : c ≠ 0) (hx : f x ≠ 1)
    (hM : M.charpoly.map f = (X - C c) ^ n) (Y : Matrix (Fin n) (Fin n) F)
    (hY : j x • (j.mapMatrix M * Y) = Y * j.mapMatrix M) : Y = 0 := by
  classical
  set p := M.charpoly with hp
  set Mf := f.mapMatrix M with hMf
  set Mj := j.mapMatrix M with hMj
  have hint : aeval (j x • Mj) (p.map j) * Y = Y * aeval Mj (p.map j) :=
    aeval_inter Mj (j x • Mj) Y (by rw [smul_mul_assoc]; exact hY) _
  have hCH : aeval Mj (p.map j) = 0 := by
    rw [hp, ← Matrix.charpoly_map]
    exact Matrix.aeval_self_charpoly _
  rw [hCH, mul_zero] at hint
  have hfc : Mf.charpoly = (X - C c) ^ n := by
    rw [hMf, RingHom.mapMatrix_apply, Matrix.charpoly_map]
    exact hM
  set Nl := Mf - algebraMap K (Matrix (Fin n) (Fin n) K) c with hNl
  have hnil : IsNilpotent Nl := by
    refine ⟨n, ?_⟩
    have h0 := Matrix.aeval_self_charpoly Mf
    rw [hfc, map_pow, map_sub, aeval_X, aeval_C] at h0
    exact h0
  set s : K := (f x - 1) * c with hs
  have hs0 : s ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hx) hc
  have hunitF : IsUnit (aeval (f x • Mf) (p.map f)) := by
    rw [hp, hM, map_pow, map_sub, aeval_X, aeval_C]
    apply IsUnit.pow
    have heq : f x • Mf - algebraMap K (Matrix (Fin n) (Fin n) K) c =
        algebraMap K (Matrix (Fin n) (Fin n) K) s * ((s⁻¹ * f x) • Nl + 1) := by
      rw [← Algebra.smul_def, smul_add, smul_smul, mul_inv_cancel_left₀ hs0, hNl, hs,
        Algebra.algebraMap_eq_smul_one]
      module
    rw [heq]
    exact (IsUnit.map _ (Ne.isUnit hs0)).mul (hnil.smul _).isUnit_add_one
  set D : A := (aeval (x • M) p).det with hD
  have hfD : f D ≠ 0 := by
    have hsm : f.mapMatrix (x • M) = f x • Mf := by
      ext i k
      simp [hMf]
    have h1 : f D = (aeval (f x • Mf) (p.map f)).det := by
      rw [hD, RingHom.map_det, aeval_mapM, hsm]
    rw [h1]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hunitF).ne_zero
  have hD0 : D ≠ 0 := fun h => hfD (by rw [h, map_zero])
  have hjD : (aeval (j x • Mj) (p.map j)).det ≠ 0 := by
    have hsm : j.mapMatrix (x • M) = j x • Mj := by
      ext i k
      simp [hMj]
    have h1 : j D = (aeval (j x • Mj) (p.map j)).det := by
      rw [hD, RingHom.map_det, aeval_mapM, hsm]
    rw [← h1]
    exact fun h => hD0 (hj (by rw [h, map_zero]))
  have hU : IsUnit (aeval (j x • Mj) (p.map j)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hjD)
  exact (hU.mul_right_eq_zero).mp hint

private theorem absolute_irreducible_rank_four {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {n : ℕ} {r : Resid F O n} (h : r.V0ok) (y : Point r) : y.N4 := by
  intro X hX
  obtain ⟨-, hchi, g, hg, heps⟩ := h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    ext i
    exact i.elim0
  letI := y.field
  haveI := y.fin
  letI := y.algk
  letI := y.algO
  haveI := y.tower
  let i0 : Fin n := ⟨0, hn⟩
  let z : O := algebraMap ℤ_[l] O (F.ε g)
  let c : y.K := algebraMap (ResidueField O) y.K (r.chib i0 g)
  refine key (PowerSeries.constantCoeff) (algebraMap y.A y.Fr) (IsFractionRing.injective _ _) (mat y.ρ g)
    (algebraMap O y.A z) c ?_ ?_ ?_ X ?_
  · exact (_root_.map_ne_zero _).mpr (Units.ne_zero _)
  · intro h1
    apply heps
    apply Units.ext
    apply (algebraMap (ResidueField O) y.K).injective
    rw [Units.val_one, map_one, ← h1]
    show algebraMap (ResidueField O) y.K (algebraMap O (ResidueField O) z) =
      PowerSeries.constantCoeff (algebraMap O y.A z)
    rw [← IsScalarTower.algebraMap_apply]
    first
    | rfl
    | simp [PowerSeries.algebraMap_apply']
  · have hred := congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) y.red
    simp only [Resid.Dbar, chi_map_ofRep] at hred
    rw [hred]
    show Polynomial.map _ (Matrix.diagonal fun i => ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)).charpoly = _
    rw [Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hall : ∀ i : Fin n, (Polynomial.X - C (algebraMap (ResidueField O) y.K ↑((r.chib i) g))) =
        Polynomial.X - C c := fun i => by rw [hchi g hg i i0]
    simp only [hall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have := hX g hg
    exact this

theorem UpperTheory.V.Pr.n4Of :
    UpperTheory.V.Pr.EveryPointSatisfiesFrameCondition := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M _ L _ _ _ _ _ Φ k c₁ _ f n ka R y
  exact absolute_irreducible_rank_four R.v0 y
