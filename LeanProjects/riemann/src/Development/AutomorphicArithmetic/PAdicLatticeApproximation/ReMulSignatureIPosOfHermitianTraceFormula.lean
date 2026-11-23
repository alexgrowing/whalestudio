import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open scoped ComplexOrder
open UpperTheory.Gal.W2

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

private lemma hvAddL {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x x' y : Fin n → ℂ) :
    hv M (x + x') y = hv M x y + hv M x' y := by
  simp [hv, Matrix.mulVec_add, dotProduct_add]

private lemma hvAddR {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y y' : Fin n → ℂ) :
    hv M x (y + y') = hv M x y + hv M x y' := by
  simp [hv, add_dotProduct]

private lemma hvSmulL {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) (x y : Fin n → ℂ) :
    hv M (a • x) y = (a : ℂ) * hv M x y := by
  have : a • x = (a : ℂ) • x := by ext i; simp
  rw [this]
  simp [hv, Matrix.mulVec_smul, dotProduct_smul]

private lemma hvSmulR {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) (x y : Fin n → ℂ) :
    hv M x (a • y) = (a : ℂ) * hv M x y := by
  have : a • y = (a : ℂ) • y := by ext i; simp
  rw [this]
  simp [hv, star_smul, smul_dotProduct]

private noncomputable def thR (th : VQ D →+ Arch G) : ℝ ⊗[ℚ] VQ D →ₗ[ℝ] Arch G :=
  LinearMap.liftBaseChange ℝ th.toRatLinearMap

private lemma thR_tmul (th : VQ D →+ Arch G) (a : ℝ) (w : VQ D) :
    thR th (a ⊗ₜ w) = a • th w := by
  simp [thR]

private lemma psiR_tm (G : HTGroup p) (v : InfinitePlace G.F) (r : ℝ) (c : G.C) :
    G.psiR v (r ⊗ₜ c) = r • G.psi v c := by
  rw [Algebra.smul_def]
  unfold HTGroup.psiR
  erw [Algebra.TensorProduct.lift_tmul]
  rfl

private lemma thR_act (L : Link D G) (th : VQ D →+ Arch G)
    (hrep : ∀ c w v, th (L.rep c w) v = G.psi v c *ᵥ th w v)
    (a : ℝ ⊗[ℚ] G.C) (x : ℝ ⊗[ℚ] VQ D) (v : InfinitePlace G.F) :
    thR th (actOn L.rep ℝ a x) v = G.psiR v a *ᵥ thR th x v := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, ha, hb, Matrix.add_mulVec]
  | tmul r c =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add, Pi.add_apply, hx, hy, Matrix.mulVec_add]
    | tmul s w =>
      have h : actOn L.rep ℝ (r ⊗ₜ c) (s ⊗ₜ w) = (r * s) ⊗ₜ (L.rep c w) := by
        simp [actOn, Algebra.TensorProduct.lift_tmul, Module.End.baseChangeHom, Algebra.ofId_apply,
          Module.algebraMap_end_apply]
        change r • (s ⊗ₜ[ℚ] (L.rep c w)) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul]
      rw [h, thR_tmul, thR_tmul, psiR_tm, Pi.smul_apply, Pi.smul_apply, hrep,
        Matrix.smul_mulVec, Matrix.mulVec_smul, mul_smul]

private lemma form_ext (th : VQ D →+ Arch G) (lam : InfinitePlace G.F → ℂ)
    (hform : ∀ u w, ((D.EF.baseChange ℚ u w : ℚ) : ℝ) = ∑ v, 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re)
    (x y : ℝ ⊗[ℚ] VQ D) :
    (D.EF.baseChange ℚ).baseChange ℝ x y
      = ∑ v, 2 * (lam v * hv (G.gram v) (thR th x v) (thR th y v)).re := by
  induction x using TensorProduct.induction_on with
  | zero => simp [hv]
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', Pi.add_apply, hvAddL, mul_add, Complex.add_re,
      Finset.sum_add_distrib]
  | tmul a u =>
    induction y using TensorProduct.induction_on with
    | zero => simp [hv]
    | add y y' hy hy' =>
      simp only [map_add, hy, hy', Pi.add_apply, hvAddR, mul_add, Complex.add_re, Finset.sum_add_distrib]
    | tmul b w =>
      rw [LinearMap.BilinForm.baseChange_tmul, thR_tmul, thR_tmul]
      have hterm : ∀ v, 2 * (lam v * hv (G.gram v) ((a • th u) v) ((b • th w) v)).re
          = (a * b) * (2 * (lam v * hv (G.gram v) (th u v) (th w v)).re) := by
        intro v
        have e : lam v * hv (G.gram v) ((a • th u) v) ((b • th w) v)
            = ((a * b : ℝ) : ℂ) * (lam v * hv (G.gram v) (th u v) (th w v)) := by
          rw [Pi.smul_apply, Pi.smul_apply, hvSmulL, hvSmulR]
          push_cast
          ring
        rw [e, Complex.re_ofReal_mul]
        ring
      rw [Finset.sum_congr rfl fun v _ => hterm v, ← Finset.mul_sum, ← hform, Rat.smul_def]
      ring

end

theorem UpperTheory.re_mul_signature_I_pos_of_hermitian_trace_formula :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (th : VQ D →+ Arch G) (lam : InfinitePlace G.F → ℂ), (∀ c w v, th (L.rep c w) v = G.psi v c *ᵥ th w v) → (∀ u w, ((D.EF.baseChange ℚ u w : ℚ) : ℝ) = ∑ v, 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re) → Submodule.span ℝ (Set.range th) = ⊤ → (∀ v, (starRingEnd ℂ) (lam v) = -lam v) → ∀ v, 0 < (lam v * sgnV L v * Complex.I).re := by
  intro p _ D G L th lam hrep hform hspan _ v
  obtain ⟨J, -, -, hpos, hPD⟩ := L.orient
  have hsurj : Function.Surjective (thR th) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨(1 : ℝ) ⊗ₜ w, by simp [thR_tmul]⟩
  set z : Fin G.n → ℂ := Pi.single ⟨0, G.n_pos⟩ 1 with hz
  have hz0 : z ≠ 0 := by
    intro h
    have := congrFun h ⟨0, G.n_pos⟩
    simp [hz] at this
  obtain ⟨x, hx⟩ := hsurj (Pi.single v z)
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := congrFun hx v
    simp at this
    exact hz0 this.symm
  have h1 := hpos x hx0
  rw [form_ext th lam hform] at h1
  have hsum : ∑ v', 2 * (lam v' * hv (G.gram v') (thR th (actOn L.rep ℝ J x) v') (thR th x v')).re
      = 2 * (lam v * hv (G.gram v) (G.psiR v J *ᵥ z) z).re := by
    rw [Finset.sum_eq_single v]
    · rw [thR_act L th hrep, hx]; simp
    · intro v' _ hv'
      rw [hx]
      simp [hv, Pi.single_eq_of_ne hv']
    · simp
  rw [hsum] at h1
  have hif : (if v.embedding (L.e D.ω) = D.ρc then -Complex.I else Complex.I) = -(sgnV L v * Complex.I) := by
    unfold sgnV
    split_ifs <;> simp
  have hss : sgnV L v * sgnV L v = 1 := by
    unfold sgnV
    split_ifs <;> simp
  have hq := (hPD v).dotProduct_mulVec_pos hz0
  rw [hif] at hq
  set h := hv (G.gram v) (G.psiR v J *ᵥ z) z with hh
  set q := star z ⬝ᵥ ((-(sgnV L v * Complex.I) • (G.gram v * G.psiR v J)) *ᵥ z) with hqdef
  have hqe : q = -(sgnV L v * Complex.I) * h := by
    simp [hqdef, hh, hv, Matrix.neg_mulVec, Matrix.smul_mulVec, dotProduct_smul, Matrix.mulVec_mulVec]
  have hhq : h = sgnV L v * Complex.I * q := by
    rw [hqe]
    linear_combination (Complex.I * Complex.I * h) * hss + h * Complex.I_mul_I
  obtain ⟨hqre, hqim⟩ := Complex.pos_iff.1 hq
  have hqr : q = (q.re : ℂ) := by
    apply Complex.ext <;> simp [← hqim]
  have hfin : (lam v * h).re = (lam v * sgnV L v * Complex.I).re * q.re := by
    rw [hhq, hqr]
    have : lam v * (sgnV L v * Complex.I * (q.re : ℂ)) = (lam v * sgnV L v * Complex.I) * (q.re : ℂ) := by ring
    simp only [Complex.ofReal_re]
    rw [this, Complex.re_mul_ofReal]
  rw [hfin] at h1
  have h2 : 0 < (lam v * sgnV L v * Complex.I).re * q.re := by linarith
  exact (mul_pos_iff_of_pos_right hqre).1 h2
