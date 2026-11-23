import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem pow_mul_Sb {g : ℕ} {H Sb : Matrix (Fin g) (Fin g) ℂ} {ev : Fin g → ℂ}
    (h : H * Sb = Sb * Matrix.diagonal ev) (i : ℕ) :
    H ^ i * Sb = Sb * Matrix.diagonal (fun j => ev j ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [_root_.pow_succ, _root_.mul_assoc, h, ← _root_.mul_assoc, ih, _root_.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    simp only [_root_.pow_succ]

private theorem sum_mul_Sb {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] {g : ℕ}
    {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {a : 𝓞 F →+* O} {H Sb : Matrix (Fin g) (Fin g) ℂ}
    {ty : Fin g → (F →+* ℂ)} {ev : Fin g → ℂ} (hD : IsDiag a ρ H Sb ty ev) (q : (𝓞 F)[X]) :
    (q.sum fun i b => ρ (a b) * H ^ i) * Sb =
      Sb * Matrix.diagonal (fun j => ((q.map (algebraMap (𝓞 F) F)).map (ty j)).eval (ev j)) := by
  obtain ⟨-, hc, hH⟩ := hD
  have key : ∀ (i : ℕ) (b : 𝓞 F), ρ (a b) * H ^ i * Sb =
      Sb * Matrix.diagonal (fun j => ty j (b : F) * ev j ^ i) := by
    intro i b
    rw [_root_.mul_assoc, pow_mul_Sb hH i, ← _root_.mul_assoc, hc b, _root_.mul_assoc,
      Matrix.diagonal_mul_diagonal]
  simp only [Polynomial.sum_def, Finset.sum_mul, key, ← Finset.mul_sum]
  congr 1
  ext k l
  simp only [Matrix.sum_apply, Matrix.diagonal_apply, Polynomial.map_map, Polynomial.eval_map,
    Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  split_ifs with hkl
  · subst hkl
    rfl
  · simp

theorem UpperTheory.Gal.W2.rootsFull_of :
    UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.PowSumRat → UpperTheory.Gal.W2.NewtonPoly → UpperTheory.Gal.W2.KillsMat → UpperTheory.Gal.W2.RootsFull := by
  intro hTC hPS hNP hKM F _ _ O _ bar g ρ a n t₀ ε hS D P₀ hP ga H hga Sb ty ev hD χ hχ hdeg τ
  have hcard : ∀ σ, (evFull ty ev σ).card = n :=
    fun σ => (hTC F O bar g ρ a n t₀ ε hS H Sb ty ev hD σ).2
  obtain ⟨ψ, hψm, hψd, hψ⟩ :=
    hNP F n (evFull ty ev) hcard (hPS F O bar g ρ a D P₀ hP ga H hga Sb ty ev hD)
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors (𝓞 F)) ψ
  set q := IsLocalization.integerNormalization (nonZeroDivisors (𝓞 F)) ψ
  have hb' : q.map (algebraMap (𝓞 F) F) = Polynomial.C (algebraMap (𝓞 F) F (b : 𝓞 F)) * ψ := by
    rw [hb, Polynomial.C_mul', algebraMap_smul]
  have h0 : (fun j => ((q.map (algebraMap (𝓞 F) F)).map (ty j)).eval (ev j)) = 0 := by
    funext j
    have hmem : ev j ∈ evFull ty ev (ty j) :=
      Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨j, by simp, rfl⟩))
    rw [hb', Polynomial.map_mul, Polynomial.eval_mul, hψ (ty j), Polynomial.eval_multiset_prod,
      Pi.zero_apply]
    apply mul_eq_zero_of_right
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map]
    exact Multiset.mem_map.2 ⟨ev j, hmem, by simp⟩
  have h1 := sum_mul_Sb hD q
  rw [h0, show Matrix.diagonal (0 : Fin g → ℂ) = 0 from Matrix.diagonal_zero,
    Matrix.mul_zero] at h1
  have hu : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hD.1
  have hsum : (q.sum fun i c => ρ (a c) * H ^ i) = 0 := by
    rw [← Matrix.mul_one (q.sum fun i c => ρ (a c) * H ^ i), ← Matrix.mul_nonsing_inv Sb hu,
      ← Matrix.mul_assoc, h1, Matrix.zero_mul]
  have hk := (hKM F O bar g ρ a D P₀ hP ga H hga q).2 hsum
  have hdvd : χ ∣ ψ := by
    have := (hχ.2 q).1 hk
    rw [hb'] at this
    have hne : algebraMap (𝓞 F) F (b : 𝓞 F) ≠ 0 :=
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
    exact (Polynomial.dvd_C_mul hne).1 this
  have heq : ψ = χ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hχ.1 hψm hdvd (by rw [hψd, hdeg])
  show (Polynomial.map τ χ).roots = _
  rw [← heq, hψ τ, Polynomial.roots_multiset_prod_X_sub_C]
