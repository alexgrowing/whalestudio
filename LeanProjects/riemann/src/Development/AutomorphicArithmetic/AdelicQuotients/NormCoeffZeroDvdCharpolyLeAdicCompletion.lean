import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem charpoly_scale {K : Type} [Field K] [Infinite K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [Polynomial.scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly,
    Matrix.eval_charpoly, ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

private theorem coeff_zero_mem {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (hN : ∀ i j, N i j ∈ O) (q : K[X]) (hq : q.Monic)
    (hd : q ∣ N.charpoly) : q.coeff 0 ∈ O := by
  let N' : Matrix (Fin n) (Fin n) O := fun i j => ⟨N i j, hN i j⟩
  have hmap : N'.map (algebraMap O K) = N := by
    ext i j
    rfl
  have hd' : q ∣ (N'.charpoly).map (algebraMap O K) := by
    rw [← Matrix.charpoly_map, hmap]
    exact hd
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (Matrix.charpoly_monic N') hd'
  rw [hq.leadingCoeff, map_one, mul_one] at hg
  rw [← hg, coeff_map]
  exact (g.coeff 0).2

theorem UpperTheory.norm_coeff_zero_dvd_charpoly_le_adicCompletion :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (R : ℝ), 1 ≤ R →
        (∀ i j, ‖M i j‖ ≤ R) → ∀ p : (w.adicCompletion E)[X], p.Monic → p ∣ M.charpoly → ‖p.coeff 0‖ ≤ R ^ n := by
  intro E _ _ w n M R hR hM p hp hd
  classical
  haveI : Infinite (w.adicCompletion E) :=
    Infinite.of_injective _ (algebraMap E (w.adicCompletion E)).injective

  let S : Finset (w.adicCompletion E) :=
    insert 1 (Finset.univ.image fun ij : Fin n × Fin n => M ij.1 ij.2)
  obtain ⟨c, hcS, hcmax⟩ := Finset.exists_max_image S (fun x => ‖x‖) ⟨1, Finset.mem_insert_self _ _⟩
  have hc1 : 1 ≤ ‖c‖ := by
    have := hcmax 1 (Finset.mem_insert_self _ _)
    simpa using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc1
    linarith
  have hcR : ‖c‖ ≤ R := by
    rcases Finset.mem_insert.1 hcS with rfl | h
    · simpa using hR
    · obtain ⟨ij, -, rfl⟩ := Finset.mem_image.1 h
      exact hM _ _
  have hent : ∀ i j, ‖M i j‖ ≤ ‖c‖ := fun i j =>
    hcmax _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hinv : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have hint : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 → x ∈ w.adicCompletionIntegers E := fun x hx =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 (Valued.toNormedField.norm_le_one_iff.1 hx)
  have hint' : ∀ x : w.adicCompletion E, x ∈ w.adicCompletionIntegers E → ‖x‖ ≤ 1 := fun x hx =>
    Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 hx)
  have hN : ∀ i j, (c⁻¹ • M) i j ∈ w.adicCompletionIntegers E := by
    intro i j
    apply hint
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hent i j) (norm_nonneg _)
  have hq : (p.scaleRoots c⁻¹).Monic := (Polynomial.monic_scaleRoots_iff _).2 hp
  have hdq : p.scaleRoots c⁻¹ ∣ (c⁻¹ • M).charpoly := by
    rw [charpoly_scale M hinv]
    obtain ⟨r, hr⟩ := hd
    rw [hr, Polynomial.mul_scaleRoots_of_noZeroDivisors]
    exact dvd_mul_right _ _
  have hmem := hint' _ (coeff_zero_mem _ _ hN _ hq hdq)
  rw [Polynomial.coeff_scaleRoots, Nat.sub_zero, norm_mul, norm_pow, norm_inv, inv_pow] at hmem
  have hcpos : 0 < ‖c‖ ^ p.natDegree := by positivity
  have h1 : ‖p.coeff 0‖ ≤ ‖c‖ ^ p.natDegree := by
    rwa [← div_eq_mul_inv, div_le_one hcpos] at hmem
  have hdeg : p.natDegree ≤ n := by
    have := Polynomial.natDegree_le_of_dvd hd (Matrix.charpoly_monic M).ne_zero
    simpa [Matrix.charpoly_natDegree_eq_dim] using this
  calc ‖p.coeff 0‖ ≤ ‖c‖ ^ p.natDegree := h1
    _ ≤ R ^ p.natDegree := pow_le_pow_left₀ (norm_nonneg _) hcR _
    _ ≤ R ^ n := pow_le_pow_right₀ hR hdeg
