import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobDenseOffFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem fin_places (S : Finset ℕ) : {v : HeightOneSpectrum (𝓞 ℚ) | normV v ∈ S}.Finite := by
  have h : {I : Ideal (𝓞 ℚ) | Ideal.absNorm I ≤ S.sup id}.Finite := Ideal.finite_setOf_absNorm_le _
  refine (h.preimage (f := fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset fun v hv => ?_
  have : normV v ≤ S.sup id := Finset.le_sup (f := id) hv
  simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this

private theorem scal_iff {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) :
    (∃ t : K, A = t • 1) ↔ A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨A 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]

private theorem det_of_quad {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) (a c : K)
    (hA : ¬ ∃ t : K, A = t • 1) (h : A ^ 2 - a • A + c • (1 : Matrix (Fin 2) (Fin 2) K) = 0) : A.det = c := by
  rw [scal_iff] at hA
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have ht : A 0 0 + A 1 1 - a = 0 := by
    by_contra hne
    apply hA
    refine ⟨?_, ?_, ?_⟩
    · exact (mul_eq_zero.1 (by linear_combination h01 : A 0 1 * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne
    · exact (mul_eq_zero.1 (by linear_combination h10 : A 1 0 * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne
    · exact sub_eq_zero.1 ((mul_eq_zero.1
        (by linear_combination h00 - h11 : (A 0 0 - A 1 1) * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne)
  rw [Matrix.det_fin_two]
  linear_combination A 0 0 * ht - h00

theorem UpperTheory.V.Z.Kato.Nb.sDetChar :
    UpperTheory.V.Z.Kato.Nb.SDetChar := by
  intro l _ Ω _ _ _ ρ χ hρ hχ ⟨s₀, hs₀⟩ S hF
  have hc : Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := Units.continuous_val.comp hρ
  have hχ' : Continuous fun s => (χ s : Qbar l) := Units.continuous_val.comp hχ
  have he : ∀ i j, Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) i j := fun i j => hc.matrix_elem i j
  have hU : IsOpen {s | ¬ ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1} := by
    simp only [scal_iff]
    exact (((isClosed_eq (he 0 1) continuous_const).inter
      ((isClosed_eq (he 1 0) continuous_const).inter (isClosed_eq (he 0 0) (he 1 1))))).isOpen_compl
  have hC : IsClosed {s | (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s} := isClosed_eq hc.matrix_det hχ'
  have hD := GlobalTheory.frob_dense_off_finite ℚ Ω _ (fin_places S)
  have key : ∀ s, (¬ ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s := by
    intro s hs
    refine hC.closure_subset_iff.2 ?_ (hD.open_subset_closure_inter hU hs)
    rintro σ ⟨hσ, v, hv, B, hB, hf⟩
    obtain ⟨a, ha⟩ := hF v B σ hv hB hf
    exact det_of_quad _ a _ hσ ha
  intro s
  by_cases hs : ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1
  · obtain ⟨t, ht⟩ := hs
    have h0 := key s₀ (fun ⟨u, hu⟩ => hs₀ u hu)
    have h1 := key (s * s₀) (by
      rintro ⟨u, hu⟩
      rw [map_mul, Units.val_mul, ht, smul_mul_assoc, one_mul] at hu
      have t0 : t ≠ 0 := by
        rintro rfl
        exact (ρ s).ne_zero (by simpa using ht)
      exact hs₀ (t⁻¹ * u) (by rw [mul_smul, ← hu, smul_smul, inv_mul_cancel₀ t0, one_smul]))
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, h0] at h1
    exact mul_right_cancel₀ (χ s₀).ne_zero h1
  · exact key s hs
