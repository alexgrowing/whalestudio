import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.IwasawaVal
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem ordInt_diag {K : Type} [Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA (show id j < id i from h), zero_mul]
    · rw [hB (show id i < id j from h), mul_zero]
  · simp

private theorem ordInt_conj {K : Type} [Field K] {n : ℕ} (b : GL (Fin n) K) {M : Matrix (Fin n) (Fin n) K}
    (hb : (b : Matrix (Fin n) (Fin n) K).BlockTriangular id) (hM : M.BlockTriangular id) :
    ((b : Matrix (Fin n) (Fin n) K) * M * ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).BlockTriangular id ∧
      ∀ i, ((b : Matrix (Fin n) (Fin n) K) * M * ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i = M i i := by
  have hi : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    letI := b.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨(hb.mul hM).mul hi, fun i => ?_⟩
  have h1 := ordInt_diag hb hi i
  rw [Units.mul_inv, Matrix.one_apply_eq] at h1
  rw [ordInt_diag (hb.mul hM) hi, ordInt_diag hb hM, mul_right_comm, ← h1, one_mul]

private def ordInt_V (l : ℕ) [Fact l.Prime] : ValuationSubring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : Qbar l)‖ ≤ 1; simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : Qbar l)‖ ≤ 1; simp
  neg_mem' := fun {a} ha => by show ‖-a‖ ≤ 1; rwa [norm_neg]
  mem_or_inv_mem' := fun a => by
    rcases le_total ‖a‖ 1 with h | h
    · exact Or.inl h
    · right
      show ‖a⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h

theorem UpperTheory.V.Th.Nm.ordInt :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (v : F.Vl) (ψ : Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (w : GL (Fin n) (Qbar l)) (Y : Matrix (Fin n) (Fin n) (Qbar l)), OrdAt F ρ v ψ z w Y → ∃ w' : GL (Fin n) (Qbar l), IntM (w' : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((w'⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ OrdAt F ρ v ψ z w' Y := by
  intro l _ n F ρ v ψ z w Y h
  obtain ⟨k, hk⟩ := UpperTheory.V.Pr.T.iwasawaVal (ordInt_V l) n (w : Matrix (Fin n) (Fin n) (Qbar l))
  let k' : GL (Fin n) (Qbar l) := GeneralLinearGroup.map (ordInt_V l).subtype k
  have hb : ((k' * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).BlockTriangular id := hk
  refine ⟨k'⁻¹, fun i j => ?_, fun i j => ?_, fun g => ?_⟩
  · have : k'⁻¹ = GeneralLinearGroup.map (ordInt_V l).subtype k⁻¹ := (map_inv _ _).symm
    rw [this]
    exact ((k⁻¹ : GL (Fin n) (ordInt_V l)) i j).2
  · rw [inv_inv]
    exact (k i j).2
  · obtain ⟨h1, h2, h3, h4⟩ := h g
    have e : ∀ M : Matrix (Fin n) (Fin n) (Qbar l),
        ((k'⁻¹⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * M * (k'⁻¹ : GL (Fin n) (Qbar l)) =
        ((k' * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
          (((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * M * (w : Matrix (Fin n) (Fin n) (Qbar l))) *
          (((k' * w)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
      intro M
      rw [inv_inv, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
      simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    have c1 := ordInt_conj (k' * w) hb
      (M := ((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * (ρ (F.φ v g) : Matrix (Fin n) (Fin n) (Qbar l)) *
        (w : Matrix (Fin n) (Fin n) (Qbar l))) (fun i j hij => h1 i j hij)
    have c2 := ordInt_conj (k' * w) hb (fun i j hij => h3 i j hij)
    rw [← e] at c1 c2
    refine ⟨fun i j hij => c1.1 hij, fun i => (c1.2 i).trans (h2 i), fun i j hij => c2.1 hij,
      fun hg i => (c2.2 i).trans (h4 hg i)⟩
