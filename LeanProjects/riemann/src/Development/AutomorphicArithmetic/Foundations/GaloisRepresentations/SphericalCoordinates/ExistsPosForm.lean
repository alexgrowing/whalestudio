import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegDefOfHermitianMatrixPositiveIndexEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHaarMeasureScaling
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_pos_form {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (h1 : sigPosH hA = 1) :
    ∃ w : Fin n → ℂ, 0 < (star w ⬝ᵥ (A *ᵥ w)).re := by
  have hne : Nonempty {i : Fin n // 0 < hA.eigenvalues i} := by
    apply Fintype.card_pos_iff.1
    unfold sigPosH at h1
    omega
  obtain ⟨i, hi⟩ := hne
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1, ?_⟩
  rw [GlobalTheory.SignatureOneForms.form_re_eq_sum hA]
  have hU : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ
      ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, Unitary.coe_star_mul_self, Matrix.one_mulVec]
  rw [hU, Finset.sum_eq_single i]
  · simpa using hi
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem UpperTheory.Gal.W2.sigB_of :
    UpperTheory.Gal.W2.SigB := by
  intro p _ G B v
  obtain ⟨hH, hdet, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v B.β B.sym B.trivR
  have hZi : (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hiZ : ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ x y : Fin G.n → ℂ, hv (GlobalTheory.LKCx.herm G v B.β) x y =
      star ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ y) ⬝ᵥ
        (G.gram v *ᵥ ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x)) := by
    intro x y
    unfold hv
    rw [hZ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have hinj : ∀ x : Fin G.n → ℂ, x ≠ 0 → (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x ≠ 0 := by
    intro x hx h0
    apply hx
    have h2 := congrArg (fun w => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) h0
    simpa [Matrix.mulVec_mulVec, hiZ] using h2
  refine ⟨hH, fun h1 => ⟨?_, ?_⟩, fun h1 => ?_⟩
  · obtain ⟨w, hw⟩ := exists_pos_form (G.gram_herm v) h1
    refine ⟨((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w, ?_⟩
    rw [key, Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]
    exact hw
  · intro z x hz hx hxz
    rw [key] at hz hxz ⊢
    exact GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one (G.gram v) (G.gram_herm v) (G.gram_det v) h1 _ _ hz hxz (hinj x hx)
  · have h0 : sigPosH (G.gram_herm v) = 0 := by
      rcases G.sig v with h | h
      · exact absurd h.1 h1
      · exact h.1
    intro x hx
    rw [key]
    exact GlobalTheory.herm_negDef_of_sigPosH_eq_zero (G.gram v) (G.gram_herm v) (G.gram_det v) h0 _ (hinj x hx)
