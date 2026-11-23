import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.ExGModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsHermitianConjugationOfUnitaryTau
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLinearEquivSpOfIsUnitDetBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsHermitianFormOfUnitaryRotationBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SigLEqOfHermSemilinearEqStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HermitianDatumUniqueUpToScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemilinearCoordsEqMulVecStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsStarFixedRotationBasisOfCharpoly

open Matrix

namespace UpperTheory.V.Z.Sym.Glob

open Loc

private theorem unitary_form' {K : Type} [Field K] {Δ : K} (g : U3 Δ) (v w : Fin 3 → Lsq K Δ) :
    ∑ i, ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v) i * star (((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ w) i) =
      ∑ i, v i * star (w i) := by
  have hu : (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ))ᴴ * (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = 1 := by
    have := g.2
    rw [Matrix.mem_unitaryGroup_iff'] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have e1 : ∀ a b : Fin 3 → Lsq K Δ, ∑ i, a i * star (b i) = star b ⬝ᵥ a := by
    intro a b
    simp [dotProduct, mul_comm]
  rw [e1, e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]

end UpperTheory.V.Z.Sym.Glob

private theorem map_star_mul_divisor {R : Type} [CommRing R] [StarRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    (A * A.map star).map star = A.map star * A := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.mul_apply, star_sum, star_mul', star_star]

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc in
theorem UpperTheory.V.Z.Sym.Glob.classG :
    UpperTheory.V.Z.Sym.Glob.ClassG := by
  unfold ClassG
  intro K _ _ Δ τ d m hΔ hD δ hδ
  have hreg := hD.reg
  have hnorm := hD.d_norm
  obtain ⟨B, hBB, hNB, hBw⟩ := UpperTheory.exists_hermitian_conjugation_of_unitary_tau K Δ τ hreg d hnorm δ hδ _ rfl
  have hchar := hδ
  rw [HasTau.eq_1] at hchar
  obtain ⟨e, v, hBe, hBv, hNe, hNv, hdet⟩ := UpperTheory.exists_star_fixed_rotation_basis_of_charpoly K Δ τ hΔ hreg B _ hBB hNB hchar
  set N : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) with hN
  have hδe : (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star e = e := (hBw e hBe).1 hNe
  have hδv : (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star v = d.re • v + d.im • N *ᵥ v := (hBw v hBv).2 hNv
  obtain ⟨c, m', hm'u, hm's, hform⟩ := UpperTheory.exists_hermitian_form_of_unitary_rotation_basis K Δ τ hreg N (δ * theta Δ δ).property e v hNe hNv hdet
  obtain ⟨P, hP⟩ := UpperTheory.exists_linearEquiv_sp_of_isUnit_det_basis K Δ τ e v (N *ᵥ v) hdet
  have hform' : ∀ x y : Sp Δ τ, herm (c : K) m' x y = ∑ i, P x i * star (P y i) := by
    intro x y
    rw [hform, hP, hP]
  have h1 : N = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star := by
    rw [hN]
    rfl
  have hA : (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * N.map star = N * δ := by
    rw [h1, map_star_mul_divisor, Matrix.mul_assoc]
  have hsemi : ∀ x, P (semi d x) = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (P x) := by
    intro x
    rw [hP, hP]
    exact UpperTheory.semilinear_coords_eq_mulVec_star K Δ τ d δ N e v hA hδe hδv hNv x
  have hinv : ∀ x y, herm (c : K) m' (semi d x) (semi d y) = star (herm (c : K) m' x y) := by
    intro x y
    rw [hform', hform', hsemi, hsemi, unitary_form']
    simp [star_sum, mul_comm]
  have hsig := UpperTheory.sigL_eq_of_herm_semilinear_eq_star K Δ τ (c : K) d m' hreg hinv
  have hD' : IsDat (c : K) d m' := ⟨hreg, c.ne_zero, hnorm, hm'u, hm's, hsig⟩
  obtain ⟨t, ht⟩ := UpperTheory.hermitian_datum_unique_up_to_scalar K Δ τ 1 (c : K) d m m' hD hD'
  obtain ⟨δ', ι, hM⟩ := exG_models hD' P hform'
  refine ⟨c, t, ι, P, ?_⟩
  rw [← ht]
  exact ⟨hform', hsemi, hM.tor⟩
