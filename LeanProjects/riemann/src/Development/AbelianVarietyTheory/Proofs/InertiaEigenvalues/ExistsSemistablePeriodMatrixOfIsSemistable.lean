import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorProductBasisCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPeriodMatrixOfFinrankStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_periodMatrix_of_isSst : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → ∃ Q : GL n (Bst P), ∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P)) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q := by
  intro l _ P AI T n _ _ K V _ _ b ρ h
  obtain ⟨hdom, hreg, hu⟩ := stRegular l P AI ⟨T⟩
  obtain ⟨e, -, -, he⟩ := GlobalTheory.T.tensorProduct_basis_coordinates ℚ_[l] (Bst P) V n b
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hK0 : ∀ c : ↥(K0 K), algebraMap ↥(K0 K) (Bst P) c = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) ⟨c, c.2.2⟩ :=
    fun c => rfl
  have hst : ∀ (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Bst P),
      stRep P ρ g y = TensorProduct.map (ρ g) (actSt P (g : GQ l)).toLinearMap y := fun g y => rfl
  refine GlobalTheory.T.exists_periodMatrix_of_finrank_alt ℚ_[l] ↥(K0 K) (Bst P) ↥(GK K)
    (fun g => (actSt P (g : GQ l) : Bst P →+* Bst P)) n (fun g => LinearMap.toMatrix b b (ρ g))
    (fun g => ?_) (fun g c => ?_) (fun x x' hx hh => ?_) (fun x hx hh => hu K x hx hh)
    ((Dst P ρ).map e.toLinearMap) (fun x => ?_) ?_
  · have h1 : LinearMap.toMatrix b b (ρ g) * LinearMap.toMatrix b b (ρ g⁻¹) = 1 := by
      rw [← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel, map_one, LinearMap.toMatrix_one]
    exact (Matrix.isUnit_det_of_right_inverse h1).ne_zero
  · rw [hK0]
    exact actSt_algebraMap P g _ _ (mem_GK.mp g.2 _ c.2.1)
  · obtain ⟨c, hc, hc'⟩ := hreg K x x' hx hh
    exact ⟨⟨c, hc, c.2⟩, by rw [hK0]; exact hc'⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    have h1 : e y ∈ (Dst P ρ).map e.toLinearMap ↔ y ∈ Dst P ρ := by
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    rw [h1, mem_Dst]
    refine forall_congr' fun g => ?_
    rw [hst, ← e.injective.eq_iff, he]
    rfl
  · rw [LinearEquiv.finrank_map_eq, h, finrank_eq_card_basis b]

end GlobalTheory.PMon
