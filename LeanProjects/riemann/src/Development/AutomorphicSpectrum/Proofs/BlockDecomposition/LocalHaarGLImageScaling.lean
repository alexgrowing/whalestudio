import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatAtIsCO
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.NuFin

variable {R : Type} [CommRing R] {n : ℕ}

theorem image_eq (A Ai A' B Dm K3 K4 C : Matrix (Fin n) (Fin n) R) (O : AddSubgroup (Fin n → R))
    (hAiA : Ai * A = 1) (hC : A * C = B * A') (hD3 : Dm * K3 = -1) (hD4 : Dm * K4 = -C)
    (hset : {x | ∃ y ∈ O, ∃ y' ∈ O, x = K3 *ᵥ y + K4 *ᵥ y'} = (O : Set (Fin n → R))) :
    {x | ∃ y ∈ O.map (Matrix.mulVecLin A).toAddMonoidHom, ∃ y' ∈ O.map (Matrix.mulVecLin A').toAddMonoidHom,
        x = y + B *ᵥ y'} =
      (fun x => (A * Dm * Ai) *ᵥ x) '' (O.map (Matrix.mulVecLin A).toAddMonoidHom : Set (Fin n → R)) := by
  have hgA : (A * Dm * Ai) * A = A * Dm := by rw [mul_assoc, hAiA, mul_one]
  have hid : ∀ u u', (A * Dm * Ai) *ᵥ (A *ᵥ (-(K3 *ᵥ u + K4 *ᵥ u'))) = A *ᵥ u + B *ᵥ (A' *ᵥ u') := by
    intro u u'
    have e3 : (A * Dm) * K3 = -A := by rw [mul_assoc, hD3, mul_neg, mul_one]
    have e4 : (A * Dm) * K4 = -(B * A') := by rw [mul_assoc, hD4, mul_neg, hC]
    rw [Matrix.mulVec_mulVec, hgA, Matrix.mulVec_neg, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, e3, e4, Matrix.mulVec_mulVec, Matrix.neg_mulVec, Matrix.neg_mulVec]
    simp only [neg_add, neg_neg]
  have hK : ∀ u ∈ O, ∀ u' ∈ O, -(K3 *ᵥ u + K4 *ᵥ u') ∈ O := by
    intro u hu u' hu'
    have h1 : K3 *ᵥ u + K4 *ᵥ u' ∈ (O : Set (Fin n → R)) := by
      rw [← hset]
      exact ⟨u, hu, u', hu', rfl⟩
    exact neg_mem h1
  ext x
  constructor
  · rintro ⟨y, hy, y', hy', rfl⟩
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hy
    obtain ⟨u', hu', rfl⟩ := AddSubgroup.mem_map.1 hy'
    exact ⟨A *ᵥ (-(K3 *ᵥ u + K4 *ᵥ u')), AddSubgroup.mem_map.2 ⟨_, hK u hu u' hu', rfl⟩, hid u u'⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hy
    have h1 : -w ∈ (O : Set (Fin n → R)) := neg_mem hw
    rw [← hset] at h1
    obtain ⟨u, hu, u', hu', e⟩ := h1
    have hw' : w = -(K3 *ᵥ u + K4 *ᵥ u') := by rw [← e, neg_neg]
    refine ⟨A *ᵥ u, AddSubgroup.mem_map.2 ⟨u, hu, rfl⟩, A' *ᵥ u', AddSubgroup.mem_map.2 ⟨u', hu', rfl⟩, ?_⟩
    change (A * Dm * Ai) *ᵥ (A *ᵥ w) = _
    rw [hw']
    exact hid u u'

theorem map_neg_matrix {S T : Type} [Ring S] [Ring T] (f : S →+* T) (M : Matrix (Fin n) (Fin n) S) :
    (-M).map f = -(M.map f) := by
  ext i j
  simp

set_option maxHeartbeats 1600000 in

theorem local_haar_GL_image_eq_absValue_det : ∀ (D : D7) (n : ℕ) (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₃ k₄ : Mx D n n) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam.IsAddHaarMeasure → (∀ (g : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) (S : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam ((fun x => g.1.mulVec x) '' S) = (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S) → PositivityTheory.SiegelWeilFormula.Gen.IsCO (latAt a.1 v) → d.1 * k₃ = -1 → d.1 * k₄ = -(pull a b).1 → {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) → PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (latAt a.1 v) (latAt (adj (a⁻¹).1) v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) = (absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ) := by
  intro D n a d b k₃ k₄ v lam hlam hscale hCO hk3 hk4 hset
  have matV_neg : ∀ M : Matrix (Fin n) (Fin n) (AE D), PositivityTheory.SiegelWeilFormula.Gen.matV v (-M) = -PositivityTheory.SiegelWeilFormula.Gen.matV v M := fun M =>
    map_neg_matrix (Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV D.host.F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA D.host.F))
      (AlgHom.id D.host.F D.host.E)).toRingHom M
  let gv : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) :=
    Matrix.GeneralLinearGroup.map (compFin D.host.F D.host.E v) (a * d * a⁻¹)
  have hgv : gv.1 = PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v d.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v (a⁻¹).1 := by
    have key : ∀ x y z : Matrix (Fin n) (Fin n) (AE D), PositivityTheory.SiegelWeilFormula.Gen.matV v (x * y * z) = PositivityTheory.SiegelWeilFormula.Gen.matV v x * PositivityTheory.SiegelWeilFormula.Gen.matV v y * PositivityTheory.SiegelWeilFormula.Gen.matV v z := by
      intro x y z
      rw [LatCO.matV_mul, LatCO.matV_mul]
    exact key a.1 d.1 (a⁻¹).1
  have hinv : a.1 * (a⁻¹).1 = 1 := by simp
  have hinv' : (a⁻¹).1 * a.1 = 1 := by simp
  have hAiA : PositivityTheory.SiegelWeilFormula.Gen.matV v (a⁻¹).1 * PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 = 1 := by
    rw [← LatCO.matV_mul, hinv', LatCO.matV_one]
  have hC : PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v (pull a b).1 = PositivityTheory.SiegelWeilFormula.Gen.matV v b.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v (adj (a⁻¹).1) := by
    have e : a.1 * (pull a b).1 = b.1 * adj (a⁻¹).1 := by
      change a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) = _
      rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
    rw [← LatCO.matV_mul, ← LatCO.matV_mul, e]
  have hD3 : PositivityTheory.SiegelWeilFormula.Gen.matV v d.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v k₃ = -1 := by
    rw [← LatCO.matV_mul, hk3, matV_neg, LatCO.matV_one]
  have hD4 : PositivityTheory.SiegelWeilFormula.Gen.matV v d.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v k₄ = -PositivityTheory.SiegelWeilFormula.Gen.matV v (pull a b).1 := by
    rw [← LatCO.matV_mul, hk4, matV_neg]
  have hS := image_eq (PositivityTheory.SiegelWeilFormula.Gen.matV v a.1) (PositivityTheory.SiegelWeilFormula.Gen.matV v (a⁻¹).1) (PositivityTheory.SiegelWeilFormula.Gen.matV v (adj (a⁻¹).1)) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) (PositivityTheory.SiegelWeilFormula.Gen.matV v d.1)
    (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃) (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄) (PositivityTheory.SiegelWeilFormula.Gen.matV v (pull a b).1) (latLoc D.host.F (stdLattice D.host.E n) v).toAddSubgroup
    hAiA hC hD3 hD4 hset
  rw [← hgv] at hS
  have hdet : Matrix.GeneralLinearGroup.det gv = unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d) := by
    have h1 : Matrix.GeneralLinearGroup.det (a * d * a⁻¹) = Matrix.GeneralLinearGroup.det d := by
      rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det a), mul_inv_cancel_right]
    rw [← h1]
    exact Matrix.GeneralLinearGroup.map_det _ _
  have hm0 : lam (latAt a.1 v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) ≠ 0 :=
    (hCO.1.measure_pos lam ⟨0, zero_mem _⟩).ne'
  have hmT : lam (latAt a.1 v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) ≠ ⊤ :=
    hCO.2.measure_lt_top.ne
  have hval : lam {x | ∃ y ∈ latAt a.1 v, ∃ y' ∈ latAt (adj (a⁻¹).1) v, x = y + (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1).mulVec y'} =
      (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det gv) : ℝ≥0∞) * lam (latAt a.1 v : Set _) := by
    rw [← hscale gv]
    exact congrArg lam hS
  unfold PositivityTheory.SiegelWeilFormula.Gen.nu2
  rw [hval, hdet, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hm0 hmT, mul_one, ENNReal.coe_toReal]

end GlobalTheory.CompanionTheory.MM.NuFin
