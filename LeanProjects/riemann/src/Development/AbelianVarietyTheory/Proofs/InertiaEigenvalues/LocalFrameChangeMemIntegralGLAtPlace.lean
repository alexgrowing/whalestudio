import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.LocCore

theorem adj_det_integral {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, v (A i j) ≤ 1) :
    (∀ i j, v (A.adjugate i j) ≤ 1) ∧ v A.det ≤ 1 := by
  let A' : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨A i j, hA i j⟩
  have hA' : A'.map v.integer.subtype = A := by ext i j; rfl
  constructor
  · intro i j
    have h := RingHom.map_adjugate v.integer.subtype A'
    simp only [RingHom.mapMatrix_apply, hA'] at h
    rw [← h]
    exact (A'.adjugate i j).2
  · have h := RingHom.map_det v.integer.subtype A'
    simp only [RingHom.mapMatrix_apply, hA'] at h
    rw [← h]
    exact (A'.det).2

theorem solve_integral {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} (A B κ : Matrix (Fin n) (Fin n) K) (hAB : A * κ = B)
    (hA : ∀ i j, v (A i j) ≤ 1) (hB : ∀ i j, v (B i j) ≤ 1)
    (hdA : v A.det = 1) (hdB : v B.det = 1) :
    (∀ a b, v (κ a b) ≤ 1) ∧ v κ.det = 1 ∧
      ((∀ i j, v ((A - 1) i j) < 1) → (∀ i j, v ((B - 1) i j) < 1) →
        ∀ a b, v ((κ - 1) a b) < 1) := by
  obtain ⟨hadj, -⟩ := adj_det_integral v A hA
  have key : A.det • κ = A.adjugate * B := by
    rw [← hAB, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have key' : A.det • (κ - 1) = A.adjugate * (B - A) := by
    rw [smul_sub, key, Matrix.mul_sub, Matrix.adjugate_mul]
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    have h := congrFun (congrFun key a) b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
    have h2 := congrArg v h
    rw [map_mul, hdA, one_mul] at h2
    rw [h2]
    apply v.map_sum_le
    intro k _
    rw [map_mul]
    exact mul_le_one' (hadj a k) (hB k b)
  · have h := congrArg v (congrArg Matrix.det hAB)
    rw [Matrix.det_mul, map_mul, hdA, one_mul, hdB] at h
    exact h
  · intro hA1 hB1 a b
    have h := congrFun (congrFun key' a) b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
    have h2 := congrArg v h
    rw [map_mul, hdA, one_mul] at h2
    rw [h2]
    apply v.map_sum_lt one_ne_zero
    intro k _
    rw [map_mul]
    have hBA : (B - A) k b = (B - 1) k b - (A - 1) k b := by
      simp only [Matrix.sub_apply, sub_sub_sub_cancel_right]
    have hlt : v ((B - A) k b) < 1 := by
      rw [hBA]; exact lt_of_le_of_lt (v.map_sub _ _) (max_lt (hB1 k b) (hA1 k b))
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hadj a k)) hlt

end GlobalTheory.LocCore

namespace GlobalTheory.LocCore

noncomputable def topAt {D : D7} (P : Pl D.host.E) {m n : ℕ} (hmn : n ≤ m)
    (U : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) :
    Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion D.host.E P) :=
  fun i j => GlobalTheory.StdFrames.cpt P (U (Fin.castLE hmn i) j)

theorem topAt_facts {D : D7} (P : Pl D.host.E) {m n : ℕ} (hmn : n ≤ m)
    (U : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) (hU : IsIntM U)
    (hdU : IsUnit (topL n (redM P U)).det) :
    (∀ i j, Valued.v (topAt P hmn U i j) ≤ 1) ∧ Valued.v (topAt P hmn U).det = 1 ∧
      (topL n (redM P U) = 1 → ∀ i j, Valued.v ((topAt P hmn U - 1) i j) < 1) := by
  let S := Formalism.L2.Herm.intAf (↥D.host.F) D.host.E
  let A' : Matrix (Fin n) (Fin n) S := fun i j => ⟨U (Fin.castLE hmn i) j, hU _ _⟩
  let φ : S →+* HeightOneSpectrum.adicCompletion D.host.E P :=
    (GlobalTheory.StdFrames.cpt P).comp S.subtype
  have hA : A'.map φ = topAt P hmn U := by ext i j; rfl
  have hred : A'.map (resS (↥D.host.F) P) = topL n (redM P U) := by
    ext i j
    simp only [Matrix.map_apply, topL, redM]
    rw [dif_pos ⟨lt_of_lt_of_le i.2 hmn, j.2⟩, dif_pos (hU _ _)]
    rfl
  have hint : ∀ i j, Valued.v (topAt P hmn U i j) ≤ 1 := by
    intro i j
    have := (GlobalTheory.StdFrames.mem_OA_iff (U (Fin.castLE hmn i) j)).1 (hU _ _) P
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 this
  have hφ : ∀ s : S, resS (↥D.host.F) P s = 0 ↔ Valued.v (φ s) < 1 :=
    fun s => GlobalTheory.AdIsom.resS_eq_zero_iff_cpt P s
  refine ⟨hint, ?_, ?_⟩
  · apply le_antisymm ((adj_det_integral Valued.v _ hint).2)
    have h1 : resS (↥D.host.F) P A'.det ≠ 0 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hred]; exact hdU.ne_zero
    rw [Ne, hφ, not_lt, RingHom.map_det, RingHom.mapMatrix_apply, hA] at h1
    exact h1
  · intro h1 i j
    have hm : (resS (↥D.host.F) P).mapMatrix (A' - 1) = 0 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hred, h1, sub_self]
    have h2 : resS (↥D.host.F) P ((A' - 1) i j) = 0 := by
      have := congrFun (congrFun hm i) j
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using this
    have hm' : φ.mapMatrix (A' - 1) = topAt P hmn U - 1 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hA]
    have h3 : (topAt P hmn U - 1) i j = φ ((A' - 1) i j) := by
      have e := congrFun (congrFun hm' i) j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply] at e
      exact e.symm
    rw [h3]
    exact (hφ _).1 h2

end GlobalTheory.LocCore

namespace GlobalTheory.LocCore

theorem kappa_integral_at : ∀ (D : D7) (P : Pl D.host.E) (m n : ℕ) (U Y : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) (κ : Matrix (Fin n) (Fin n) (Formalism.IndefR.Datum.EAf D)) (c : Formalism.IndefR.Datum.EAf D), GlobalTheory.StdFrames.cpt P c = 1 → (HMul.hMul U κ : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) = c • Y + (1 - c) • U → IsIntM U → IsIntM Y → IsUnit (topL n (redM P U)).det → IsUnit (topL n (redM P Y)).det → (∀ a b, GlobalTheory.StdFrames.cpt P (κ a b) ∈ P.adicCompletionIntegers D.host.E) ∧ Valued.v (GlobalTheory.StdFrames.cpt P κ.det) = 1 ∧ (topL n (redM P U) = 1 → topL n (redM P Y) = 1 → ∀ a b, Valued.v (GlobalTheory.StdFrames.cpt P ((κ - 1) a b)) < 1) := by
  intro D P m n U Y κ c hc hUk hU hY hdU hdY
  by_cases hmn : n ≤ m
  swap
  · exfalso
    push_neg at hmn
    have h0 : (topL n (redM P U)).det = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero ⟨m, hmn⟩
      intro j
      simp [topL]
    rw [h0] at hdU
    exact not_isUnit_zero hdU
  set cp := GlobalTheory.StdFrames.cpt (D := D) P with hcp
  obtain ⟨hAi, hAd, hA1⟩ := topAt_facts P hmn U hU hdU
  obtain ⟨hBi, hBd, hB1⟩ := topAt_facts P hmn Y hY hdY
  have hAB : topAt P hmn U * κ.map cp = topAt P hmn Y := by
    refine Matrix.ext fun i j => ?_
    have h := congrArg cp (congrFun (congrFun hUk (Fin.castLE hmn i)) j)
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
      map_mul, map_add, map_sub, map_one, hc, sub_self, zero_mul, add_zero, one_mul] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply]
    exact h
  obtain ⟨k1, k2, k3⟩ := solve_integral Valued.v _ _ _ hAB hAi hBi hAd hBd
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (k1 a b)
  · rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact k2
  · intro h1 h2 a b
    have e : cp.mapMatrix (κ - 1) = κ.map cp - 1 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply]
    have e2 := congrFun (congrFun e a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at e2
    rw [e2]
    exact k3 (hA1 h1) (hB1 h2) a b

end GlobalTheory.LocCore
