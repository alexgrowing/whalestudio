import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarDensityConjUnitaryHermitianGroupsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityLieAlgebraOfOmegaDensityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityUnitaryGroupProbabilityStatement

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FdegDens

theorem volUn_pos (j : ℕ) : 0 < volUn j := by
  unfold volUn
  refine Finset.prod_pos fun i _ => ?_
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  exact div_pos (pow_pos h2π _) (by exact_mod_cast Nat.factorial_pos i)

theorem exists_sort {n : ℕ} (ε : Fin n → Bool) : ∃ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin n), p + q = n ∧
    (∀ i, ε (e (Sum.inl i)) = true) ∧ ∀ j, ε (e (Sum.inr j)) = false := by
  classical
  let A := {i : Fin n // ε i = true}
  let B := {i : Fin n // ¬ε i = true}
  let e : Fin (Fintype.card A) ⊕ Fin (Fintype.card B) ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFin A).symm (Fintype.equivFin B).symm).trans
      (Equiv.sumCompl fun i => ε i = true)
  refine ⟨Fintype.card A, Fintype.card B, e, ?_, fun i => ?_, fun j => ?_⟩
  · simpa using Fintype.card_congr e
  · exact ((Fintype.equivFin A).symm i).2
  · show ε (((Fintype.equivFin B).symm j : B) : Fin n) = false
    simpa using ((Fintype.equivFin B).symm j).2

theorem measurable_reindex {n p q : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n) :
    Measurable fun g : Formalism.BasicNotions.UpqT p q =>
      (Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) : PI.MtM n) := by
  haveI : BorelSpace (Formalism.BasicNotions.UpqT p q) := ⟨rfl⟩
  have hmat : Continuous (Formalism.BasicNotions.UpqT.mat : Formalism.BasicNotions.UpqT p q → _) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous fun g : Formalism.BasicNotions.UpqT p q =>
      (Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) : PI.MtM n) :=
    hmat.matrix_reindex e e
  exact hc.measurable

theorem reindex_mem {n p q : ℕ} (ε : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) (g : Formalism.BasicNotions.UpqT p q) :
    Formalism.REAL.inUJ ε (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) := by
  obtain ⟨g0, hg0⟩ := g
  have hg : ((g0 : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * Formalism.UG.Jpq p q *
      (g0 : GL (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hg0
  show (Matrix.reindex e e ((g0 : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))ᴴ *
      Formalism.REAL.Jm ε * Matrix.reindex e e (g0 : GL (Fin p ⊕ Fin q) ℂ) = Formalism.REAL.Jm ε
  rw [GlobalTheory.OmegaFrobenius.jm_eq h1 h2, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

theorem hasDens_unique {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (Fin m → Fin m → ℂ)} {c c' : ℝ≥0∞}
    (h : HasDens S μ c) (h' : HasDens S μ c') : c = c' := by
  unfold HasDens at h h'
  exact tendsto_nhds_unique h h'

theorem hasDens_smul {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (Fin m → Fin m → ℂ)} {c : ℝ≥0∞}
    (h : HasDens S μ c) (t : NNReal) : HasDens S (t • μ) (t * c) := by
  unfold HasDens at h ⊢
  refine (ENNReal.Tendsto.const_mul h (Or.inr ENNReal.coe_ne_top) (a := (t : ℝ≥0∞))).congr fun ρ => ?_
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc]

theorem cd_dens {n p q : ℕ} (ε : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n) (hpq : p + q = n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) (cd : Formalism.BasicNotions.CDHaar) :
    PI.IsHaarOnM (UH (Formalism.REAL.Jm ε))
      ((cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) ∧
    HasDens (UH (Formalism.REAL.Jm ε))
      ((cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)))
      (ENNReal.ofReal (volUn n)⁻¹) := by
  subst hpq
  obtain ⟨c0, -, -, hc1, hc2⟩ := cd.trick p q
  have hK := GlobalTheory.T.hasDensityAtIdentityLieAlgebra_of_omegaDensity (p + q) (fun _ => true) (p + q) 0 (Equiv.sumEmpty _ _) (fun _ => rfl)
    (fun j => j.elim0) (cd.cd (p + q) 0) c0 (cd.haar _ _) hc2
  have hJ : Formalism.REAL.Jm (fun _ : Fin (p + q) => true) = 1 := by
    unfold Formalism.REAL.Jm
    simp
  rw [hJ] at hK
  have hprob : ((cd.cd (p + q) 0).map fun g => Matrix.of.symm (Matrix.reindex
      (Equiv.sumEmpty (Fin (p + q)) (Fin 0)) (Equiv.sumEmpty (Fin (p + q)) (Fin 0))
      (Formalism.BasicNotions.UpqT.mat g))) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_reindex _) MeasurableSet.univ, Set.preimage_univ]
    haveI := cd.prob (p + q)
    exact measure_univ
  have hc0 : c0 = ENNReal.ofReal (volUn (p + q))⁻¹ :=
    hasDens_unique hK.2 (GlobalTheory.T.hasDensityAtIdentity_unitaryGroup_probability (p + q) _ hK.1 hprob)
  have hM := GlobalTheory.T.hasDensityAtIdentityLieAlgebra_of_omegaDensity (p + q) ε p q e h1 h2 (cd.cd p q) c0 (cd.haar p q) hc1
  rw [hc0] at hM
  exact hM

theorem umat_emb {n : ℕ} (ε : Fin n → Bool) :
    MeasurableEmbedding fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM n) := by
  have h : Topology.IsClosedEmbedding (fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM n)) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  exact h.measurableEmbedding

theorem conj_emb {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    MeasurableEmbedding fun x : PI.MtM n => (Matrix.of.symm (P⁻¹ * Matrix.of x * P) : PI.MtM n) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hm : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
      Measurable fun x : PI.MtM n => (Matrix.of.symm (A * Matrix.of x * B) : PI.MtM n) := by
    intro A B
    have hx : Continuous fun x : PI.MtM n => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ) := continuous_id
    have hc : Continuous fun x : PI.MtM n => (Matrix.of.symm (A * Matrix.of x * B) : PI.MtM n) :=
      (continuous_const.matrix_mul hx).matrix_mul continuous_const
    exact hc.measurable
  let φ : PI.MtM n ≃ PI.MtM n :=
    { toFun := fun x => Matrix.of.symm (P⁻¹ * Matrix.of x * P)
      invFun := fun y => Matrix.of.symm (P * Matrix.of y * P⁻¹)
      left_inv := fun x => by
        show Matrix.of.symm (P * (P⁻¹ * Matrix.of x * P) * P⁻¹) = x
        simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, ← Matrix.mul_assoc P P⁻¹,
          Matrix.mul_nonsing_inv_cancel_left _ _ hu]
      right_inv := fun y => by
        show Matrix.of.symm (P⁻¹ * (P * Matrix.of y * P⁻¹) * P) = y
        simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hu] }
  exact (MeasurableEquiv.mk φ (hm _ _) (hm _ _)).measurableEmbedding

theorem schur_of_dens : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (cd : Formalism.BasicNotions.CDHaar) (sc : NNReal) (P : Mat k r) (d c : ℝ) (μG : Measure (Mt k r)), (∀ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin (2 * r + k + 1)), (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A → ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) A = cd.cd p q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}) → IsCayley k r ε P → IsFdeg ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) d → 0 < c → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → SchurH μG σ (d / (c * volUn (2 * r + k + 1))) := by
  intro k r H _ _ _ σ ε cd sc P d c μG hcomp hP hF hc hμG hdG
  obtain ⟨p, q, e, hpq, h1, h2⟩ := exists_sort ε
  have hU := umat_emb ε
  have hC := conj_emb P hP.1

  have hν : ((sc : ℝ≥0∞) • Formalism.REAL.muG ε).map (fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM (2 * r + k + 1))) =
      (cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) := by
    ext B hB
    rw [Measure.map_apply hU.measurable hB, Measure.map_apply (measurable_reindex e) hB,
      hcomp p q e h1 h2 _ (hU.measurable hB)]
    congr 1
    ext g
    constructor
    · rintro ⟨a, ha, hag⟩
      show Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) ∈ B
      rw [← hag]
      exact ha
    · intro hg
      have hmem : Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g) ∈ Set.range
          (fun a : Formalism.REAL.UJ ε => ((a : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
            Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
        rw [(Formalism.REAL.isClosedEmbeddingMatrix _ ε).2]
        exact reindex_mem ε e h1 h2 g
      obtain ⟨a, ha⟩ := hmem
      refine ⟨a, ?_, ha⟩
      show Matrix.of.symm (umat a) ∈ B
      rw [show umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g) from ha]
      exact hg
  have hcd := cd_dens ε e hpq h1 h2 cd
  rw [← hν] at hcd
  have hHk := Formalism.QuantumDeterminants.hpkFacts k r
  have hD := GlobalTheory.T.haar_density_conj_unitaryHermitianGroups (2 * r + k + 1) (Formalism.QuantumDeterminants.Hpk k r) (Formalism.REAL.Jm ε) P hHk.1 hHk.2.1
    (Formalism.REAL.Jm_conjTranspose ε) (Formalism.REAL.Jm_mul_self ε) hP.1 hP.2 _ _ hcd.1 hcd.2
  obtain ⟨t, -, httop, hμt⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ _
    (GlobalTheory.AdDens.isMatGroup_UH _ hHk.2.1) hD.1).1 μG hμG
  have hdt : HasDens (GG k r) μG (t * ENNReal.ofReal (volUn (2 * r + k + 1))⁻¹) := by
    have h := hasDens_smul hD.2 t.toNNReal
    rwa [ENNReal.smul_def, ENNReal.coe_toNNReal httop.ne, ← hμt] at h
  have hV := volUn_pos (2 * r + k + 1)
  have htr : t.toReal = c * volUn (2 * r + k + 1) := by
    have h := congrArg ENNReal.toReal (hasDens_unique hdG hdt)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal (inv_nonneg.mpr hV.le)] at h
    rw [h, mul_assoc, inv_mul_cancel₀ hV.ne', mul_one]
  rw [Measure.map_map hC.measurable hU.measurable] at hμt
  have hemb := hC.comp hU
  obtain ⟨hd, hFd⟩ := hF
  refine ⟨div_pos hd (mul_pos hc hV), fun v w v' w' => ?_⟩
  obtain ⟨hI, hE⟩ := hFd v w v' w'
  rw [hμt]
  refine ⟨Integrable.smul_measure ?_ httop.ne, ?_⟩
  · rw [hemb.integrable_map_iff]
    exact hI
  rw [integral_smul_measure, hemb.integral_map]
  refine (congrArg (fun z : ℂ => t.toReal • z) hE).trans ?_
  rw [htr, Complex.real_smul]
  push_cast
  rw [div_div_eq_mul_div]
  ring

end GlobalTheory.FdegDens
