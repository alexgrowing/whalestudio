import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubMulRight
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section utinv

open Formalism.FourierDecayAlt.P.Dx2.SplitM

def eQ (j : ℕ) : ((G.UT j → ℂ) × (Fin j → ℂ)) ≃ᵐ (G.UT (j + 1) → ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : G.UT j ⊕ Fin j => ℂ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : G.UT (j + 1) => ℂ) eL)

theorem eQ_eq (j : ℕ) (p : (G.UT j → ℂ) × (Fin j → ℂ)) : eQ j p = combineUpperTriangularCoords p := rfl

theorem eQ_mp (j : ℕ) : MeasurePreserving (eQ j) volume volume := combined_coordinates_measure_preserving

theorem upper_eQ_cc {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) (a b : Fin j) :
    G.upper (eQ j p) a.castSucc b.castSucc = G.upper p.1 a b := by
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, Fin.castSucc_inj,
    Fin.castSucc_lt_castSucc_iff]
  congr 1
  split_ifs with h
  · have e : (⟨(a.castSucc, b.castSucc), Fin.castSucc_lt_castSucc_iff.mpr h⟩ : G.UT (j + 1)) = eL (Sum.inl ⟨(a, b), h⟩) := rfl
    rw [e, eQ_eq, combined_coordinates_left]
  · rfl

theorem upper_eQ_cl {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) (a : Fin j) :
    G.upper (eQ j p) a.castSucc (Fin.last j) = p.2 a := by
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  rw [if_neg (Fin.castSucc_ne_last a), dif_pos (Fin.castSucc_lt_last a), zero_add]
  have e : (⟨(a.castSucc, Fin.last j), Fin.castSucc_lt_last a⟩ : G.UT (j + 1)) = eL (Sum.inr a) := rfl
  rw [e, eQ_eq, combineUpperTriangular_inr]

theorem upper_eQ_lc {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) (b : Fin j) :
    G.upper (eQ j p) (Fin.last j) b.castSucc = 0 := by
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  rw [if_neg (Ne.symm (Fin.castSucc_ne_last b)), dif_neg (not_lt.2 (Fin.castSucc_lt_last b).le), zero_add]

theorem upper_eQ_ll {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) :
    G.upper (eQ j p) (Fin.last j) (Fin.last j) = 1 := by
  simp [G.upper, G.strictUpper]

def utInv (m : ℕ) (u : G.UT m → ℂ) : G.UT m → ℂ := StabilizerDisintegration.utc (G.upper u)⁻¹

theorem upper_inv_mem {m : ℕ} (u : G.UT m → ℂ) : (G.upper u)⁻¹ ∈ C2.UTset m :=
  Formalism.FourierDecayAlt.P.C2x2.ut_inv (StabilizerDisintegration.UC.upper_mem u)

theorem upper_utInv {m : ℕ} (u : G.UT m → ℂ) : G.upper (utInv m u) = (G.upper u)⁻¹ :=
  StabilizerDisintegration.UC.upper_utc (upper_inv_mem u)

theorem utInv_eQ {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) :
    utInv (j + 1) (eQ j p) = eQ j (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2)) := by
  have hu1 : IsUnit (G.upper p.1).det := by rw [StabilizerDisintegration.UC.det_UT (StabilizerDisintegration.UC.upper_mem _)]; exact isUnit_one
  have hprod : G.upper (eQ j (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2))) * G.upper (eQ j p) = 1 := by
    ext a b
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
    · simp [upper_eQ_lc, upper_eQ_ll]
    · simp [upper_eQ_lc, upper_eQ_ll, Matrix.one_apply]
      exact (Fin.castSucc_ne_last _).symm
    · simp only [upper_eQ_cc, upper_eQ_cl, upper_eQ_ll, mul_one, Matrix.one_apply, Fin.castSucc_ne_last, if_false,
        upper_utInv]
      have : ∑ x : Fin j, (G.upper p.1)⁻¹ a x * p.2 x = ((G.upper p.1)⁻¹ *ᵥ p.2) a := rfl
      rw [this]; simp
    · simp only [upper_eQ_cc, upper_eQ_lc, mul_zero, add_zero, upper_utInv, Matrix.one_apply,
        Fin.castSucc_inj]
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hu1, Matrix.one_apply]
  have hinv : (G.upper (eQ j p))⁻¹ = G.upper (eQ j (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2))) :=
    Matrix.inv_eq_left_inv hprod
  unfold utInv
  rw [hinv, StabilizerDisintegration.UC.utc_upper]
  rfl

theorem utInv_mp : ∀ m : ℕ, MeasurePreserving (utInv m) volume volume
  | 0 => by
    have : IsEmpty (G.UT 0) := ⟨fun ⟨⟨a, _⟩, _⟩ => a.elim0⟩
    have : utInv 0 = id := funext fun u => funext fun q => isEmptyElim q
    rw [this]; exact MeasurePreserving.id _
  | j + 1 => by
    have ih := utInv_mp j
    have hA : ∀ u1 : G.UT j → ℂ, ‖(-(G.upper u1)⁻¹).det‖ = 1 := by
      intro u1
      have hu := upper_inv_mem u1
      rw [Matrix.det_neg, StabilizerDisintegration.UC.det_UT hu, mul_one]
      simp
    have hg : MeasurePreserving (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2)))
        volume volume := by
      rw [Measure.volume_eq_prod]
      refine MeasurePreserving.skew_product (f := utInv j) (g := fun u1 v => -((G.upper u1)⁻¹ *ᵥ v)) ih ?_ ?_
      · have hc : Continuous (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => -((G.upper p.1)⁻¹ *ᵥ p.2)) := by
          have h1 : Continuous (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => (G.upper p.1)⁻¹) := by
            have : (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => (G.upper p.1)⁻¹) =
                fun p => (G.upper p.1).adjugate := by
              funext p
              rw [Matrix.inv_def, StabilizerDisintegration.UC.det_UT (StabilizerDisintegration.UC.upper_mem _)]; simp
            rw [this]
            exact (StabilizerDisintegration.UC.cont_upper.comp continuous_fst).matrix_adjugate
          exact (h1.matrix_mulVec continuous_snd).neg
        exact hc.measurable
      · refine Filter.Eventually.of_forall fun u1 => ?_
        have h := mp_vec (-(G.upper u1)⁻¹) (hA u1)
        have e : (fun v : Fin j → ℂ => -((G.upper u1)⁻¹ *ᵥ v)) = fun v => (-(G.upper u1)⁻¹) *ᵥ v := by
          funext v; rw [Matrix.neg_mulVec]
        rw [e]; exact h.map_eq
    have e : utInv (j + 1) = eQ j ∘ (fun p : (G.UT j → ℂ) × (Fin j → ℂ) =>
        (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2))) ∘ (eQ j).symm := by
      funext u
      obtain ⟨p, rfl⟩ := (eQ j).surjective u
      simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
      exact utInv_eQ p
    rw [e]
    exact (eQ_mp j).comp (hg.comp (eQ_mp j).symm)

end utinv

section rad

variable {k j ρ : ℕ}

theorem strictUpper_neg {d : ℕ} (v : G.UT d → ℂ) : G.strictUpper (-v) = -G.strictUpper v := by
  ext i j
  simp only [G.strictUpper, Matrix.of_apply, Matrix.neg_apply, Pi.neg_apply]
  split_ifs <;> simp

theorem skewOf_neg (q : (G.UT j → ℂ) × (Fin j → ℝ)) : U.skewOf (-q) = -U.skewOf q := by
  simp only [U.skewOf, Prod.fst_neg, Prod.snd_neg, strictUpper_neg, Matrix.conjTranspose_neg]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.diagonal_apply, Pi.neg_apply]
  split_ifs <;> push_cast <;> ring

theorem rn_mul_neg (x : U.RC k j ρ) : U.Rn k j ρ x * U.Rn k j ρ (-x) = 1 := by
  unfold U.Rn
  rw [Ux3.block3_mul, ← Ux3.block3_one]
  have hc : (Matrix.of (-x).1 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) = -Matrix.of x.1 := rfl
  have hs : U.skewOf (-x).2 = -U.skewOf x.2 := skewOf_neg x.2
  rw [hc, hs]
  congr 1 <;> simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_add_cancel, add_neg_cancel]

  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg, Matrix.mul_assoc]
  module

theorem rn_inv (x : U.RC k j ρ) : (U.Rn k j ρ x)⁻¹ = U.Rn k j ρ (-x) := Matrix.inv_eq_right_inv (rn_mul_neg x)

theorem negRC_mp : MeasurePreserving (fun x : U.RC k j ρ => -x) (U.muRC k j ρ) (U.muRC k j ρ) := by
  have h1 : MeasurePreserving (fun c : Fin (2 * ρ + k + 1) → Fin j → ℂ => -c) volume volume :=
    volume_preserving_pi (fun _ => volume_preserving_pi (fun _ => Measure.measurePreserving_neg volume))
  have h2 : MeasurePreserving (fun c : G.UT j → ℂ => -c) volume volume :=
    volume_preserving_pi (fun _ => Measure.measurePreserving_neg volume)
  have h3 : MeasurePreserving (fun c : Fin j → ℝ => -c) volume volume :=
    volume_preserving_pi (fun _ => Measure.measurePreserving_neg volume)
  unfold U.muRC
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  exact h1.prod (h2.prod h3)

theorem muP_one : U.muP k j ρ (1 : Matrix (Fin j) (Fin j) ℂ) = 1 := by
  unfold U.muP
  rw [Matrix.conjTranspose_one, inv_one, Matrix.mul_one, Ux3.wMat_mul_self, Ux3.block3_one]

theorem leviElement_inv (q : Matrix (Fin j) (Fin j) ℂ) (hq : IsUnit q.det) : (U.muP k j ρ q)⁻¹ = U.muP k j ρ q⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Dx2.Split.leviElement_mul, Matrix.mul_nonsing_inv _ hq, muP_one]

end rad

section split

variable {k : ℕ}

theorem embG_one {j ρ : ℕ} : U.embG k j ρ (1 : B.Mat k ρ) = 1 := by
  unfold U.embG; exact Ux3.block3_one

def psiF (k j : ℕ) (p : U.RC k j 0 × (G.UT j → ℂ)) : Mt k (j + 0) := Matrix.of.symm (U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2))

def psiR (k j : ℕ) (p : U.RC k j 0 × (G.UT j → ℂ)) : Mt k (j + 0) := Matrix.of.symm (U.muP k j 0 (G.upper p.2) * U.Rn k j 0 p.1)

theorem psiF_cont (j : ℕ) : Continuous (psiF k j) := by
  unfold psiF
  exact ((Dx2.SplitF.rn_cont (k := k) j 0).comp continuous_fst).matrix_mul
    ((Dx2.SplitF.mup_cont (k := k) j 0).comp continuous_snd)

theorem psiR_cont (j : ℕ) : Continuous (psiR k j) := by
  unfold psiR
  exact ((Dx2.SplitF.mup_cont (k := k) j 0).comp continuous_snd).matrix_mul
    ((Dx2.SplitF.rn_cont (k := k) j 0).comp continuous_fst)

theorem psiF_meas (j : ℕ) : Measurable (psiF k j) := by
  exact (psiF_cont j).measurable

theorem psiR_meas (j : ℕ) : Measurable (psiR k j) := by
  exact (psiR_cont j).measurable

theorem muN_fwd (j : ℕ) : D.muN k (j + 0) = ((U.muRC k j 0).prod (volume : Measure (G.UT j → ℂ))).map (psiF k j) := by
  have hs := Dx2.SplitF.split_all (k := k) j 0
  have h0 : D.muN k 0 = Measure.dirac (Matrix.of.symm (1 : B.Mat k 0)) := rfl
  have : SigmaFinite (U.muRC k j 0) := Dx2.SplitF.sf_RC j 0
  rw [hs, h0, Measure.prod_dirac]
  have hm : Measurable (fun u : G.UT j → ℂ => (u, Matrix.of.symm (1 : B.Mat k 0))) :=
    measurable_id.prodMk measurable_const
  conv_lhs => rw [← Measure.map_id (μ := U.muRC k j 0)]
  rw [Measure.map_prod_map _ _ measurable_id hm,
    Measure.map_map (Dx2.SplitF.psi_meas j 0) (measurable_id.prodMap hm)]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map, id, Dx2.SplitF.Psi, psiF]
  rw [show Matrix.of (Matrix.of.symm (1 : B.Mat k 0)) = (1 : B.Mat k 0) from rfl, embG_one, Matrix.mul_one]

theorem muN_rev (j : ℕ) : D.muN k (j + 0) = ((U.muRC k j 0).prod (volume : Measure (G.UT j → ℂ))).map (psiR k j) := by
  have : SigmaFinite (U.muRC k j 0) := Dx2.SplitF.sf_RC j 0
  have hinv := Formalism.FourierDecayAlt.P.haar_measure_inversion k (j + 0) (Nset k (j + 0)) (D.muN k (j + 0))
    (Formalism.FourierDecayAlt.P.unipotent_radical_closed k (j + 0)) (Dx2.MN.haar (k := k) (j + 0))
  rw [← hinv, muN_fwd j, Measure.map_map (Formalism.FourierDecayAlt.P.TwoByOneBlock.invM_meas) (psiF_meas j)]
  have hmp : MeasurePreserving (fun p : U.RC k j 0 × (G.UT j → ℂ) => (-p.1, utInv j p.2))
      ((U.muRC k j 0).prod volume) ((U.muRC k j 0).prod volume) :=
    negRC_mp.prod (utInv_mp j)
  have e : (B2.invM ∘ psiF k j) = psiR k j ∘ (fun p : U.RC k j 0 × (G.UT j → ℂ) => (-p.1, utInv j p.2)) := by
    funext p
    have hu : IsUnit (G.upper p.2).det := by rw [StabilizerDisintegration.UC.det_UT (StabilizerDisintegration.UC.upper_mem _)]; exact isUnit_one
    show Matrix.of.symm ((Matrix.of (Matrix.of.symm (U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2))))⁻¹) =
      Matrix.of.symm (U.muP k j 0 (G.upper (utInv j p.2)) * U.Rn k j 0 (-p.1))
    rw [show Matrix.of (Matrix.of.symm (U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2))) =
      U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2) from rfl, Matrix.mul_inv_rev, rn_inv, leviElement_inv _ hu, upper_utInv]
  rw [e, ← Measure.map_map (psiR_meas j) hmp.measurable, hmp.map_eq]

end split

end Formalism.FourierDecayAlt.P.PBM
