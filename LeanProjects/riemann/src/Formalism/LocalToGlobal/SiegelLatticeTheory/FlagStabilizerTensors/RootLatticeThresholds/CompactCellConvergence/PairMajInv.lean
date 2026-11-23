import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.EtEquiv
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.KeyBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProper5OfSteps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.DoubleCosetDecomposition
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.C2

variable {k r : ℕ}

theorem pairMaj_inv (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ ∈ UH (Hpk k r)) (b : ℝ) {x : PairSp k r} (hx : Good L x)
    {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ RStab k r γ) :
    Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b (stabAct γ a x) = Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b x := by
  have hg : IsUnit γ.det := PIQnLT.isUnit_det_of_UH γ hγ
  have ha' : IsUnit a.det := PIQnLT.isUnit_det_of_UH a ha.1.1
  have key : (Matrix.of x.1.1)⁻¹ * (a * Matrix.of x.1.2)⁻¹ * γ * (γ⁻¹ * a * γ * Matrix.of x.2.2) * Matrix.of x.2.1
      = (Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * γ * Matrix.of x.2.2 * Matrix.of x.2.1 := by
    rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hg,
      Matrix.nonsing_inv_mul_cancel_left _ _ ha']
  unfold Formalism.MainNotions.S.Pv.AmpDD.pairMaj stabAct
  exact congrArg (fun M => Formalism.FourierDecayAlt.B.gN M ^ (-b)) key

theorem pair_bound (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hstd : Std k r L.z L.z') (hpos : PosPt k r L.z L.z' γ) (hmono : IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ))
    (T : ℝ) (hT : 1 ≤ T) (b : ℝ) (hb : 0 ≤ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : PairSp k r, Good L x → x.1.2 ∈ ET (k := k) (r := r) L.z L.z' γ T →
      Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b x ≤
        K * (Formalism.FourierDecayAlt.B.gN (Matrix.of x.1.2 * Matrix.of x.1.1) ^ (-(b / (2 * (5 * (r + 1) ^ 2 : ℕ)))) *
          Formalism.FourierDecayAlt.B.gN (Matrix.of x.2.2 * Matrix.of x.2.1) ^ (-(b / (2 * (5 * (r + 1) ^ 2 : ℕ))))) := by
  classical
  have hγ : γ ∈ UH (Hpk k r) := hpos.1
  have hγu : IsUnit γ.det := PIQnLT.isUnit_det_of_UH γ hγ
  obtain ⟨C, hC1, -⟩ := PI.PolynomialProperness.polyProper5 k r L.z L.z' γ hstd hpos hmono
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have gnn : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, 0 ≤ Formalism.FourierDecayAlt.B.gN g :=
    fun g => (PI.PolynomialProperness.gnFacts k r).1 g
  have gmul : ∀ g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Formalism.FourierDecayAlt.B.gN (g * h) ≤ Formalism.FourierDecayAlt.B.gN g * Formalism.FourierDecayAlt.B.gN h :=
    fun g h => PI.PolynomialProperness.GN.gN_mul_le g h
  have c1nn : 0 ≤ Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ :=
    mul_nonneg (mul_nonneg (gnn _) hT0) (gnn _)
  have hKc : (0 : ℝ) < max ((T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) * C) 1 :=
    lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max ((T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) * C) 1) ^
      (b / ((5 * (r + 1) ^ 2 : ℕ) : ℝ)), Real.rpow_pos_of_pos hKc _, ?_⟩
  intro x hx hET
  obtain ⟨y, ⟨⟨hyN, hyN'⟩, hyT⟩, hyS⟩ := hET
  obtain ⟨hP12, hP22, hP11, hP21⟩ := hx
  have hyU : Matrix.of y ∈ UH (Hpk k r) := hyN.1
  have hyu : IsUnit (Matrix.of y).det := PIQnLT.isUnit_det_of_UH _ hyU
  rw [uh_inv_eq hyU, ← sg_eq L.z L.z' hstd.2.1 γ] at hyS
  have hσ : (Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1 ∈ Sg k r L.z L.z' γ := by
    obtain ⟨n0, hn0, v, hv, hv', h, hh, he⟩ := hyS
    exact ⟨n0, hn0, v, hv, hv', h * Matrix.of x.1.1, Formalism.QuantumDeterminants.WeylGroupFacts.uw_mul hh hP11,
      by rw [he]; simp only [Matrix.mul_assoc]⟩
  have hmN : γ⁻¹ * Matrix.of y * γ ∈ Nset k r := hyN'
  have hP21u : IsUnit (Matrix.of x.2.1).det := PIQnLT.isUnit_det_of_UH _ hP21.1
  have hs : (γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1 ∈ Sset k r L.z' := by
    have hmn : (γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 ∈ Nset k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hmN) hP22
    have hw := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hP21
    refine ⟨Matrix.of x.2.1, hP21,
      (Matrix.of x.2.1)⁻¹ * ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2) * Matrix.of x.2.1, ?_, ?_⟩
    · rw [Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff]
      refine ⟨Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hw.1 hmn.1) hP21.1, ?_⟩
      exact Formalism.QuantumDeterminants.WeylGroupFacts.conj_col (Formalism.QuantumDeterminants.WeylGroupFacts.uw_block hw) (Formalism.QuantumDeterminants.WeylGroupFacts.uw_block hP21)
        (Matrix.nonsing_inv_mul _ hP21u) ((Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff _).1 hmn).2
    · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hP21u]
  have hb1 := hC1 _ hσ _ hs
  have hmu : IsUnit (γ⁻¹ * Matrix.of y * γ).det := PIQnLT.isUnit_det_of_UH _ hmN.1
  have hMeq : (Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * γ * Matrix.of x.2.2 * Matrix.of x.2.1 =
      ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1)⁻¹ * γ *
        ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1) := by
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hγu,
      Matrix.nonsing_inv_nonsing_inv _ hyu, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hγu, Matrix.mul_nonsing_inv_cancel_left _ _ hyu]
  have hX : Formalism.FourierDecayAlt.B.gN (Matrix.of x.1.2 * Matrix.of x.1.1) ≤
      T * Formalism.FourierDecayAlt.B.gN ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1) := by
    have e : Matrix.of x.1.2 * Matrix.of x.1.1 =
        Matrix.of y * ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1) := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hyu]
    rw [e]
    exact le_trans (gmul _ _) (mul_le_mul_of_nonneg_right hyT (gnn _))
  have hY : Formalism.FourierDecayAlt.B.gN (Matrix.of x.2.2 * Matrix.of x.2.1) ≤
      (Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ) *
        Formalism.FourierDecayAlt.B.gN ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1) := by
    have e : Matrix.of x.2.2 * Matrix.of x.2.1 =
        (γ⁻¹ * Matrix.of y * γ) * ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1) := by
      rw [Matrix.mul_assoc ((γ⁻¹ * Matrix.of y * γ)⁻¹), ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hmu, Matrix.one_mul]
    have hm : Formalism.FourierDecayAlt.B.gN (γ⁻¹ * Matrix.of y * γ) ≤ Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ := by
      calc Formalism.FourierDecayAlt.B.gN (γ⁻¹ * Matrix.of y * γ)
          ≤ Formalism.FourierDecayAlt.B.gN (γ⁻¹ * Matrix.of y) * Formalism.FourierDecayAlt.B.gN γ := gmul _ _
        _ ≤ (Formalism.FourierDecayAlt.B.gN γ⁻¹ * Formalism.FourierDecayAlt.B.gN (Matrix.of y)) * Formalism.FourierDecayAlt.B.gN γ :=
          mul_le_mul_of_nonneg_right (gmul _ _) (gnn _)
        _ ≤ Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyT (gnn _)) (gnn _)
    rw [e]
    exact le_trans (gmul _ _) (mul_le_mul_of_nonneg_right hm (gnn _))
  have hUH12 : Matrix.of x.1.2 * Matrix.of x.1.1 ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hP12.1 hP11.1
  have hUH22 : Matrix.of x.2.2 * Matrix.of x.2.1 ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hP22.1 hP21.1
  have hUHM : (Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * γ * Matrix.of x.2.2 * Matrix.of x.2.1 ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hP11.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hP12.1)) hγ)
      hP22.1) hP21.1
  have hsum : Formalism.FourierDecayAlt.B.gN (Matrix.of x.1.2 * Matrix.of x.1.1) + Formalism.FourierDecayAlt.B.gN (Matrix.of x.2.2 * Matrix.of x.2.1) ≤
      max ((T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) * C) 1 *
        Formalism.FourierDecayAlt.B.gN ((Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * γ * Matrix.of x.2.2 * Matrix.of x.2.1) ^
          (5 * (r + 1) ^ 2) := by
    rw [hMeq]
    have hpow : 0 ≤ Formalism.FourierDecayAlt.B.gN (((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1)⁻¹ * γ *
        ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1)) ^ (5 * (r + 1) ^ 2) :=
      pow_nonneg (gnn _) _
    have hσn := gnn ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1)
    have hsn := gnn ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1)
    calc _ ≤ T * Formalism.FourierDecayAlt.B.gN ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1) +
          (Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ) *
            Formalism.FourierDecayAlt.B.gN ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1) := add_le_add hX hY
      _ ≤ (T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) *
          (Formalism.FourierDecayAlt.B.gN ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1) +
            Formalism.FourierDecayAlt.B.gN ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1)) := by
          nlinarith [mul_nonneg c1nn hσn, mul_nonneg hT0 hsn]
      _ ≤ (T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) * (C * _) :=
          mul_le_mul_of_nonneg_left hb1 (by linarith)
      _ = ((T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) * C) * _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
  have hE : 0 < 5 * (r + 1) ^ 2 := by positivity
  have key := key_bound (PI.PolynomialProperness.GN.gN_ge_one hUH12) (PI.PolynomialProperness.GN.gN_ge_one hUH22)
    (PI.PolynomialProperness.GN.gN_ge_one hUHM) hKc hE hb hsum
  unfold Formalism.MainNotions.S.Pv.AmpDD.pairMaj
  exact key

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
