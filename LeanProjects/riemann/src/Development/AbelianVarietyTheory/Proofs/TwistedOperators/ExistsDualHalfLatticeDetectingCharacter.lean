import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToEAfOrientedHermitianFormEqTraceFramesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualElementStandardCharSplitPrimeStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.HalfDuality

variable {D : D7}

theorem exists_lift (t : Datum.EAf D) : ∃ Z : AE D, infPart D Z = 0 ∧ toEAf D Z = t :=
  ⟨GlobalTheory.LatticeStable.liftFin D ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm t),
   GlobalTheory.AdForm.infPart_liftFin _, GlobalTheory.AdForm.toEAf_liftFin t⟩

theorem trace_id (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) (k y : WO S T) :
    toEAf D (hO S T y k) = Matrix.trace (frMapAdj S T βS βT k * frMapO S T βS βT y) :=
  GlobalTheory.T.toEAf_orientedHermitianForm_eq_trace_frames S T βS βT k y

theorem local_dual (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (e₁ : AE D) (PP : Pl D.host.E)
    (he₁ : Formalism.L2.NTheta.IsIdemAt e₁ PP) :
    ∃ c : Datum.EAf D,
      (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 →
        toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧
      (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c →
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) :=
  GlobalTheory.T.exists_dualElement_standardChar_splitPrime ψ hψ e₁ PP he₁

theorem psi_trace_split (ψ : AddChar (AF D.host.F) ℂ) (a Z Z₁ : AE D) :
    ψ (Algebra.trace (AF D.host.F) (AE D) (a * Z)) =
      ψ (Algebra.trace (AF D.host.F) (AE D) (a * Z₁)) * ψ (Algebra.trace (AF D.host.F) (AE D) (a * (Z - Z₁))) := by
  rw [← AddChar.map_add_eq_mul, ← map_add, ← mul_add, add_sub_cancel Z₁ Z]

theorem redM_apply_of_mem (PP : Pl D.host.E) {b a : ℕ} (N : Matrix (Fin b) (Fin a) (Datum.EAf D)) (i : Fin b) (j : Fin a)
    (h : N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : redM PP N i j = resS D.host.F PP ⟨N i j, h⟩ := by
  simp only [redM]
  exact dif_pos h

set_option maxHeartbeats 800000 in

theorem local_dual_unit (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (e₁ : AE D) (PP : Pl D.host.E)
    (he₁ : Formalism.L2.NTheta.IsIdemAt e₁ PP) (u : Formalism.L2.Herm.intAf D.host.F D.host.E) (hu : resS D.host.F PP u ≠ 0) :
    ∃ c : Datum.EAf D,
      (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 →
        toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧
      (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c * u →
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) := by
  obtain ⟨c, h1, h2⟩ := local_dual ψ hψ e₁ PP he₁
  haveI := PP.isMaximal
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (I := PP.asIdeal) hu
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b
  have hra : resS D.host.F PP (oToS D.host.F D.host.E a) * resS D.host.F PP u = 1 := by
    rw [resS_oToS, ha, mul_comm, hb]
  refine ⟨c * ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Datum.EAf D),
    fun Z hZ r hr hZr => ?_, fun Z hZ hZu => ?_⟩
  · refine h1 Z hZ (oToS D.host.F D.host.E a * r) (by rw [map_mul, hr, mul_zero]) ?_
    rw [hZr, MulMemClass.coe_mul, mul_assoc]
  · obtain ⟨Z₁, hZ₁, hZ₁c⟩ := exists_lift (D := D) c
    have hr : resS D.host.F PP (oToS D.host.F D.host.E a * u - 1) = 0 := by
      rw [map_sub, map_mul, hra, map_one, sub_self]
    have h0 := h1 (Z - Z₁) (by rw [map_sub, hZ, hZ₁, sub_zero]) (oToS D.host.F D.host.E a * u - 1) hr (by
      rw [map_sub, hZu, hZ₁c, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, mul_sub, mul_one,
        mul_assoc])
    intro hc
    apply h2 Z₁ hZ₁ hZ₁c
    rw [psi_trace_split ψ _ Z Z₁, h0, mul_one] at hc
    exact hc

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_half_frMapO (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    (e : AE D) (hee : e * e = e) (z : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D))
    (hz : ∀ i j, toEAf D e * z i j = z i j) :
    ∃ y : WO S T, IsHalf e y ∧ (∀ i j, infPart D (y i j) = 0) ∧ frMapO S T βS βT y = z := by
  choose L hL0 hL using fun t : Datum.EAf D => exists_lift (D := D) t
  let Y : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D) := HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val
  refine ⟨Matrix.of fun i j => e * L (Y i j), fun i j => ?_, fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply, ← mul_assoc, hee]
  · simp only [Matrix.of_apply, map_mul, hL0, mul_zero]
  · have hz' : toEAf D e • z = z := Matrix.ext fun i j => hz i j
    have h3 : toEAf D e • Y = Y := by
      show toEAf D e • HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val = HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz']
    have hY : (Matrix.of fun i j => e * L (Y i j) : WO S T).map (toEAf D) = Y := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, map_mul, hL]
      exact congrFun (congrFun h3 i) j
    unfold frMapO
    rw [hY]
    have e1 : HMul.hMul (HMul.hMul (βT⁻¹).val Y) βS.val =
        HMul.hMul (HMul.hMul (HMul.hMul ((βT⁻¹).val) βT.val) z) (HMul.hMul (βS⁻¹).val βS.val) := by
      simp only [Y, Matrix.mul_assoc]
    rw [e1, Units.inv_mul, Units.inv_mul, Matrix.one_mul, Matrix.mul_one]

theorem trace_mul_single {m n : ℕ} (M : Matrix (Fin m) (Fin n) (Datum.EAf D)) (b : Fin n) (a : Fin m) (t0 : Datum.EAf D) :
    Matrix.trace (M * Matrix.single b a t0) = M a b * t0 := by
  rw [Matrix.trace, Finset.sum_eq_single a]
  · simp [Matrix.mul_apply, Matrix.single_apply]
  · intro j _ hj
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ a) h

end GlobalTheory.HalfDuality

set_option maxHeartbeats 1600000 in
theorem GlobalTheory.HalfDuality.exists_dual_half : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) →
  (∃ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) ≠ 0) →
  ∃ y : WO (Vc D i) (Wc D i), IsHalf (cA D (cA D e)) y ∧
    (∀ k : WO (Vc D i) (Wc D i), IsHalf (cA D e) k → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) → (∀ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) = 0) →
      R.ψ (symplO (Vc D i) (Wc D i) k y) = 1) ∧
    R.ψ (symplO (Vc D i) (Wc D i) x y) ≠ 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io hL e he x hx hint hex
  obtain ⟨PP, hPP, hred⟩ := hex
  have hψ : IsStdChar D R.ψ (-1) := hL.2.2.2.2.2.1.std
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  obtain ⟨⟨es, hes, -⟩, -⟩ := he
  obtain ⟨a, b, hab⟩ : ∃ a b, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) a b ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hred (Matrix.ext hn)
  have hu : resS D.host.F PP ⟨_, hint a b⟩ ≠ 0 := by
    rw [← GlobalTheory.HalfDuality.redM_apply_of_mem]
    exact hab
  obtain ⟨c₀, h1, h2⟩ := GlobalTheory.HalfDuality.local_dual_unit R.ψ hψ (es PP) PP (hes PP hPP) _ hu
  obtain ⟨y, hyh, hy0, hyz⟩ := GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) e hee
    (Matrix.single b a (toEAf D e * c₀)) (fun i' j' => by
      rw [Matrix.single_apply]
      split_ifs
      · rw [← mul_assoc, ← map_mul, hee]
      · rw [mul_zero])
  have hinf : ∀ k, infPart D (hO (Vc D i) (Wc D i) y k) = 0 := fun k => by
    simp only [hO, map_sum, map_mul, hy0, mul_zero, Finset.sum_const_zero]
  have hfin : ∀ k, IsHalf (cA D e) k → toEAf D (hO (Vc D i) (Wc D i) y k) =
      c₀ * frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k a b := fun k hk => by
    rw [GlobalTheory.HalfDuality.trace_id _ _ (R.βV i) (R.βW i), hyz, GlobalTheory.HalfDuality.trace_mul_single, mul_comm (toEAf D e) c₀, mul_left_comm,
      mul_comm _ (toEAf D e), GlobalTheory.AdjVecLocal.frMapAdj_half _ _ _ _ hk]
  have hs : ∀ k, R.ψ (symplO (Vc D i) (Wc D i) k y) =
      (R.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * hO (Vc D i) (Wc D i) y k)))⁻¹ := fun k => by
    rw [GlobalTheory.OrientedHeis.symplO_skew y k, AddChar.map_neg_eq_inv]
    rfl
  refine ⟨y, by rw [Formalism.L2.Theta.cA_cA]; exact hyh, fun k hk hki hkr => ?_, ?_⟩
  · rw [hs, h1 _ (hinf k) ⟨_, hki a b⟩ (by rw [← GlobalTheory.HalfDuality.redM_apply_of_mem]; exact congrFun (congrFun (hkr PP hPP) a) b) (hfin k hk), inv_one]
  · rw [hs]
    exact fun h => h2 _ (hinf x) (hfin x hx) (inv_eq_one.1 h)
