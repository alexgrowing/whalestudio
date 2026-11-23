import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicCharacterFactorPrimitiveOnIdempotentSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralIffSelfDualTraceCharacterSplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToEAfOrientedHermitianFormEqTraceFrames
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatPairing

set_option synthInstance.maxHeartbeats 400000 in

theorem trace_mul_int {D : D7} {a b : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D)) (B : Matrix (Fin b) (Fin a) (EAf D))
    (hA : IsIntM A) (hB : IsIntM B) :
    Matrix.trace (A * B) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hB j i)

set_option synthInstance.maxHeartbeats 400000 in

theorem resS_trace_mul {D : D7} (PP : Pl D.host.E) {a b : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D))
    (B : Matrix (Fin b) (Fin a) (EAf D)) (hA : IsIntM A) (hB : IsIntM B)
    (h : Matrix.trace (A * B) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F PP ⟨Matrix.trace (A * B), h⟩ = Matrix.trace (redM PP A * redM PP B) := by
  have h1 : (⟨Matrix.trace (A * B), h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ∑ i, ∑ j, (⟨A i j, hA i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨B j i, hB j i⟩ := by
    apply Subtype.ext
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum,
      MulMemClass.coe_mul]
  rw [h1]
  simp only [map_sum, map_mul, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [redM, dif_pos (hA i j), dif_pos (hB j i)]

theorem inv_isPrimitive {R : Type} [CommRing R] (χ : AddChar R ℂ) (h : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  intro a ha h1
  apply h (neg_ne_zero.mpr ha)
  ext x
  have := DFunLike.congr_fun h1 x
  simpa [AddChar.mulShift_apply, AddChar.inv_apply] using this

theorem exists_primitive {E : Type} [Field E] [NumberField E] (PP : Pl E) :
    ∃ χ : AddChar (kP PP) ℂ, χ.IsPrimitive := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  haveI : Finite (𝓞 E ⧸ PP.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  letI : Field (𝓞 E ⧸ PP.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 E ⧸ PP.asIdeal) := Fintype.ofFinite _
  exact ⟨_, AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (𝓞 E ⧸ PP.asIdeal)⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem pairing_eq_prod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ x : WO S T, IsHalf (cA D e) x → IsIntM (frMapAdj S T βS βT x) → ∀ u : WO S T, IsHalf e u → IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → ψ (symplO S T x u) = ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (redM PP.1 (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) * redM PP.1 (frMapAdj S T βS βT x))) := by
  intro D ψ S T ΛS ΛT βS βT hψ hS hT hβS hβT Q e he hQ ϖ hϖ hϖQ
  by_cases h0 : S.rank = 0 ∨ T.rank = 0
  · refine ⟨fun PP => (exists_primitive PP).choose, fun PP _ => (exists_primitive PP).choose_spec, ?_⟩
    intro x _ _ u _ _
    have hz : hO S T x u = 0 := by
      unfold hO
      rcases h0 with h0 | h0
      · haveI : IsEmpty (Fin S.rank) := by rw [h0]; infer_instance
        exact Finset.sum_of_isEmpty _
      · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
        exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => Finset.sum_of_isEmpty _
    rw [symplO, hz, mul_zero, map_zero, AddChar.map_zero_eq_one]
    symm
    refine Finset.prod_eq_one fun PP _ => ?_
    have : ∀ (A : Matrix (Fin T.rank) (Fin S.rank) (kP PP.1)) (B : Matrix (Fin S.rank) (Fin T.rank) (kP PP.1)),
        Matrix.trace (A * B) = 0 := by
      intro A B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      rcases h0 with h0 | h0
      · haveI : IsEmpty (Fin S.rank) := by rw [h0]; infer_instance
        exact Finset.sum_eq_zero fun _ _ => Finset.sum_of_isEmpty _
      · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
        exact Finset.sum_of_isEmpty _
    rw [this, AddChar.map_zero_eq_one]
  · rw [not_or] at h0
    obtain ⟨χ, hχ, hform⟩ := GlobalTheory.T.adelicCharacter_factor_primitive_on_idempotentSum D ψ Q e he ϖ hϖ hϖQ
      (GlobalTheory.T.integral_iff_selfDual_traceCharacter_splitPlaces D ψ S T ΛS ΛT βS βT hψ hS hT hβS hβT (Nat.pos_of_ne_zero h0.1) (Nat.pos_of_ne_zero h0.2) Q e he hQ)
    refine ⟨fun PP => (χ PP)⁻¹, fun PP hPP => inv_isPrimitive _ (hχ PP hPP), ?_⟩
    intro x _ hx u hu hux
    have heu : e • u = u := by
      funext i j
      exact hu i j
    have hsm : (u.map fun w => incA D (ϖ : D.host.E) * w : WO S T) = incA D (ϖ : D.host.E) • u := rfl
    have hZ : e * (-hO S T u x) = -hO S T u x := by
      rw [mul_neg, ← GlobalTheory.PlaceModel.hO_smul_left, heu]
    have htr : toEAf D (incA D (ϖ : D.host.E) * (-hO S T u x)) =
        -Matrix.trace (frMapAdj S T βS βT x * frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) := by
      rw [mul_neg, map_neg, ← GlobalTheory.PlaceModel.hO_smul_left, ← hsm, GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames S T βS βT]
    have hint := trace_mul_int _ _ hx hux
    have hint' : toEAf D (incA D (ϖ : D.host.E) * (-hO S T u x)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [htr]; exact Subring.neg_mem _ hint
    have hs : symplO S T x u =
        Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (-hO S T u x)) := by
      rw [GlobalTheory.PlaceModel.symplO_skew S T u x, symplO, mul_neg, map_neg]
    rw [hs, hform _ hZ hint']
    refine Finset.prod_congr rfl fun PP _ => ?_
    have h2 : (⟨_, hint'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = -⟨_, hint⟩ := Subtype.ext htr
    rw [h2, map_neg, resS_trace_mul PP.1 _ _ hx hux, AddChar.inv_apply, Matrix.trace_mul_comm]

end GlobalTheory.FlatPairing
