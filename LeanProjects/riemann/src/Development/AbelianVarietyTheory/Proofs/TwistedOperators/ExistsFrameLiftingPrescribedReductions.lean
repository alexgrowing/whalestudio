import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead.CyclotomicLifting

variable {D : D7}

theorem adj_mem {R : Type} [CommRing R] (T : Subring R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, A i j ∈ T) (i j : Fin n) : A.adjugate i j ∈ T := by
  let A' : Matrix (Fin n) (Fin n) T := fun a b => ⟨A a b, h a b⟩
  have e : T.subtype.mapMatrix A' = A := by ext a b; rfl
  rw [← e, ← RingHom.map_adjugate]
  exact (A'.adjugate i j).2

theorem loc_inv (Q : Pl D.host.E) {n : ℕ} (A : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E))
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hd : Valued.v A.det = 1) :
    ∃ A' : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E), (∀ i j, Valued.v (A' i j) ≤ 1) ∧ A * A' = 1 := by
  have h0 : A.det ≠ 0 := fun h => by rw [h, map_zero] at hd; exact zero_ne_one hd
  refine ⟨A⁻¹, fun i j => ?_, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 h0)⟩
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', map_mul, map_inv₀, hd, inv_one, one_mul]
  have := adj_mem (Q.adicCompletionIntegers D.host.E).toSubring A (fun a b => by
    change A a b ∈ Q.adicCompletionIntegers D.host.E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hA a b) i j
  change A.adjugate i j ∈ Q.adicCompletionIntegers D.host.E at this
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem glob {n : ℕ} (c c' : ∀ Q : Pl D.host.E, Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E))
    (hc : ∀ Q i j, Valued.v (c Q i j) ≤ 1) (hc' : ∀ Q i j, Valued.v (c' Q i j) ≤ 1) (h1 : ∀ Q, c Q * c' Q = 1) :
    ∃ C : GL (Fin n) (EAf D), (∀ i j, C.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      (∀ i j, (C⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      ∀ Q i j, GlobalTheory.StdFrames.cpt (D := D) Q ((C⁻¹).val i j) = c' Q i j := by
  choose z hzO hz using fun p : Fin n × Fin n => GlobalTheory.AdIsom.exists_of_cpt (D := D) (fun Q => c Q p.1 p.2) (fun Q => hc Q p.1 p.2)
  choose z' hzO' hz' using fun p : Fin n × Fin n => GlobalTheory.AdIsom.exists_of_cpt (D := D) (fun Q => c' Q p.1 p.2) (fun Q => hc' Q p.1 p.2)
  let Z : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => z (i, j)
  let Z' : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => z' (i, j)
  have hmul : Z * Z' = 1 := by
    ext i j
    refine GlobalTheory.StdFrames.cpt_ext fun Q => ?_
    have e := congrArg (fun M => M i j) (h1 Q)
    simp only [Matrix.mul_apply] at e ⊢
    rw [map_sum]
    simp only [map_mul, Z, Z', Matrix.of_apply, hz, hz']
    rw [e, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨⟨Z, Z', hmul, mul_eq_one_comm.1 hmul⟩, fun i j => hzO (i, j), fun i j => hzO' (i, j),
    fun Q i j => hz' (i, j) Q⟩

theorem col_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) (EAf D)) (w : Fin n → Fin n → EAf D) (i j : Fin n) :
    (A * colMat w) i j = Matrix.mulVec A (w j) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat]

theorem res_eq (Q : Pl D.host.E) (x : EAf D) (hmem : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (δ : Formalism.L2.Herm.intAf D.host.F D.host.E) (hcpt : GlobalTheory.StdFrames.cpt Q x = GlobalTheory.StdFrames.cpt Q (δ : EAf D)) :
    Formalism.L2.DIV.resS D.host.F Q ⟨x, hmem⟩ = Formalism.L2.DIV.resS D.host.F Q δ := by
  have e0 : (⟨x, hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨x - δ, sub_mem hmem δ.2⟩ + δ := Subtype.ext (by simp)
  have e1 := (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt (D := D) Q ⟨x - δ, sub_mem hmem δ.2⟩).2 (by
    change Valued.v (GlobalTheory.StdFrames.cpt Q (x - δ)) < 1
    rw [map_sub, hcpt, sub_self, map_zero]
    exact zero_lt_one)
  rw [e0, map_add, e1, zero_add]

end GlobalTheory.SeeConjRead.CyclotomicLifting

namespace GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
open GlobalTheory.SeeConjRead.CyclotomicLifting in

theorem exists_lift_redIs : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (S : Finset (Pl D.host.E)) (W : Pl D.host.E → Fin n → Fin n → EAf D), (∀ Q ∈ S, ∀ i j, ((β₀⁻¹).val * colMat (W Q)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ Q ∈ S, Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * colMat (W Q)).det) = 1) → ∃ β : GL (Fin n) (EAf D), GlobalTheory.NormSum.AdLattice.lat β = GlobalTheory.NormSum.AdLattice.lat β₀ ∧ ∀ Q ∈ S, RedIs β Q (W Q) := by
  intro D n β₀ S W hint hdet
  have hloc : ∀ Q : Pl D.host.E, ∃ c c' : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E),
      (∀ i j, Valued.v (c i j) ≤ 1) ∧ (∀ i j, Valued.v (c' i j) ≤ 1) ∧ c * c' = 1 ∧
      (Q ∈ S → c = ((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)) := by
    intro Q
    by_cases hQ : Q ∈ S
    · have hA : ∀ i j, Valued.v ((((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)) i j) ≤ 1 :=
        fun i j => (GlobalTheory.AdIsom.mem_OA _).1 (hint Q hQ i j) Q
      have hd : Valued.v (((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)).det = 1 := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact hdet Q hQ
      obtain ⟨A', hA', h1⟩ := loc_inv Q _ hA hd
      exact ⟨_, A', hA, hA', h1, fun _ => rfl⟩
    · refine ⟨1, 1, fun i j => ?_, fun i j => ?_, one_mul _, fun h => absurd h hQ⟩ <;>
      · rw [Matrix.one_apply]; split_ifs <;> simp
  choose c c' hc hc' h1 hS using hloc
  obtain ⟨C, hCi, hCi', hCc⟩ := glob c c' hc hc' h1
  refine ⟨β₀ * C, le_antisymm (GlobalTheory.NormSum.AdLattice.lat_le_of_int fun i j => ?_)
    (GlobalTheory.NormSum.AdLattice.lat_le_of_int fun i j => ?_), fun Q hQ i j => ?_⟩
  · rw [inv_mul_cancel_left]; exact hCi i j
  · rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]; exact hCi' i j
  have key : Matrix.mulVec ((β₀ * C)⁻¹).val (W Q j) i = ((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j := by
    rw [← Matrix.mul_assoc, col_apply, mul_inv_rev, Units.val_mul]
  rw [key]
  have hmem : ((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hCi' i k) (hint Q hQ k j)
  refine ⟨hmem, ?_⟩
  have hcpt : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    have e : c' Q * c Q = 1 := mul_eq_one_comm.1 (h1 Q)
    rw [hS Q hQ] at e
    rw [← e, Matrix.mul_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hCc]
    rfl
  split_ifs with hij
  · have h1' : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) =
        GlobalTheory.StdFrames.cpt Q ((1 : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [hcpt, Matrix.one_apply, if_pos hij]
      exact (map_one _).symm
    exact (res_eq Q _ hmem 1 h1').trans (map_one _)
  · have h0' : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) =
        GlobalTheory.StdFrames.cpt Q ((0 : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [hcpt, Matrix.one_apply, if_neg hij]
      exact (map_zero _).symm
    exact (res_eq Q _ hmem 0 h0').trans (map_zero _)

end GlobalTheory.SeeConjRead
