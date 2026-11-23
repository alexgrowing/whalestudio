import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastRest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySignsHaarIsMulRightInvariant

noncomputable section

open MeasureTheory MvPolynomial GlobalTheory.OpTrace
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.PsCo.Pc3.RangeSh

variable {n : ℕ}

def evK (ε : Fin n → Bool) : Poly n →ₗ[ℂ] (KG ε → ℂ) where
  toFun P k := ev (toMK k) P
  map_add' P Q := by funext k; simp
  map_smul' c P := by funext k; simp [ev, smul_eval]

def polyK (ε : Fin n → Bool) (d : ℕ) : Submodule ℂ (KG ε → ℂ) :=
  (restrictTotalDegree _ ℂ d).map (evK ε)

instance (ε : Fin n → Bool) (d : ℕ) : FiniteDimensional ℂ (polyK ε d) := by
  unfold polyK; infer_instance

theorem mem_polyK {ε : Fin n → Bool} {d : ℕ} {F : KG ε → ℂ} :
    F ∈ polyK ε d ↔ ∃ P : Poly n, P.totalDegree ≤ d ∧ ∀ k, F k = ev (toMK k) P := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, (mem_restrictTotalDegree _ _ _).1 hP, fun _ => rfl⟩
  · rintro ⟨P, hP, h⟩
    refine Submodule.mem_map.2 ⟨P, (mem_restrictTotalDegree _ _ _).2 hP, ?_⟩
    funext k
    rw [h k]
    rfl

theorem ev_conjTranspose (P : Poly n) :
    ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧ ∀ A : Mat n, ev A.conjTranspose P = ev A Q := by
  refine ⟨rename (Sum.elim (fun x => Sum.inr x.swap) (fun x => Sum.inl x.swap)) P, totalDegree_rename_le _ _,
    fun A => ?_⟩
  rw [ev, ev, eval_rename]
  congr 2
  funext v
  rcases v with x | x <;> simp

theorem conj_ev (P : Poly n) :
    ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧ ∀ A : Mat n, conj (ev A P) = ev A Q := by
  refine ⟨rename Sum.swap (map (starRingEnd ℂ) P), (totalDegree_rename_le _ _).trans ?_, fun A => ?_⟩
  · exact Finset.sup_mono (support_map_subset _ _)
  · induction P using MvPolynomial.induction_on with
    | C a => simp [ev]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p v hp =>
      simp only [map_mul, hp]
      rcases v with x | x <;> simp [ev]

theorem ev_mul (a b : Mat n) (P : Poly n) :
    ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧ ∀ g : Mat n, ev (a * g * b) P = ev g Q :=
  GlobalTheory.PolyEntryMul.main n a b P

theorem toMK_inv {ε : Fin n → Bool} (k : KG ε) : toM ((k : UJ ε)⁻¹) = (toMK k).conjTranspose := by
  have h1 : toMK k * star (toMK k) = 1 := Unitary.mul_star_self_of_mem k.2.1
  exact Units.inv_eq_of_mul_eq_one_right h1

theorem rM_inv (ε : Fin n → Bool) (k k' : KG ε) (g : UJ ε) :
    rM ε (toM ((k : UJ ε) * g * (k' : UJ ε))) = rM ε (toM g) :=
  (GlobalTheory.offDiagBlockNorm_cont_inv n ε).2 k k' g

theorem shape_cc {ε : Fin n → Bool} {d : ℕ} {φ : Mat n → ℂ} (hφ : φ ∈ ShapeM ε d) :
    Continuous (fun g : UJ ε => φ (toM g)) ∧ HasCompactSupport (fun g : UJ ε => φ (toM g)) := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, ⟨hH, R, hR⟩, -, rfl⟩ := h
    have hM : Continuous fun g : UJ ε => toM g := Units.continuous_val.comp continuous_subtype_val
    refine ⟨?_, ?_⟩
    · have hr : Continuous fun g : UJ ε => rM ε (toM g) := (GlobalTheory.offDiagBlockNorm_cont_inv n ε).1
      have hent : Continuous fun g : UJ ε =>
          (Sum.elim (fun x => toM g x.1 x.2) (fun x => star (toM g x.1 x.2)) :
            (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ) := by
        refine continuous_pi fun i => ?_
        rcases i with x | x
        · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp hM)
        · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp hM))
      exact (Complex.continuous_ofReal.comp (hH.continuous.comp hr)).mul
        ((MvPolynomial.continuous_eval P).comp hent)
    · refine HasCompactSupport.intro (GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel n ε R) fun g hg => ?_
      have h : R ≤ rM ε (toM g) := (not_le.1 hg).le
      simp [bas, hR _ h]
  | zero => exact ⟨continuous_const, HasCompactSupport.zero⟩
  | add φ ψ _ _ h1 h2 => exact ⟨h1.1.add h2.1, h1.2.add h2.2⟩
  | smul c φ _ h => exact ⟨h.1.const_smul c, h.2.smul_left (f := fun _ => c)⟩

theorem shape_left {ε : Fin n → Bool} {d : ℕ} {φ : Mat n → ℂ} (hφ : φ ∈ ShapeM ε d) (g : UJ ε) :
    (fun k : KG ε => φ (toM ((k : UJ ε)⁻¹ * g))) ∈ polyK ε d := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, -, hP, rfl⟩ := h
    obtain ⟨Q, hQ, hQe⟩ := ev_mul 1 (toM g) P
    obtain ⟨S, hS, hSe⟩ := ev_conjTranspose Q
    have hm : (fun k : KG ε => ev (toMK k) S) ∈ polyK ε d :=
      mem_polyK.2 ⟨S, hS.trans (hQ.trans hP), fun _ => rfl⟩
    convert (polyK ε d).smul_mem (H (rM ε (toM g)) : ℂ) hm using 1
    funext k
    have h1 : rM ε (toM ((k : UJ ε)⁻¹ * g)) = rM ε (toM g) := by
      simpa using rM_inv ε k⁻¹ 1 g
    have h2 : toM ((k : UJ ε)⁻¹ * g) = 1 * (toMK k).conjTranspose * toM g := by
      rw [Matrix.one_mul, ← toMK_inv]; rfl
    simp only [bas, Pi.smul_apply, smul_eq_mul]
    rw [h1, h2, hQe, hSe]
  | zero => exact (polyK ε d).zero_mem
  | add φ ψ _ _ h1 h2 => exact (polyK ε d).add_mem h1 h2
  | smul c φ _ h => exact (polyK ε d).smul_mem c h

theorem shape_right {ε : Fin n → Bool} {d : ℕ} {φ : Mat n → ℂ} (hφ : φ ∈ ShapeM ε d) (g : UJ ε) :
    (fun k : KG ε => φ (toM (g * (k : UJ ε)))) ∈ polyK ε d := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, -, hP, rfl⟩ := h
    obtain ⟨Q, hQ, hQe⟩ := ev_mul (toM g) 1 P
    have hm : (fun k : KG ε => ev (toMK k) Q) ∈ polyK ε d :=
      mem_polyK.2 ⟨Q, hQ.trans hP, fun _ => rfl⟩
    convert (polyK ε d).smul_mem (H (rM ε (toM g)) : ℂ) hm using 1
    funext k
    have h1 : rM ε (toM (g * (k : UJ ε))) = rM ε (toM g) := by
      simpa using rM_inv ε 1 k g
    have h2 : toM (g * (k : UJ ε)) = toM g * toMK k * 1 := by
      rw [Matrix.mul_one]; rfl
    simp only [bas, Pi.smul_apply, smul_eq_mul]
    rw [h1, h2, hQe]
  | zero => exact (polyK ε d).zero_mem
  | add φ ψ _ _ h1 h2 => exact (polyK ε d).add_mem h1 h2
  | smul c φ _ h => exact (polyK ε d).smul_mem c h

theorem conj_mem {ε : Fin n → Bool} {d : ℕ} {F : KG ε → ℂ} (hF : F ∈ polyK ε d) :
    (fun k => conj (F k)) ∈ polyK ε d := by
  obtain ⟨P, hP, h⟩ := mem_polyK.1 hF
  obtain ⟨Q, hQ, hQe⟩ := conj_ev P
  exact mem_polyK.2 ⟨Q, hQ.trans hP, fun k => by rw [h, hQe]⟩

end GlobalTheory.PsCo.Pc3.RangeSh

namespace GlobalTheory.PsCo.Pc3

open RangeSh

theorem rangeShape : RangeShape := by
  intro n ε μ _ U _ _ _ π hπ d φ hφ
  haveI := GlobalTheory.unitarySigns_haar_isMulRightInvariant n ε μ
  obtain ⟨hc, hs⟩ := shape_cc hφ
  set f : UJ ε → ℂ := fun g => φ (toM g) with hf
  have hT : IsRepOp π μ f (repOp π μ f) := hπ.isRepOp hc hs
  have hin : ∀ a b : U, ⟪a, repOp π μ f b⟫_ℂ = ∫ g, f g * ⟪a, π g b⟫_ℂ ∂μ := by
    intro a b
    rw [(hT b).2, ← integral_inner (hT b).1]
    simp only [inner_smul_right]
  have hco : ∀ a b : U, Continuous fun g => ⟪a, π g b⟫_ℂ :=
    fun a b => continuous_const.inner (hπ.continuous_apply b)
  refine ⟨hT, fun u => ⟨fun l => mem_polyK.1 ?_, fun l => mem_polyK.1 ?_⟩⟩
  · have key := GlobalTheory.Pc3.RS.integral_mem μ (polyK ε d) (fun g k => ⟪l, π g u⟫_ℂ * f ((k : UJ ε)⁻¹ * g))
      (fun g => (polyK ε d).smul_mem ⟪l, π g u⟫_ℂ (shape_left hφ g))
      (fun k => ((hco l u).mul (hc.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        (hs.comp_homeomorph (Homeomorph.mulLeft ((k : UJ ε)⁻¹))).mul_left)
    convert key using 1
    funext k
    have e1 : ⟪l, π k (repOp π μ f u)⟫_ℂ = ⟪π (k : UJ ε)⁻¹ l, repOp π μ f u⟫_ℂ := by
      rw [hπ.inner_apply_left, inv_inv]
    rw [e1, hin, ← integral_mul_left_eq_self (fun g => ⟪l, π g u⟫_ℂ * f ((k : UJ ε)⁻¹ * g)) (k : UJ ε)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hπ.inner_apply_left, inv_inv, inv_mul_cancel_left, map_mul, ContinuousLinearMap.mul_apply]
    ring
  · have key := GlobalTheory.Pc3.RS.integral_mem μ (polyK ε d) (fun g k => ⟪u, π g l⟫_ℂ * f (g * (k : UJ ε)))
      (fun g => (polyK ε d).smul_mem ⟪u, π g l⟫_ℂ (shape_right hφ g))
      (fun k => ((hco u l).mul (hc.comp (continuous_id.mul continuous_const))).integrable_of_hasCompactSupport
        (hs.comp_homeomorph (Homeomorph.mulRight (k : UJ ε))).mul_left)
    convert conj_mem key using 1
    funext k
    have e1 : ⟪l, π k (ContinuousLinearMap.adjoint (repOp π μ f) u)⟫_ℂ =
        conj ⟪u, repOp π μ f (π (k : UJ ε)⁻¹ l)⟫_ℂ := by
      rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, hπ.inner_apply_left, inv_inv]
    rw [e1, hin, ← integral_mul_right_eq_self (fun g => ⟪u, π g l⟫_ℂ * f (g * (k : UJ ε))) (k : UJ ε)⁻¹]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [inv_mul_cancel_right, map_mul, ContinuousLinearMap.mul_apply]
    ring

end GlobalTheory.PsCo.Pc3

end
