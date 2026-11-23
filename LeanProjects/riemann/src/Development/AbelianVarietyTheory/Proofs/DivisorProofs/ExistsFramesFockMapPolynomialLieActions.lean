import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapSignaturesDependOnPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSignatureOrthonormalFrameEigenOfCartanInvoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMemberLieActionFockPlusTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweSplittingActsFockActionPlusTraceMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceEqRangeFockMapVariableSignatuStatement

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD.FockData

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) : (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, inclR, compInf, infEmb_tmul]

theorem det_map_ne_zero {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (h : J.det ≠ 0) :
    (J.map τ).det ≠ 0 := by
  rw [show J.map τ = τ.mapMatrix J from rfl, ← RingHom.map_det]
  exact (map_ne_zero τ).2 h

theorem exists_fock_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) , IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W), IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → M.IsWeil ψ χX χW om → ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) → (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) → ∃ (P Q R S : InfinitePlace F → ℕ) (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c c' : InfinitePlace F → ℂ), FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C ∧ Function.Injective Φ ∧ LinearMap.range Φ = M.Pol ψ τ ∧ ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c ∧ ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c' := by
  intro F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hXh hXd hWs hWd hW τ hXc hWc

  have hX : ∀ w, ∃ (r s : ℕ) (A : Matrix (Fin n) (Ix r s) ℂ),
      IsFrame (X.J.map (τ w).1) A ∧ X.θ w * A = A * Jm r s := by
    intro w
    refine GlobalTheory.T.exists_signatureOrthonormalFrame_eigen_of_cartanInvolution n _ _ ?_ (det_map_ne_zero _ _ hXd) (hXc w)
    intro i j
    simp only [Matrix.map_apply]
    rw [← hCM.2.2.2 (τ w).1, hXh]
  have hW' : ∀ w, ∃ (r s : ℕ) (C : Matrix (Fin d) (Ix r s) ℂ),
      IsFrame (Complex.I • W.J.map (τ w).1) C ∧ W.θ w * C = C * Jm r s := by
    intro w
    refine GlobalTheory.T.exists_signatureOrthonormalFrame_eigen_of_cartanInvolution d _ _ ?_ ?_ (hWc w)
    · intro i j
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul']
      rw [← hCM.2.2.2 (τ w).1, hWs, map_neg, show star Complex.I = -Complex.I from Complex.conj_I]
      ring
    · rw [Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (det_map_ne_zero _ _ hWd)
  choose P Q A hA hθA using hX
  choose R S C hC hθC using hW'

  have hF : FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C := by
    refine ⟨one_mul _, fun w => ?_, fun w => ?_⟩
    · rw [one_smul, incM_map_piInf]
      exact hA w
    · rw [incM_map_piInf]
      exact hC w
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_fockMap_signatures_depend_on_place F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co 1 Complex.I A C
    hCM hψ hF

  obtain ⟨hB, ⟨d', hd', hA'⟩, -⟩ := hW
  obtain ⟨c, hc⟩ := GlobalTheory.T.firstMember_lieAction_fock_plus_trace F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co d' 1 Complex.I A C Φ
    (om.comp (MonoidHom.inl _ _)) hCM hψ hF hΦ hd' hA'.1
  obtain ⟨c', hc'⟩ := GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co 1 Complex.I A C Φ
    (om.comp (MonoidHom.inr _ _)) hCM hψ hF hΦ hB.1
  exact ⟨P, Q, R, S, A, C, Φ, c, c', hF, hΦ.1,
    GlobalTheory.T.polynomialFockSpace_eq_range_fockMap_variable_signature F E σ n d P Q R S X W M ψ τ A C Φ hCM hψ hF hθA hθC hΦ, hc, hc'⟩

end GlobalTheory.HoweD.FockData

end
