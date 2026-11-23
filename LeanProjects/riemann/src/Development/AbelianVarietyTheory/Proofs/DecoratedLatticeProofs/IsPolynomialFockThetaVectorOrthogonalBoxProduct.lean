import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumMatApply
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVector
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
open GlobalTheory.OrientedHeis GlobalTheory.Core.Rk.FockBox

noncomputable section

namespace GlobalTheory.Core.Rk.FockBoxT

theorem killed_of_leibniz₂ {P₁ P₂ Q U₁ U₂ V : Type} [Zero U₁] [Zero U₂] [AddCommGroup V] (a₁ : P₁ → U₁ → U₁)
    (a₂ : P₂ → U₂ → U₂) (b : Q → V → V) (T₁ : U₁ → Prop) (T₂ : U₂ → Prop)
    (TV : V → Prop) (δ : U₁ → U₂ → V) (c₁ : Q → P₁) (c₂ : Q → P₂) (ha₁ : ∀ p f, T₁ f → T₁ (a₁ p f))
    (ha₂ : ∀ p f, T₂ f → T₂ (a₂ p f)) (hb : ∀ q f, TV f → TV (b q f))
    (hadd : ∀ q f g, TV f → TV g → b q (f + g) = b q f + b q g) (hb0 : ∀ q, b q 0 = 0)
    (hδ : ∀ f g, T₁ f → T₂ g → TV (δ f g)) (h1 : ∀ g, δ 0 g = 0) (h2 : ∀ f, δ f 0 = 0)
    (hL : ∀ q f g, T₁ f → T₂ g → b q (δ f g) = δ (a₁ (c₁ q) f) g + δ f (a₂ (c₂ q) g)) (N : ℕ) :
    ∀ (N₁ N₂ : ℕ) (f : U₁) (g : U₂), N₁ + N₂ ≤ N → T₁ f → T₂ g →
      (∀ l : List P₁, l.length = N₁ → l.foldr a₁ f = 0) → (∀ l : List P₂, l.length = N₂ → l.foldr a₂ g = 0) →
      ∀ l : List Q, l.length = N → l.foldr b (δ f g) = 0 := by
  have w0 : ∀ l : List Q, l.foldr b 0 = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hb0]
  have wT : ∀ (l : List Q) f, TV f → TV (l.foldr b f) := fun l f hf => by
    induction l with
    | nil => exact hf
    | cons q l ih => exact hb _ _ ih
  have wadd : ∀ (l : List Q) f g, TV f → TV g → l.foldr b (f + g) = l.foldr b f + l.foldr b g := fun l f g hf hg => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hadd _ _ _ (wT l f hf) (wT l g hg)]; rfl
  have step : ∀ {P U : Type} [Zero U] (a : P → U → U) (M : ℕ) (f : U) (p : P),
      (∀ l : List P, l.length = M + 1 → l.foldr a f = 0) →
      ∀ l : List P, l.length = M → l.foldr a (a p f) = 0 := fun a M f p h l hl => by
    have := h (l ++ [p]) (by simp [hl])
    rwa [List.foldr_append] at this
  induction N with
  | zero =>
    intro N₁ N₂ f g hN _ _ k₁ _ l _
    have : f = 0 := k₁ [] (by simp; omega)
    rw [this, h1, w0]
  | succ N ih =>
    intro N₁ N₂ f g hN hf hg k₁ k₂ l hl
    rcases N₁ with _ | M₁
    · have : f = 0 := k₁ [] rfl
      rw [this, h1, w0]
    rcases N₂ with _ | M₂
    · have : g = 0 := k₂ [] rfl
      rw [this, h2, w0]
    obtain rfl | ⟨l', q, rfl⟩ := l.eq_nil_or_concat'
    · simp at hl
    have hl' : l'.length = N := by simpa using hl
    rw [List.foldr_append, List.foldr_cons, List.foldr_nil, hL q f g hf hg,
      wadd _ _ _ (hδ _ _ (ha₁ _ _ hf) hg) (hδ _ _ hf (ha₂ _ _ hg)),
      ih M₁ (M₂ + 1) _ _ (by omega) (ha₁ _ _ hf) hg (step _ _ _ _ k₁) k₂ l' hl',
      ih (M₁ + 1) M₂ _ _ (by omega) hf (ha₂ _ _ hg) k₁ (step _ _ _ _ k₂) l' hl', add_zero]

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}

theorem lineAt_mul_left (hθ : IsInfFam θ) {k m n : ℕ} (p : Mx D k m) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (Formalism.IndefR.Datum.compAt θ τ p * z) t = (HMul.hMul p (lineAt θ τ z t) : Mx D k n) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ Mx D k n :=
    { toFun := fun t => HMul.hMul p (lineAt θ τ z t)
      map_zero' := by rw [AddMonoidHom.map_zero, Matrix.mul_zero]
      map_add' := fun s t => by rw [AddMonoidHom.map_add, Matrix.mul_add] }
  have hL' : IsLineAt θ τ (Formalism.IndefR.Datum.compAt θ τ p * z) L := by
    refine ⟨continuous_const.matrix_mul hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (HMul.hMul p (lineAt θ τ z t) : Mx D k n).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1, Matrix.mul_zero]
    · show Formalism.IndefR.Datum.compAt θ τ' (HMul.hMul p (lineAt θ τ z t) : Mx D k n) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul]
      · rw [Matrix.mul_zero]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

variable {A B W H : HSp D} (o : OrthDec B W H)

theorem compAt_pA (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ o.pA = o.qA.map (tauE D τ) := by
  ext i j
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem compAt_pB (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ o.pB = o.qB.map (tauE D τ) := by
  ext i j
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem dRho_boxT (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin B.rank) (Fin A.rank) ℂ) {f : WO A W → ℂ} {g : WO A H → ℂ} (hf : IsThetaFunO ψ A W f)
    (hg : IsThetaFunO ψ A H g) :
    Formalism.IndefR.Datum.dRho (heisO ψ A B) θ τ z (o.boxT A f g) =
      o.boxT A (Formalism.IndefR.Datum.dRho (heisO ψ A W) θ τ (o.qA.map (tauE D τ) * z) f) g +
        o.boxT A f (Formalism.IndefR.Datum.dRho (heisO ψ A H) θ τ (o.qB.map (tauE D τ) * z) g) := by
  funext x
  have d := (hasDerivAt_dRho hθ hψ τ (o.qA.map (tauE D τ) * z) hf (o.resT A x).1).mul
    (hasDerivAt_dRho hθ hψ τ (o.qB.map (tauE D τ) * z) hg (o.resT A x).2)
  simp only [map_zero, heisO_zero] at d
  refine Eq.trans ?_ d.deriv
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [o.heisO_boxT, Pi.mul_apply, ← compAt_pA o hθ, ← compAt_pB o hθ, lineAt_mul_left hθ, lineAt_mul_left hθ]
  rfl

theorem qA_sumMat (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    o.qA.map (tauE D τ) * sumMat o sW sH τ = sW τ * o.qA.map (tauE D τ) := by
  simp only [sumMat_apply, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qA_iA, o.qA_iB,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem qB_sumMat (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    o.qB.map (tauE D τ) * sumMat o sW sH τ = sH τ * o.qB.map (tauE D τ) := by
  simp only [sumMat_apply, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qB_iA, o.qB_iB,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, zero_add]

theorem mul_cplxO {k m n : ℕ} {q : Matrix (Fin k) (Fin m) ℂ} {s : Matrix (Fin m) (Fin m) ℂ}
    {s' : Matrix (Fin k) (Fin k) ℂ} (h : q * s = s' * q) (r : Matrix (Fin n) (Fin n) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    q * cplxO r s z = cplxO r s' (q * z) := by
  unfold cplxO
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_assoc s']

theorem annih_boxT (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (s : Matrix (Fin A.rank) (Fin A.rank) ℂ) (sW : RealMat W) (sH : RealMat H)
    (z : Matrix (Fin B.rank) (Fin A.rank) ℂ) {f : WO A W → ℂ} {g : WO A H → ℂ} (hf : IsThetaFunO ψ A W f)
    (hg : IsThetaFunO ψ A H g) :
    annih (heisO ψ A B) θ τ (cplxO s (sumMat o sW sH τ)) z (o.boxT A f g) =
      o.boxT A (annih (heisO ψ A W) θ τ (cplxO s (sW τ)) (o.qA.map (tauE D τ) * z) f) g +
        o.boxT A f (annih (heisO ψ A H) θ τ (cplxO s (sH τ)) (o.qB.map (tauE D τ) * z) g) := by
  unfold annih
  rw [dRho_boxT o hθ hψ τ _ hf hg, dRho_boxT o hθ hψ τ _ hf hg, mul_cplxO (qA_sumMat o sW sH τ),
    mul_cplxO (qB_sumMat o sW sH τ)]
  funext x
  simp only [OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem isFockVec_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B W H : HSp D) (o : OrthDec B W H) (sA : RealMat A) (sW : RealMat W) (sH : RealMat H), IsStdChar D ψ (-1) → IsInfFam θ → ∀ Φ Φ', IsFockVec ψ θ A W sA sW Φ → IsFockVec ψ θ A H sA sH Φ' → IsFockVec ψ θ A B sA (sumMat o sW sH) (o.boxT A Φ Φ') := by
  intro D ψ θ A B W H o sA sW sH hψ hθ Φ₁ Φ₂ ⟨t₁, N₁, k₁⟩ ⟨t₂, N₂, k₂⟩
  have hT : ∀ (S : HSp D) τ J z f, IsThetaFunO ψ A S f → IsThetaFunO ψ A S (annih (heisO ψ A S) θ τ J z f) :=
    fun S τ J z f hf => theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ _ hf))
  refine ⟨o.isThetaFunO_boxT t₁ t₂, N₁ + N₂, ?_⟩
  refine killed_of_leibniz₂ (P₁ := D.what₂.Tau × Matrix (Fin W.rank) (Fin A.rank) ℂ)
    (P₂ := D.what₂.Tau × Matrix (Fin H.rank) (Fin A.rank) ℂ)
    (Q := D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (fun p f => annih (heisO ψ A W) θ p.1 (cplxO (sA p.1) (sW p.1)) p.2 f)
    (fun p f => annih (heisO ψ A H) θ p.1 (cplxO (sA p.1) (sH p.1)) p.2 f)
    (fun p f => annih (heisO ψ A B) θ p.1 (cplxO (sA p.1) (sumMat o sW sH p.1)) p.2 f)
    (IsThetaFunO ψ A W) (IsThetaFunO ψ A H) (IsThetaFunO ψ A B) (o.boxT A)
    (fun q => (q.1, o.qA.map (tauE D q.1) * q.2)) (fun q => (q.1, o.qB.map (tauE D q.1) * q.2))
    (fun p f hf => hT W _ _ _ f hf) (fun p f hf => hT H _ _ _ f hf) (fun p f hf => hT B _ _ _ f hf)
    (fun q f g hf hg => ?_) (fun q => ?_)
    (fun f g hf hg => o.isThetaFunO_boxT hf hg) (fun g => ?_) (fun f => ?_)
    (fun q f g hf hg => annih_boxT o hθ hψ q.1 (sA q.1) sW sH q.2 hf hg)
    _ N₁ N₂ Φ₁ Φ₂ le_rfl t₁ t₂ k₁ k₂
  · simp only [annih]
    rw [GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hf hg, GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hf hg, smul_add]
    abel
  · funext x
    simp [annih, Formalism.IndefR.Datum.dRho, heisO]
  · funext x
    simp [OrthDec.boxT]
  · funext x
    simp [OrthDec.boxT]

end GlobalTheory.Core.Rk.FockBoxT

end
