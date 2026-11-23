import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_cons (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a b c d : E)
    (x y : Fin M → E) :
    hE σ (hypOne J) (Fin.cons a (Fin.cons b x) : Fin (M + 2) → E)
        (Fin.cons c (Fin.cons d y) : Fin (M + 2) → E) = σ a * d + σ b * c + hE σ J x y := by
  simp only [hE, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have e00 : hypOne J 0 0 = 0 := rfl
  have e01 : hypOne J 0 (Fin.succ 0) = 1 := rfl
  have e10 : hypOne J (Fin.succ 0) 0 = 1 := rfl
  have e11 : hypOne J (Fin.succ 0) (Fin.succ 0) = 0 := rfl
  have e0r : ∀ j : Fin M, hypOne J 0 j.succ.succ = 0 := fun _ => rfl
  have e1r : ∀ j : Fin M, hypOne J (Fin.succ 0) j.succ.succ = 0 := fun _ => rfl
  have er0 : ∀ i : Fin M, hypOne J i.succ.succ 0 = 0 := fun _ => rfl
  have er1 : ∀ i : Fin M, hypOne J i.succ.succ (Fin.succ 0) = 0 := fun _ => rfl
  have err : ∀ i j : Fin M, hypOne J i.succ.succ j.succ.succ = J i j := fun _ _ => rfl
  simp only [e00, e01, e10, e11, e0r, e1r, er0, er1, err]
  simp
  ring

theorem e0_cons (M : ℕ) : e0 E M 0 = Fin.cons 1 (Fin.cons 0 (fun _ => 0)) := by
  funext i
  refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i

theorem consA_zero {M n : ℕ} (a : Fin 1 → Fin n → E) (Y : Fin n → Fin M → E) :
    consA a Y 0 = Fin.cons 1 (Fin.cons 0 (fun _ => 0)) := by
  rw [← e0_cons]; rfl

theorem consA_succ {M n : ℕ} (a : Fin 1 → Fin n → E) (Y : Fin n → Fin M → E) (j : Fin n) :
    consA a Y j.succ = Fin.cons (a 0 j) (Fin.cons 0 (Y j)) := rfl

theorem consA_mem (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a : Fin 1 → Fin n → E) (Y : Fin n → Fin M → E) (hY : Y ∈ framesE σ J (0 : Matrix (Fin n) (Fin n) E)) :
    consA a Y ∈ framesOne σ J n := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hg : ∀ i j, hE σ J (Y i) (Y j) = 0 := fun i j => congrFun (congrFun hY.2 i) j
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    rw [Fin.sum_univ_succ] at hc
    have htail : ∀ k : Fin n, c k.succ = 0 := by
      refine Fintype.linearIndependent_iff.1 hY.1 (fun k => c k.succ) ?_
      funext i
      have := congrFun hc i.succ.succ
      simpa [Finset.sum_apply, consA_zero, consA_succ] using this
    have h0 : c 0 = 0 := by
      have := congrFun hc 0
      simpa [Finset.sum_apply, consA_zero, consA_succ, htail] using this
    intro k
    exact Fin.cases h0 htail k
  · ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [gramE, consA_zero, hE_cons, hz, BlockAlg.hE_zero_left]
    · simp [gramE, consA_zero, consA_succ, hE_cons, hz, BlockAlg.hE_zero_left]
    · simp [gramE, consA_zero, consA_succ, hE_cons, hz, BlockAlg.hE_zero_right]
    · simp [gramE, consA_succ, hE_cons, hg]
  · rfl

theorem sec_zero (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin (n + 1) → Fin (M + 2) → E) (hX : X ∈ framesOne σ J n) (a : Fin n) :
    X a.succ (Fin.succ 0) = 0 := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hc : X a.succ = Fin.cons (X a.succ 0) (Fin.cons (X a.succ (Fin.succ 0)) (fun i => X a.succ i.succ.succ)) := by
    funext i
    refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i
  have h : hE σ (hypOne J) (X 0) (X a.succ) = 0 := congrFun (congrFun hX.1.2 0) a.succ
  rw [hX.2, e0_cons, hc, hE_cons, hz, BlockAlg.hE_zero_left] at h
  simpa using h

theorem tail_mem (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin (n + 1) → Fin (M + 2) → E) (hX : X ∈ framesOne σ J n) :
    (fun (a : Fin n) (i : Fin M) => X a.succ i.succ.succ) ∈ framesE σ J (0 : Matrix (Fin n) (Fin n) E) := by
  have hgr : ∀ a b, hE σ (hypOne J) (X a) (X b) = 0 := fun a b =>
    congrFun (congrFun hX.1.2 a) b
  have hc : ∀ a, X a = Fin.cons (X a 0) (Fin.cons (X a (Fin.succ 0)) (fun i => X a i.succ.succ)) :=
    fun a => by
      funext i
      refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i
  have hsec := sec_zero σ J X hX
  have h0 := hX.2.trans (e0_cons M)
  refine ⟨?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc' a => ?_
    have h1 := Fintype.linearIndependent_iff.1 hX.1.1
      (Fin.cons (-∑ k, c k * X k.succ 0) c) (by
      rw [Fin.sum_univ_succ, h0]
      funext i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
      · simp [Finset.sum_apply]
      · have hsec' : ∀ a : Fin n, X a.succ 1 = 0 := hsec
        simp [Finset.sum_apply, hsec']
      · have := congrFun hc' k
        simpa [Finset.sum_apply] using this) a.succ
    simpa using h1
  · ext a b
    have h := hgr a.succ b.succ
    rw [hc a.succ, hc b.succ, hE_cons, hsec, hsec] at h
    simpa [gramE] using h

def framesOneEquiv (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (n : ℕ) :
    framesE σ J (0 : Matrix (Fin n) (Fin n) E) × (Fin 1 → Fin n → E) ≃ framesOne σ J n where
  toFun p := ⟨consA p.2 p.1.1, consA_mem σ J p.2 p.1.1 p.1.2⟩
  invFun X := (⟨fun a i => X.1 a.succ i.succ.succ, tail_mem σ J X.1 X.2⟩, fun _ a => X.1 a.succ 0)
  left_inv p := by
    obtain ⟨⟨Y, hY⟩, a⟩ := p
    refine Prod.ext (Subtype.ext ?_) ?_
    · rfl
    · funext i j
      have : i = 0 := Subsingleton.elim _ _
      subst this
      rfl
  right_inv X := by
    obtain ⟨X, hX⟩ := X
    refine Subtype.ext ?_
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · exact hX.2.symm
    · funext i
      refine Fin.cases rfl (fun i => Fin.cases ?_ (fun l => rfl) i) i
      exact (sec_zero σ J X hX k).symm

theorem tsum_framesOne : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞), ∑' X : framesOne σ J n, f X.1 = ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∑' a : Fin 1 → Fin n → E, f (consA a Y.1) := by
  intro F E _ _ _ σ M J n f
  rw [← (framesOneEquiv σ J n).tsum_eq (fun X : framesOne σ J n => f X.1), ENNReal.tsum_prod']
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne
