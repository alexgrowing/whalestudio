import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerMovedVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FockFrameChange

private theorem sum4_lemma {α β γ δ R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid R]
    (f : α → β → γ → δ → R) :
    ∑ k, ∑ l, ∑ k', ∑ l', f k l k' l' = ∑ k', ∑ l', ∑ k, ∑ l, f k l k' l' := by
  calc ∑ k, ∑ l, ∑ k', ∑ l', f k l k' l' = ∑ k, ∑ k', ∑ l, ∑ l', f k l k' l' :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k', ∑ k, ∑ l, ∑ l', f k l k' l' := Finset.sum_comm
    _ = ∑ k', ∑ k, ∑ l', ∑ l, f k l k' l' :=
        Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k', ∑ l', ∑ k, ∑ l, f k l k' l' := Finset.sum_congr rfl fun k' _ => Finset.sum_comm

theorem substF_mul {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF h g (GlobalTheory.CompactHowe.substF h' g' P) =
      GlobalTheory.CompactHowe.substF (fun τ => h τ * h' τ) (fun τ => g τ * g' τ) P := by
  unfold GlobalTheory.CompactHowe.substF
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  refine congrArg (fun F => (MvPolynomial.aeval F) P) (funext fun p => ?_)
  obtain ⟨τ, a, b⟩ := p
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine (sum4_lemma _).trans ?_
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l' _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem change_mul {n : ℕ} {A F : Matrix (Fin n) (Fin n) ℂ} (hA : A * A⁻¹ = 1) (hF : F * F⁻¹ = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) : F⁻¹ * A * (A⁻¹ * M * A) = F⁻¹ * M * F * (F⁻¹ * A) := by
  calc F⁻¹ * A * (A⁻¹ * M * A) = F⁻¹ * (A * A⁻¹) * M * A := by simp only [Matrix.mul_assoc]
    _ = F⁻¹ * M * A := by rw [hA, Matrix.mul_one]
    _ = F⁻¹ * M * (F * F⁻¹) * A := by rw [hF, Matrix.mul_one]
    _ = F⁻¹ * M * F * (F⁻¹ * A) := by simp only [Matrix.mul_assoc]

theorem change_mul_invT {n : ℕ} {A F : Matrix (Fin n) (Fin n) ℂ} (hA : A * A⁻¹ = 1) (hF : F * F⁻¹ = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ((F⁻¹ * A)⁻¹).transpose * ((A⁻¹ * M * A)⁻¹).transpose = ((F⁻¹ * M * F)⁻¹).transpose * ((F⁻¹ * A)⁻¹).transpose := by
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.mul_inv_rev (F⁻¹ * A) (A⁻¹ * M * A),
    ← Matrix.mul_inv_rev (F⁻¹ * M * F) (F⁻¹ * A), change_mul hA hF M]

theorem subst_change {ι : Type} {N n : ℕ} {A F : ι → Matrix (Fin N) (Fin N) ℂ} {A' F' : ι → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ τ, A τ * (A τ)⁻¹ = 1) (hF : ∀ τ, F τ * (F τ)⁻¹ = 1) (hA' : ∀ τ, A' τ * (A' τ)⁻¹ = 1)
    (hF' : ∀ τ, F' τ * (F' τ)⁻¹ = 1) (M : ι → Matrix (Fin N) (Fin N) ℂ) (M' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * A τ).map (starRingEnd ℂ))
                 (fun τ => ((((F' τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ))
                 (GlobalTheory.CompactHowe.substF (fun τ => ((A τ)⁻¹ * M τ * A τ).map (starRingEnd ℂ))
                   (fun τ => ((((A' τ)⁻¹ * M' τ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) =
      GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * M τ * F τ).map (starRingEnd ℂ))
        (fun τ => ((((F' τ)⁻¹ * M' τ * F' τ)⁻¹).transpose).map (starRingEnd ℂ))
        (GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * A τ).map (starRingEnd ℂ))
          (fun τ => ((((F' τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) := by
  rw [substF_mul, substF_mul]
  exact congrArg₂ (fun h g => GlobalTheory.CompactHowe.substF h g P)
    (funext fun τ => by
      simp only [← Matrix.map_mul]
      rw [change_mul (hA τ) (hF τ)])
    (funext fun τ => by
      simp only [← Matrix.map_mul]
      rw [change_mul_invT (hA' τ) (hF' τ)])

theorem map_mul_inv {n : ℕ} {E : Type} [Field E] (φ : E →+* ℂ) (g : GL (Fin n) E) :
    g.1.map φ * (g.1.map φ)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  have h := (Matrix.isUnits_det_units g).map φ
  rw [RingHom.map_det] at h
  exact h

private theorem fock_frame_lemma {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BS A' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT A : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hBS : ∀ τ, BS τ * (BS τ)⁻¹ = 1) (hBT : ∀ τ, BT τ * (BT τ)⁻¹ = 1)
    (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) A' A f P =
      pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f
        (GlobalTheory.CompactHowe.substF (fun τ => ((BT τ)⁻¹ * A τ).map (starRingEnd ℂ))
          (fun τ => ((((BS τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) := by
  have e1 : A' = fun τ => BS τ * ((BS τ)⁻¹ * A' τ) := by
    funext τ
    rw [← Matrix.mul_assoc, hBS τ, Matrix.one_mul]
  have e2 : A = fun τ => BT τ * ((BT τ)⁻¹ * A τ) := by
    funext τ
    rw [← Matrix.mul_assoc, hBT τ, Matrix.one_mul]
  conv_lhs => rw [e1, e2]
  exact GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D ψ θ S T hψ hθ BS (fun τ => (BS τ)⁻¹ * A' τ) BT
    (fun τ => (BT τ)⁻¹ * A τ) f hf P

theorem exists_frame_change : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∃ σ₀ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank,
      (∀ t ∈ U, ∀ d : FinDatum G t (.chi i D.R.m), S.Z.HasVec d → ∀ P,
        W.fock (.chi i D.R.m) (S.Z.vec d) P = fockIn W S.N.frC (.chi i D.R.m) (S.Z.vec d) (σ₀ P)) ∧
      ∀ k : GA D (G.V (.grid i D.R.m)), k ∈ GinfC (G.V (.grid i D.R.m)) →
        ∀ k' : GA D (G.V (.grid (i + 1) D.R.m)), k' ∈ GinfC (G.V (.grid (i + 1) D.R.m)) → ∀ P,
          σ₀ (realSubst W W.onb (.chi i D.R.m) k k' P) = realSubst W S.N.frC (.chi i D.R.m) k k' (σ₀ P) := by
  intro D T L sc G W U S μ0 hL i hi
  have hdT : DefNode D.R.m (Node.grid i D.R.m) := by
    unfold DefNode
    exact ⟨hi.le, rfl⟩
  have hdS : DefNode D.R.m (Node.grid (i + 1) D.R.m) := by
    unfold DefNode
    exact ⟨hi, rfl⟩
  have hdP : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := by
    unfold DefPair
    exact ⟨hi, rfl⟩
  have honb : ∀ X, DefNode D.R.m X → ∀ τ, W.onb X τ * (W.onb X τ)⁻¹ = 1 := fun X hX τ =>
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse (GlobalTheory.FockReal.onb_def hL W hX τ))
  have hfr : ∀ X τ, S.N.frC X τ * (S.N.frC X τ)⁻¹ = 1 := fun X τ => map_mul_inv (tauE D τ) (S.N.fr X)
  refine ⟨(GlobalTheory.CompactHowe.substF
      (fun τ => ((S.N.frC (Node.grid i D.R.m) τ)⁻¹ * W.onb (Node.grid i D.R.m) τ).map (starRingEnd ℂ))
      (fun τ => ((((S.N.frC (Node.grid (i + 1) D.R.m) τ)⁻¹ * W.onb (Node.grid (i + 1) D.R.m) τ)⁻¹).transpose).map
        (starRingEnd ℂ))).toLinearMap, ?_, ?_⟩
  · intro t _ d hd P
    have hf := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hdP d hd).1
    have hcS : G.cartS W.cart (Pair.chi i D.R.m : Pair T) = fun _ => -1 := by
      funext τ
      show -W.cart (Node.grid (i + 1) D.R.m) τ = -1
      rw [GlobalTheory.FockReal.cart_def hL W hdS τ]
    have hcT : G.onT W.cart (Pair.chi i D.R.m : Pair T) = fun _ => 1 := by
      funext τ
      exact GlobalTheory.FockReal.cart_def hL W hdT τ
    unfold GlobalTheory.ChiGrid.GridData.Weil.fock GlobalTheory.FunObj.fockIn
    rw [hcS, hcT, AlgHom.toLinearMap_apply]
    exact fock_frame_lemma W.ψ W.θ (G.V (Node.grid (i + 1) D.R.m)) (G.V (Node.grid i D.R.m)) W.ψ_std W.θ_is
      (S.N.frC (Node.grid (i + 1) D.R.m)) (W.onb (Node.grid (i + 1) D.R.m))
      (S.N.frC (Node.grid i D.R.m)) (W.onb (Node.grid i D.R.m))
      (hfr _) (hfr _) (S.Z.vec d) hf P
  · intro k _ k' _ P
    unfold GlobalTheory.FockReal.realSubst
    rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]
    exact subst_change (A := W.onb (Node.grid i D.R.m)) (F := S.N.frC (Node.grid i D.R.m))
      (A' := W.onb (Node.grid (i + 1) D.R.m)) (F' := S.N.frC (Node.grid (i + 1) D.R.m))
      (fun τ => honb _ hdT τ) (hfr _) (fun τ => honb _ hdS τ) (hfr _) _ _ P

end GlobalTheory.FockFrameChange

end
