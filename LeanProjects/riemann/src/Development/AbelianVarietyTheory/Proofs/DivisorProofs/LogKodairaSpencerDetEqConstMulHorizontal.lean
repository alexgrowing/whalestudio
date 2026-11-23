import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberTangentPointOfLogarithmicDerivatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeLinearInKodairaSpencerMatrixOfIStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedSymmetricPairMatrixHorizontalSingleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFlagTangentConjugateMatrixChangeEqOneStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogPole

theorem logDet_eq_hor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (s : ℚ), s ≠ 0 → KSCompare TF s → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (b : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), (∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (b j).1 (GlobalTheory.LogKSDiv.symPair e (ε j))) → ∀ (o : Fin Dw.dim ≃ HIx Dw (psiSet H)), ∃ a : ℚ, a ≠ 0 ∧ ∀ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1) (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ, (g σ).det = 1) → GlobalTheory.Frames.FrChg g 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : HIx Dw (psiSet H) → FrPt Xo c (DualNumber K)) (hw : ∀ b, ⊤ ≤ (frX (w b) ≫ TF.Y.j) ⁻¹ᵁ U.1), (∀ b, IsDef P (w b) ∧ FlagTan.IsKS (psiSet H) P (w b).x (Pi.single b 1)) → ev (frX P₀ ≫ TF.Y.j) U.1 hU (logDet (fun j => (b j).1) x) = (a : K) * (Matrix.of fun i j => (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd).det := by
  intro E _ _ _ H Dw l Xo c TF s hs hcmp hKS U n e v hv ε b hb o
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.balancedSymmetricPairMatrix_horizontal_single ε
  refine ⟨s ^ Dw.dim * ((Equiv.Perm.sign (κ.trans o.symm) : ℤ) : ℚ), ?_, ?_⟩
  · have : ((Equiv.Perm.sign (κ.trans o.symm) : ℤ) : ℚ) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (κ.trans o.symm)) with h | h <;> simp [h]
    exact mul_ne_zero (pow_ne_zero _ hs) this
  intro x K _ _ P₀ P hU g hg hP hB w hw hwk
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.tangentDerivative_linear_in_kodairaSpencerMatrix_of_iso TF K P₀ (hKS K P₀) U.1 hU
  choose y' hy' hsnd hred hev using fun j => GlobalTheory.T.exists_dualNumberTangentPoint_of_logarithmicDerivation TF U (b j) K P₀ hU
  have hKSj : ∀ j, FlagTan.IsKS (psiSet H) P₀ (y' j ≫ pullback.fst _ _)
      (fun k => (s : K) * (Pi.single (κ j) (1 : K) : HIx Dw (psiSet H) → K) k) := by
    intro j
    have := hcmp U n e v hv (b j) _ (hb j) K P₀ hU hB (y' j) (hy' j) (hsnd j) (hev j)
    convert this using 3 with k
    rw [hκ (ev (frX P₀ ≫ TF.Y.j) U.1 hU) n e j k]
  have hL : ∀ i j, ev (frX P₀ ≫ TF.Y.j) U.1 hU ((b j).1 (x i)) = (s : K) * δ (κ j) (x i) := by
    intro i j
    have h1 := hδ (y' j) (hy' j) (hsnd j) (hred j) _ (hKSj j) (x i)
    rw [hev j] at h1
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h1
    rw [h1]
    simp [Pi.single_apply, mul_comm, mul_left_comm]
  have hx : P.x = P₀.x := hP.1
  have hR : ∀ i j, (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd =
      ∑ k, FlagTan.ksChg (psiSet H) g (Pi.single (o j) 1 : HIx Dw (psiSet H) → K) k * δ k (x i) := by
    intro i j
    have hk := (FlagTan.isKS_frChg_iff (psiSet H) g 1 P₀ P hP _ _).1 (hwk (o j)).2
    refine hδ (frX (w (o j))) (hw _) (GlobalTheory.FlagMod.frX_snd _) ?_ _ ?_ (x i)
    · rw [GlobalTheory.FlagMod.frX_frMap (hwk (o j)).1]
      exact GlobalTheory.FlagMod.eq_frX P₀ (by rw [GlobalTheory.FlagMod.frX_fst, hx]) (GlobalTheory.FlagMod.frX_snd P)
    · rw [GlobalTheory.FlagMod.frX_fst]; exact hk
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin Dw.dim) (Fin Dw.dim) K, A = Matrix.of fun i j => δ (o j) (x i) := ⟨_, rfl⟩
  have eL : (ev (frX P₀ ≫ TF.Y.j) U.1 hU).mapMatrix (Matrix.of fun i j => (b j).1 (x i)) =
      (s : K) • A.submatrix id (κ.trans o.symm) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hL, hA]
    simp
  have eR : (Matrix.of fun i j => (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd) =
      A * Matrix.of fun i j => FlagTan.ksChg (psiSet H) g (Pi.single (o j) 1 : HIx Dw (psiSet H) → K) (o i) := by
    ext i j
    rw [Matrix.of_apply, hR, Matrix.mul_apply, ← Equiv.sum_comp o, hA]
    simp only [Matrix.of_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [logDet, RingHom.map_det, eR, Matrix.det_mul, GlobalTheory.T.det_flagTangentConjugateMatrixChange_eq_one K g hg o, mul_one, eL, Matrix.det_smul,
    Matrix.det_permute', Fintype.card_fin]
  push_cast
  ring

end GlobalTheory.LogPole
