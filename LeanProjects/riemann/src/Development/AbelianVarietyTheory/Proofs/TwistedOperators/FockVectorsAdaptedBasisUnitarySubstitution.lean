import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.BasisChange

open GlobalTheory.JointHarm.FMul (lsub lsub_X lsub_one lsub_mul fockL_lsub_adj Jm_mul_Jm Jm_conj)
open scoped Kronecker ComplexOrder

section Pol

variable {σ : Type}

theorem fockIp_eq (P Q : MvPolynomial σ ℂ) : fockIp P Q = star (Formalism.L2.DIV.fockL P Q) := by
  show fockIp P Q = star (Formalism.L2.DIV.fockS P Q)
  unfold fockIp Formalism.L2.DIV.fockS
  rw [star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', star_mul', star_star, starRingEnd_apply, star_natCast]
  simp only [Formalism.L2.DIV.mfact, Finsupp.prod]

variable [Fintype σ]

theorem lsub_homog (M : Matrix σ σ ℂ) {d : ℕ} {P : MvPolynomial σ ℂ} (h : P.IsHomogeneous d) :
    (lsub M P).IsHomogeneous d := by
  have hg : ∀ v : σ, (∑ w, MvPolynomial.C (M w v) * MvPolynomial.X w : MvPolynomial σ ℂ).IsHomogeneous 1 :=
    fun v => MvPolynomial.IsHomogeneous.sum _ _ _ fun w _ => MvPolynomial.isHomogeneous_C_mul_X _ _
  have key := h.eval₂ (algebraMap ℂ (MvPolynomial σ ℂ)) _ (fun r => MvPolynomial.isHomogeneous_C _ r) hg
  rw [one_mul] at key
  unfold lsub
  rw [MvPolynomial.aeval_def]
  exact key

variable [DecidableEq σ]

theorem exists_equiv {M : Matrix σ σ ℂ} (h : M * Mᴴ = 1) :
    ∃ ς : MvPolynomial σ ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ, Graded ς ∧ (∀ P Q, fockIp (ς P) (ς Q) = fockIp P Q) ∧
      ∀ P, ς P = lsub M P := by
  have h' : Mᴴ * M = 1 := mul_eq_one_comm.mp h
  have back : ∀ P, lsub M (lsub Mᴴ P) = P := fun P => by
    rw [← AlgHom.comp_apply, ← lsub_mul, h, lsub_one]; rfl
  have forth : ∀ P, lsub Mᴴ (lsub M P) = P := fun P => by
    rw [← AlgHom.comp_apply, ← lsub_mul, h', lsub_one]; rfl
  refine ⟨{ (lsub M).toLinearMap with invFun := lsub Mᴴ, left_inv := forth, right_inv := back }, ?_, ?_,
    fun P => rfl⟩
  · intro d P
    change (lsub M P).IsHomogeneous d ↔ P.IsHomogeneous d
    refine ⟨fun hP => ?_, fun hP => lsub_homog M hP⟩
    simpa only [forth] using lsub_homog Mᴴ hP
  · intro P Q
    change fockIp (lsub M P) (lsub M Q) = fockIp P Q
    rw [fockIp_eq, fockIp_eq, fockL_lsub_adj, forth]

theorem unitary_mix {N : Matrix σ σ ℂ} (h : N * Nᴴ = 1) (e e' : σ → Bool) (he : ∀ w v, N w v ≠ 0 → e w = e' v) :
    (Matrix.of fun w v => if e w then N w v else star (N w v)) *
      (Matrix.of fun w v => if e w then N w v else star (N w v))ᴴ = 1 := by
  ext w w'
  have hww := congrFun (congrFun h w) w'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply] at hww ⊢
  by_cases hw : e w = e w'
  · cases hb : e w with
    | true =>
      have hb' : e w' = true := by rw [← hw]; exact hb
      simp only [hb', if_true]
      exact hww
    | false =>
      have hb' : e w' = false := by rw [← hw]; exact hb
      simp only [hb', Bool.false_eq_true, if_false, star_star]
      have hs := congrArg star hww
      rw [star_sum] at hs
      simp only [star_mul', star_star] at hs
      rw [hs]
      split_ifs <;> simp
  · have hne : w ≠ w' := fun hh => hw (by rw [hh])
    rw [if_neg hne]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases h1 : N w v = 0
    · simp [h1]
    · have h3 : N w' v = 0 := by
        by_contra h3
        exact hw ((he w v h1).trans (he w' v h3).symm)
      simp [h3]

end Pol

section Mat

variable {m n : ℕ}

theorem cartan_of_frame {G s fr : Mn n} {ε : Fin n → Bool} (h : IsFrameOf G s ε fr) : IsCartanInv G s := by
  obtain ⟨hu, hG, hs⟩ := h
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hu
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Jm_mul_Jm ε
  have hi : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hd
  have hi' : fr⁻¹ * fr = 1 := Matrix.nonsing_inv_mul fr hd
  have hGs : G * s = frᴴ * fr := by
    rw [← hG, hs]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc fr fr⁻¹, hi, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJ,
      Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc fr fr⁻¹, hi, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJ,
      Matrix.one_mul, hi']
  · have hc : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hi, Matrix.conjTranspose_one]
    rw [Matrix.mul_assoc, hGs, hs, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conj, ← hG]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (fr⁻¹)ᴴ frᴴ, hc, Matrix.one_mul]
  · rw [hGs]
    simpa using (Matrix.PosDef.one (n := Fin n) (R := ℂ)).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_iff_isUnit.mpr hu)

theorem frame_eigen {G s fr : Mn n} {ε : Fin n → Bool} (h : IsFrameOf G s ε fr) :
    IsUnit fr⁻¹ ∧ s * fr⁻¹ = fr⁻¹ * Formalism.REAL.Jm ε := by
  obtain ⟨hu, -, hs⟩ := h
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hu
  refine ⟨Matrix.isUnit_nonsing_inv_iff.mpr hu, ?_⟩
  rw [hs, Matrix.mul_assoc, Matrix.mul_nonsing_inv fr hd, Matrix.mul_one]

theorem adapted_eq {G s fr B : Mn n} {ε : Fin n → Bool} (h : IsFrameOf G s ε fr) (hB : IsAdapted G s B) :
    ∃ (u : Mn n) (ε' : Fin n → Bool), B = fr⁻¹ * u ∧ uᴴ * u = 1 ∧ ∀ a i, u a i ≠ 0 → ε a = ε' i := by
  obtain ⟨hu, hG, hs⟩ := h
  obtain ⟨ε', hBG, hsB⟩ := hB
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hu
  have hJu : Formalism.REAL.Jm ε * (fr * B) = fr * B * Formalism.REAL.Jm ε' := by
    have key : fr * (s * B) = fr * (B * Formalism.REAL.Jm ε') := by rw [hsB]
    rw [hs] at key
    simp only [Matrix.mul_assoc] at key
    rw [← Matrix.mul_assoc fr fr⁻¹, Matrix.mul_nonsing_inv fr hd, Matrix.one_mul] at key
    rw [key, Matrix.mul_assoc]
  have hGu : (fr * B)ᴴ * Formalism.REAL.Jm ε * (fr * B) = Formalism.REAL.Jm ε' := by
    rw [← hBG, ← hG, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  refine ⟨fr * B, ε', ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul fr hd, Matrix.one_mul]
  · calc (fr * B)ᴴ * (fr * B) = (fr * B)ᴴ * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * (fr * B) := by
          rw [Jm_mul_Jm, Matrix.mul_one]
      _ = (fr * B)ᴴ * Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * (fr * B)) := by simp only [Matrix.mul_assoc]
      _ = (fr * B)ᴴ * Formalism.REAL.Jm ε * (fr * B) * Formalism.REAL.Jm ε' := by
          rw [hJu]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGu, Jm_mul_Jm]
  · intro a i hai
    have key := congrFun (congrFun hJu a) i
    unfold Formalism.REAL.Jm at key
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at key
    rcases h1 : ε a <;> rcases h2 : ε' i <;> simp only [h1, h2, Bool.false_eq_true, if_true, if_false] at key ⊢
    all_goals first
      | exact absurd (by linear_combination -key / 2) hai
      | exact absurd (by linear_combination key / 2) hai

theorem cplxO_unitMap {s B : Mn n} {t B' : Mn m} {ε : Fin n → Bool} {ε' : Fin m → Bool} (hu : IsUnit B)
    (hs : s * B = B * Formalism.REAL.Jm ε) (ht : t * B' = B' * Formalism.REAL.Jm ε') (a : Fin m) (b : Fin n) :
    cplxO s t (unitMap B B' a b) = (Complex.I * if (ε' a == ε b) then 1 else -1) • unitMap B B' a b := by
  have hd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hu
  have hs' : B⁻¹ * s = Formalism.REAL.Jm ε * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * (s * B) * B⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv B hd, Matrix.mul_one]
      _ = Formalism.REAL.Jm ε * B⁻¹ := by
          rw [hs]; simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc B⁻¹ B, Matrix.nonsing_inv_mul B hd, Matrix.one_mul]
  have hE : Formalism.REAL.Jm ε' * Matrix.single a b (1 : ℂ) * Formalism.REAL.Jm ε =
      (if (ε' a == ε b) then 1 else -1 : ℂ) • Matrix.single a b 1 := by
    ext i j
    unfold Formalism.REAL.Jm
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hij : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := hij
      cases ε' a <;> cases ε b <;> simp
    · simp [hij]
  have hT : t * (B' * Matrix.single a b (1 : ℂ) * B⁻¹) * s =
      B' * (Formalism.REAL.Jm ε' * Matrix.single a b (1 : ℂ) * Formalism.REAL.Jm ε) * B⁻¹ := by
    simp only [Matrix.mul_assoc]
    rw [hs', ← Matrix.mul_assoc t B', ht]
    simp only [Matrix.mul_assoc]
  unfold cplxO unitMap
  rw [hT, hE, Matrix.mul_smul, Matrix.smul_mul, smul_smul]

end Mat

section Theta

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {sS : Mn S.rank} {sT : Mn T.rank}
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
include hψ hθ hf

theorem aPlus_add_dir (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (z + z') f =
      Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) z f + Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) z' f := by
  have hc : cplxO sS sT (z + z') = cplxO sS sT z + cplxO sS sT z' := by
    unfold cplxO
    rw [Matrix.mul_add, Matrix.add_mul, smul_add]
  rw [GlobalTheory.FockSubst.aPlus_eq, GlobalTheory.FockSubst.aPlus_eq, GlobalTheory.FockSubst.aPlus_eq, hc,
    (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ z).2.2.1, (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.1]
  simp only [smul_add]
  abel

theorem aPlus_sum_dir {ι : Type} (t : Finset ι) (z : ι → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (∑ i ∈ t, z i) f =
      ∑ i ∈ t, Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (z i) f := by
  classical
  have h0 : Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) 0 f = 0 := by
    have key := aPlus_add_dir (sS := sS) (sT := sT) hψ hθ τ hf (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) 0
    rw [add_zero] at key
    simpa using key
  refine Finset.induction_on t (by simpa using h0) ?_
  intro i t hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, aPlus_add_dir (sS := sS) (sT := sT) hψ hθ τ hf, ih]

theorem aPlus_smul_dir (e : Bool) (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (hz : cplxO sS sT z = (Complex.I * if e then 1 else -1) • z) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (c • z) f =
      (if e then c else star c) • Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) z f := by
  have hJc : cplxO sS sT (c • z) = c • cplxO sS sT z := by
    unfold cplxO
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  have hre := Complex.re_add_im c
  cases e
  · simp only [Bool.false_eq_true, if_false, mul_neg, mul_one] at hz ⊢
    have hst : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [GlobalTheory.FockSubst.aPlus_eq, GlobalTheory.FockSubst.aPlus_eq, hJc, hz, smul_smul,
      GlobalTheory.FockBasis.dRho_smul_dir hψ hθ τ hf c z, GlobalTheory.FockBasis.dRho_smul_dir hψ hθ τ hf (c * -Complex.I) z,
      GlobalTheory.FockBasis.dRho_smul_dir hψ hθ τ hf (-Complex.I) z]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im]
    push_cast
    generalize Datum.dRho (heisO ψ S T) θ τ z f x = A
    generalize Datum.dRho (heisO ψ S T) θ τ (Complex.I • z) f x = B
    generalize ((fockScale D τ : ℂ))⁻¹ = k
    linear_combination (k * (c.im : ℂ) * B) * Complex.I_sq - (k * (A + Complex.I * B)) * hst
  · simp only [if_true, mul_one] at hz ⊢
    rw [GlobalTheory.FockSubst.aPlus_eq, GlobalTheory.FockSubst.aPlus_eq, hJc, hz, smul_smul,
      GlobalTheory.FockBasis.dRho_smul_dir hψ hθ τ hf c z, GlobalTheory.FockBasis.dRho_smul_dir hψ hθ τ hf (c * Complex.I) z]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    push_cast
    generalize Datum.dRho (heisO ψ S T) θ τ z f x = A
    generalize Datum.dRho (heisO ψ S T) θ τ (Complex.I • z) f x = B
    generalize ((fockScale D τ : ℂ))⁻¹ = k
    linear_combination (k * (c.im : ℂ) * B) * Complex.I_sq + (k * (A - Complex.I * B)) * hre

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis Complex in

theorem aPlus_comm_at (hS : IsCartanInv (gramAt D S τ) sS) (hT : IsCartanInv (gramAt D T τ) sT)
    (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) z (Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) z' f) =
    Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) z' (Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) z f) := by
  by_cases hk : ((fockScale D τ : ℝ) : ℂ) = 0
  · simp only [GlobalTheory.FockIndep.aPlus_eq, hk, _root_.inv_zero, zero_smul]
  have th : ∀ w g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (Datum.dRho (heisO ψ S T) θ τ w g) :=
    fun w g hg => by
      have e : Datum.dRho (heisO ψ S T) θ τ w g = (1 / 2 : ℂ) • (Datum.annih (heisO ψ S T) θ τ (cplxO sS sT) w g +
          ((fockScale D τ : ℝ) : ℂ) • Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) w g) := by
        rw [GlobalTheory.FockIndep.aPlus_eq, smul_smul, mul_inv_cancel₀ hk, one_smul]
        unfold Datum.annih
        funext x
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact theta_smul _ (theta_add (GlobalTheory.FockIndep.annih_theta hψ hθ τ _ w hg)
        (theta_smul _ (GlobalTheory.FockIndep.aPlus_theta hψ hθ τ _ w hg)))
  have L : ∀ w g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → ∀ a b : ℂ,
      Datum.dRho (heisO ψ S T) θ τ w (a • (g + b • g')) =
        a • (Datum.dRho (heisO ψ S T) θ τ w g + b • Datum.dRho (heisO ψ S T) θ τ w g') := by
    intro w g g' hg hg' a b
    rw [GlobalTheory.FockIndep.dRho_smul hψ hθ τ w a (theta_add hg (theta_smul b hg')),
      GlobalTheory.FockIndep.dRho_add hψ hθ τ w hg (theta_smul b hg'), GlobalTheory.FockIndep.dRho_smul hψ hθ τ w b hg']
  obtain ⟨hss, hsG, -⟩ := id hS
  obtain ⟨hts, hHt, -⟩ := id hT
  have h1 : sSᴴ * sSᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hss, Matrix.conjTranspose_one]
  have hGi : sS * (gramAt D S τ)⁻¹ * sSᴴ = (gramAt D S τ)⁻¹ := by
    calc sS * (gramAt D S τ)⁻¹ * sSᴴ = (sSᴴ * (gramAt D S τ) * sS)⁻¹ := by
          rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hss, Matrix.inv_eq_left_inv h1,
            Matrix.mul_assoc]
      _ = (gramAt D S τ)⁻¹ := by rw [hsG]
  have hA : (gramAt D S τ)⁻¹ * sSᴴ = sS * (gramAt D S τ)⁻¹ := by
    calc (gramAt D S τ)⁻¹ * sSᴴ = (sS * (gramAt D S τ)⁻¹ * sSᴴ) * sSᴴ := by rw [hGi]
      _ = sS * (gramAt D S τ)⁻¹ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hB : sTᴴ * (gramAt D T τ) = (gramAt D T τ) * sT := by
    calc sTᴴ * (gramAt D T τ) = sTᴴ * (gramAt D T τ) * (sT * sT) := by rw [hts, Matrix.mul_one]
      _ = (sTᴴ * (gramAt D T τ) * sT) * sT := by simp only [Matrix.mul_assoc]
      _ = (gramAt D T τ) * sT := by rw [hHt]
  have hI : I * star I = 1 := by apply Complex.ext <;> simp
  have hsI : star I = -I := by apply Complex.ext <;> simp
  have tr1 : ∀ y y' : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      ((gramAt D S τ)⁻¹ * (cplxO sS sT y')ᴴ * (gramAt D T τ) * cplxO sS sT y).trace = ((gramAt D S τ)⁻¹ * y'ᴴ * (gramAt D T τ) * y).trace := by
    intro y y'
    unfold cplxO
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_smul, smul_eq_mul, hI, one_mul]
    have e : (gramAt D S τ)⁻¹ * (sSᴴ * (y'ᴴ * sTᴴ)) * (gramAt D T τ) * (sT * y * sS) =
        ((gramAt D S τ)⁻¹ * sSᴴ * y'ᴴ * (sTᴴ * (gramAt D T τ) * sT) * y) * sS := by
      simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm]
    have e2 : sS * ((gramAt D S τ)⁻¹ * sSᴴ * y'ᴴ * (sTᴴ * (gramAt D T τ) * sT) * y) =
        sS * (gramAt D S τ)⁻¹ * sSᴴ * y'ᴴ * (sTᴴ * (gramAt D T τ) * sT) * y := by
      simp only [Matrix.mul_assoc]
    rw [e2, hGi, hHt]
  have tr2 : ∀ y y' : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      ((gramAt D S τ)⁻¹ * (cplxO sS sT y')ᴴ * (gramAt D T τ) * y).trace = -I * ((gramAt D S τ)⁻¹ * y'ᴴ * (gramAt D T τ) * (sT * y * sS)).trace := by
    intro y y'
    unfold cplxO
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hsI]
    congr 1
    have e : (gramAt D S τ)⁻¹ * (sSᴴ * (y'ᴴ * sTᴴ)) * (gramAt D T τ) * y = sS * ((gramAt D S τ)⁻¹ * y'ᴴ * (gramAt D T τ) * (sT * y)) := by
      calc (gramAt D S τ)⁻¹ * (sSᴴ * (y'ᴴ * sTᴴ)) * (gramAt D T τ) * y = ((gramAt D S τ)⁻¹ * sSᴴ) * y'ᴴ * (sTᴴ * (gramAt D T τ)) * y := by
            simp only [Matrix.mul_assoc]
        _ = sS * ((gramAt D S τ)⁻¹ * y'ᴴ * (gramAt D T τ) * (sT * y)) := by rw [hA, hB]; simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have tr3 : ∀ y y' : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      ((gramAt D S τ)⁻¹ * y'ᴴ * (gramAt D T τ) * cplxO sS sT y).trace = I * ((gramAt D S τ)⁻¹ * y'ᴴ * (gramAt D T τ) * (sT * y * sS)).trace := by
    intro y y'
    unfold cplxO
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have o1 : ((GlobalTheory.FockIndep.omDir S T τ (cplxO sS sT z) τ (cplxO sS sT z') : ℝ) : ℂ) =
      (GlobalTheory.FockIndep.omDir S T τ z τ z' : ℝ) := by
    unfold GlobalTheory.FockIndep.omDir
    rw [if_pos rfl, if_pos rfl, tr1]
  have o2 : ((GlobalTheory.FockIndep.omDir S T τ z τ (cplxO sS sT z') : ℝ) : ℂ) =
      -((GlobalTheory.FockIndep.omDir S T τ (cplxO sS sT z) τ z' : ℝ) : ℂ) := by
    unfold GlobalTheory.FockIndep.omDir
    rw [if_pos rfl, if_pos rfl, tr2, tr3, neg_mul, mul_neg, Complex.neg_re]
    push_cast
    ring
  simp only [GlobalTheory.FockIndep.aPlus_eq]
  rw [L z _ _ (th z' f hf) (th _ f hf), L (cplxO sS sT z) _ _ (th z' f hf) (th _ f hf),
    L z' _ _ (th z f hf) (th _ f hf), L (cplxO sS sT z') _ _ (th z f hf) (th _ f hf)]
  rw [GlobalTheory.FockIndep.dRho_comm hψ hθ τ z τ z' hf, GlobalTheory.FockIndep.dRho_comm hψ hθ τ z τ (cplxO sS sT z') hf,
    GlobalTheory.FockIndep.dRho_comm hψ hθ τ (cplxO sS sT z) τ z' hf,
    GlobalTheory.FockIndep.dRho_comm hψ hθ τ (cplxO sS sT z) τ (cplxO sS sT z') hf]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹) * (-(2 * Real.pi * I)) * f x) * o1 +
    (-I * ((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹) * (-(2 * Real.pi * I)) * f x) * o2 +
    (((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹) * (-(2 * Real.pi * I)) * f x *
      ((GlobalTheory.FockIndep.omDir S T τ (cplxO sS sT z) τ (cplxO sS sT z') : ℝ) : ℂ)) * Complex.I_sq

end Theta

theorem ptAt_basis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ BS BT, IsAdapted (gramAt D S τ) sS BS → IsAdapted (gramAt D T τ) sT BT → ∃ ς : LPol T.rank S.rank ≃ₗ[ℂ] LPol T.rank S.rank, Graded ς ∧ (∀ P Q, fockIp (ς P) (ς Q) = fockIp P Q) ∧ ∀ f, IsThetaFunO ψ S T f → ∀ P, ptAt ψ θ S T τ sS sT BS BT f P = ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f (ς P) := by
  intro D ψ θ S T τ hψ hθ sS frS εS sT frT εT hfS hfT BS BT hBS hBT
  obtain ⟨uS, εS', rfl, huS, hsgS⟩ := adapted_eq hfS hBS
  obtain ⟨uT, εT', rfl, huT, hsgT⟩ := adapted_eq hfT hBT
  have hcS := cartan_of_frame hfS
  have hcT := cartan_of_frame hfT
  obtain ⟨hiS, heS⟩ := frame_eigen hfS
  obtain ⟨hiT, heT⟩ := frame_eigen hfT
  have hinv : uS⁻¹ = uSᴴ := Matrix.inv_eq_left_inv huS
  have hT1 : ∀ a a', ∑ i, uT a i * star (uT a' i) = if a = a' then 1 else 0 := by
    intro a a'
    have hTT : uT * uTᴴ = 1 := mul_eq_one_comm.mp huT
    have key := congrFun (congrFun hTT a) a'
    simpa [Matrix.mul_apply, Matrix.one_apply] using key
  have hS1 : ∀ b b', ∑ j, uS⁻¹ j b * star (uS⁻¹ j b') = if b = b' then 1 else 0 := by
    intro b b'
    rw [hinv]
    have hSS : uS * uSᴴ = 1 := mul_eq_one_comm.mp huS
    have key := congrFun (congrFun hSS b') b
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, star_star] at key ⊢
    rw [Finset.sum_congr rfl fun j _ => mul_comm (star (uS b j)) (uS b' j), key]
    rcases eq_or_ne b b' with h | h
    · subst h; simp
    · simp [h, h.symm]
  let N0 : Matrix (Fin T.rank × Fin S.rank) (Fin T.rank × Fin S.rank) ℂ :=
    Matrix.of fun w v => uT w.1 v.1 * uS⁻¹ v.2 w.2
  have hN0 : N0 * N0ᴴ = 1 := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [N0, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      star_mul']
    have e : ∀ i j, uT a i * uS⁻¹ j b * (star (uT a' i) * star (uS⁻¹ j b')) =
        (uT a i * star (uT a' i)) * (uS⁻¹ j b * star (uS⁻¹ j b')) := fun i j => by ring
    simp only [e]
    rw [← Finset.sum_mul_sum, hT1, hS1, Matrix.one_apply]
    by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> simp [h1, h2]
  have he : ∀ w v, N0 w v ≠ 0 → (εT w.1 == εS w.2) = (εT' v.1 == εS' v.2) := by
    intro w v hwv
    simp only [N0, hinv, Matrix.of_apply, Matrix.conjTranspose_apply] at hwv
    have h1 : uT w.1 v.1 ≠ 0 := left_ne_zero_of_mul hwv
    have h2 : uS w.2 v.2 ≠ 0 := fun h0 => right_ne_zero_of_mul hwv (by rw [h0, star_zero])
    rw [hsgT _ _ h1, hsgS _ _ h2]
  have hN := unitary_mix hN0 (fun w => εT w.1 == εS w.2) (fun v => εT' v.1 == εS' v.2) he
  obtain ⟨ς, hgr, hip, hς⟩ := exists_equiv hN
  refine ⟨ς, hgr, hip, fun f hf P => ?_⟩
  have pls : ∀ (A A' : Fin T.rank × Fin S.rank → (WO S T → ℂ) → (WO S T → ℂ)),
      (∀ i g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A i g)) →
      (∀ i g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A' i g)) →
      (∀ i j g, IsThetaFunO ψ S T g → A i (A j g) = A j (A i g)) →
      (∀ i j g, IsThetaFunO ψ S T g → A' i (A' j g) = A' j (A' i g)) →
      (∀ i g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → A i (g + g') = A i g + A i g') →
      (∀ i g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → A' i (g + g') = A' i g + A' i g') →
      (∀ i (a : ℂ) g, IsThetaFunO ψ S T g → A i (a • g) = a • A i g) →
      (∀ i (a : ℂ) g, IsThetaFunO ψ S T g → A' i (a • g) = a • A' i g) →
      ∀ N : Matrix (Fin T.rank × Fin S.rank) (Fin T.rank × Fin S.rank) ℂ,
      (∀ v g, IsThetaFunO ψ S T g → A' v g = ∑ w, N w v • A w g) →
      ∀ Q, pureTensorL A' f Q = pureTensorL A f (lsub N Q) := by
    intro A A' hA hA' hc hc' Aadd Aadd' Asm Asm' N hN Q
    have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
      fun g g' hg hg' => GlobalTheory.OrientedHeis.theta_add hg hg'
    have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
      fun a g hg => GlobalTheory.OrientedHeis.theta_smul a hg
    have h0 : ∀ B : Fin T.rank × Fin S.rank → (WO S T → ℂ) → (WO S T → ℂ), ∀ a : ℂ,
        pureTensorL B f (MvPolynomial.C a) = a • f := by
      intro B a
      have e1 : MvPolynomial.C a = a • (1 : MvPolynomial (Fin T.rank × Fin S.rank) ℂ) := by
        rw [MvPolynomial.smul_eq_C_mul, mul_one]
      rw [e1, map_smul, GlobalTheory.FockIndep.pure_one]
    induction Q using MvPolynomial.induction_on with
    | C a =>
      have e2 : lsub N (MvPolynomial.C a) = MvPolynomial.C a := by
        unfold lsub
        rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
      rw [e2, h0, h0]
    | add Q R hQ hR => rw [map_add, map_add, map_add, hQ, hR]
    | mul_X Q v hQ =>
      rw [mul_comm, GlobalTheory.FockIndep.pure_X_mul hadd hsm hA' hc' Aadd' Asm' hf, hQ,
        hN v _ (GlobalTheory.FockIndep.pure_mem hadd hsm hA hf _), map_mul, lsub_X, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [mul_assoc, ← MvPolynomial.smul_eq_C_mul, map_smul, GlobalTheory.FockIndep.pure_X_mul hadd hsm hA hc Aadd Asm hf]
  rw [hς]
  unfold ptAt
  have a0 : ∀ (w : Fin T.rank × Fin S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T
      (Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w.1 w.2) g) :=
    fun w g hg => GlobalTheory.FockIndep.aPlus_theta hψ hθ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w.1 w.2) hg
  have c0 : ∀ (w w' : Fin T.rank × Fin S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w.1 w.2)
        (Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w'.1 w'.2) g) =
      Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w'.1 w'.2)
        (Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w.1 w.2) g) :=
    fun w w' g hg => aPlus_comm_at hψ hθ τ hg hcS hcT _ _
  have d0 : ∀ (w : Fin T.rank × Fin S.rank) (g g' : WO S T → ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w.1 w.2) (g + g') =
        Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w.1 w.2) g +
          Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w.1 w.2) g' :=
    fun w g g' hg hg' => GlobalTheory.FockIndep.aPlus_add hψ hθ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w.1 w.2) hg hg'
  have m0 : ∀ (w : Fin T.rank × Fin S.rank) (a : ℂ) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w.1 w.2) (a • g) =
        a • Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w.1 w.2) g :=
    fun w a g hg => GlobalTheory.FockIndep.aPlus_smul hψ hθ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ w.1 w.2) a hg
  have a1 : ∀ (w : Fin T.rank × Fin S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T
      (Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w.1 w.2) g) :=
    fun w g hg => GlobalTheory.FockIndep.aPlus_theta hψ hθ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w.1 w.2) hg
  have c1 : ∀ (w w' : Fin T.rank × Fin S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w.1 w.2)
        (Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w'.1 w'.2) g) =
      Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w'.1 w'.2)
        (Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w.1 w.2) g) :=
    fun w w' g hg => aPlus_comm_at hψ hθ τ hg hcS hcT _ _
  have d1 : ∀ (w : Fin T.rank × Fin S.rank) (g g' : WO S T → ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w.1 w.2) (g + g') =
        Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w.1 w.2) g +
          Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w.1 w.2) g' :=
    fun w g g' hg hg' => GlobalTheory.FockIndep.aPlus_add hψ hθ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w.1 w.2) hg hg'
  have m1 : ∀ (w : Fin T.rank × Fin S.rank) (a : ℂ) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w.1 w.2) (a • g) =
        a • Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w.1 w.2) g :=
    fun w a g hg => GlobalTheory.FockIndep.aPlus_smul hψ hθ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) w.1 w.2) a hg
  refine pls (fun (k : Fin T.rank × Fin S.rank) =>
      Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ k.1 k.2))
    (fun (k : Fin T.rank × Fin S.rank) =>
      Datum.aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap (frS⁻¹ * uS) (frT⁻¹ * uT) k.1 k.2))
    a0 a1 c0 c1 d0 d1 m0 m1 _ ?_ P
  intro v g hg
  rw [GlobalTheory.FockBasis.unitMap_mul, aPlus_sum_dir hψ hθ τ hg, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [aPlus_sum_dir hψ hθ τ hg]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [aPlus_smul_dir hψ hθ τ hg _ _ _ (cplxO_unitMap hiS heS heT a b)]
  simp only [Matrix.of_apply, N0]

end GlobalTheory.ArchRec.BasisChange

end
