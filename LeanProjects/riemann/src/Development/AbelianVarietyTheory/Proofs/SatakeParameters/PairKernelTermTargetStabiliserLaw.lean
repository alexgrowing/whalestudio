import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyAt0PolDEquivariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartitionStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

open GlobalTheory.KerWt

theorem applyAt0_const_mul (D : D7) {N N' : ℕ} (P : MvPolynomial (GL3Theta.Idx D N N') ℂ) (k : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (hG : Differentiable ℂ G) : GL3Theta.applyAt0 D P (fun z => k * G z) = k * GL3Theta.applyAt0 D P G := by
  exact (GlobalTheory.NormSum.applyAt0_minorPol_linear D N N' (fun _ => 0) G hG).2.2.1 k P

theorem applyAt0_polD_eigen (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (y' γ : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (k : ℂ) (hγ : ∀ τ, (γ τ).det ≠ 0)
    (hG : Differentiable ℂ G) (hk : ∀ z : TaylorLogMetric.VC D N N', G (fun τ => (γ τ * Matrix.of (z τ) : Matrix _ _ ℂ)) = k * G z) :
    GL3Theta.applyAt0 D (GL3Theta.polD D s Q (fun τ => γ τ * y' τ)) G = k * GL3Theta.applyAt0 D (GL3Theta.polD D s Q y') G := by
  have h := GlobalTheory.ClassSumEquiv.applyAt0_polD_equivariant D N N' s Q y' γ (fun _ => 1) (fun z => k * G z) hγ (hG.const_mul k)
  have e1 : (fun z : TaylorLogMetric.VC D N N' => k * G (fun τ => ((γ τ)⁻¹ * Matrix.of (z τ) * (1 : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N') (Fin N) ℂ))) = G := by
    funext z
    refine (hk _).symm.trans (congrArg G (funext fun τ => ?_))
    have : (γ τ * ((γ τ)⁻¹ * Matrix.of (z τ) * (1 : Matrix (Fin N) (Fin N) ℂ)) : Matrix (Fin N') (Fin N) ℂ) = Matrix.of (z τ) := by
      rw [Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ (hγ τ).isUnit]
    exact this
  have e2 : (MvPolynomial.aeval (fun k : GL3Theta.FrV D N => ∑ a : Fin N, MvPolynomial.C ((1 : Matrix (Fin N) (Fin N) ℂ) k.2.1 a) *
      (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (GL3Theta.FrV D N) ℂ)) Q) = Q := by
    have : (fun k : GL3Theta.FrV D N => ∑ a : Fin N, MvPolynomial.C ((1 : Matrix (Fin N) (Fin N) ℂ) k.2.1 a) *
      (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (GL3Theta.FrV D N) ℂ)) = MvPolynomial.X := by
      funext k
      rw [Finset.sum_eq_single k.2.1]
      · simp
      · intro b _ hb
        simp [Matrix.one_apply_ne hb.symm]
      · simp
    rw [this, MvPolynomial.aeval_X_left_apply]
  beta_reduce at h
  rw [e1, e2, applyAt0_const_mul D _ k G hG] at h
  exact h

theorem lawAt_Kmap : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)), Differentiable ℂ (O.Th i c c') → ∀ g, TermLaw O i c c' g → ∀ f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → LawAt O (i + 1) g (C.Kmap i c c' f) := by
  intro D u C A Pm M O i hi h c c' hd g ⟨hdet, k, hk, hg⟩ f ⟨P, hP, hf⟩ y y' hy
  obtain ⟨n, hw, hn, -, -⟩ := GlobalTheory.T.trueWeight_consecutive_steps_partition D u C A Pm M i hi
  have hs : C.sharp i f = frPoly O i (MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ) := by
    have h1 := mulFun_evG (fr := O.frm i) (fun y => (O.frm_range i hi.le _).1 ⟨y, rfl⟩) (RingHom.id ℂ) _ (C.sSharp i) n hn P
    have e1 : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ) := by
      funext y; simp only [O.frm_de i hi.le]
    rw [e1] at h1
    rw [hf]
    exact h1
  have hQ : MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ ∈ WtPol ℂ (nuT D u i) := by
    have h2 := vv_in_weight ℂ D.what₂.Tau _ (lamTG M i) n (MvPolynomial.map (RingHom.id ℂ) P) (map_mem_VV _ _ P hP)
    have e : (fun τ r => (lamTG M i τ).natW r + n τ) = nuT D u i := by funext τ r; exact hw τ r
    rwa [e] at h2
  generalize MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ = Q at hs hQ
  have hu : ∀ x : C.Y (i + 1), C.unf i c c' (C.sharp i f) x =
      GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) x)) (O.Th i c c') := fun x => by
    rw [hs]
    exact (unfolding_iff_alt D u C O i hi.le _).1 h c c' Q hQ x
  have hK : ∀ x : C.Y (i + 1), C.Kmap i c c' f x = (C.rhoDet i c * C.rhoDet' i c') *
      ((∏ τ, (O.frm (i + 1) x τ).det ^ C.sDiv i τ)⁻¹ *
        GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) x)) (O.Th i c c')) := fun x => by
    rw [← hu x]
    simp only [← O.frm_de (i + 1) hi]
    rfl
  have hdm : ∀ τ, (g.1.map (TaylorLogMetric.embT D τ)).det = TaylorLogMetric.embT D τ g.1.det := fun τ => ((TaylorLogMetric.embT D τ).map_det g.1).symm
  have hne : ∀ τ, (g.1.map (TaylorLogMetric.embT D τ)).det ≠ 0 := fun τ => by
    rw [hdm]; exact (map_ne_zero _).2 hdet
  have hy' : O.frm (i + 1) y = fun τ => g.1.map (TaylorLogMetric.embT D τ) * O.frm (i + 1) y' τ := funext hy
  rw [hK, hK, hy', applyAt0_polD_eigen D _ _ _ Q _ _ _ k hne hd hk, hg]
  simp only [Matrix.det_mul, hdm, mul_zpow, Finset.prod_mul_distrib, zpow_neg, Finset.prod_inv_distrib, mul_inv]
  ring

end GlobalTheory.KerJ
