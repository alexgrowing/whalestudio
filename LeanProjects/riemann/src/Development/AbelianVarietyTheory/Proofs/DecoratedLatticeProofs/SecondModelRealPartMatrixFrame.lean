import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointInfiniteMatricesEqOneOfFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.RealMat

variable {D : D7}

theorem psiT_incA (τ : D.what₂.Tau) (x : D.host.E) : Formalism.IndefR.Eqv.psiT D τ (incA D x) = tauE D τ x := by
  show Formalism.IndefR.Eqv.thetaC D τ ((fstA D.host.F 1) ⊗ₜ[D.host.F] x) = _
  rw [Formalism.IndefR.Eqv.thetaC_tmul]
  simp

theorem embA_cols {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A) :
    HMul.hMul (Formalism.L2.Theta.mt S (embA d o a)) (rat (d.i₀ * o.iA) : Matrix (Fin S.rank) (Fin A.rank) (AE D)) =
      HMul.hMul (rat (d.i₀ * o.iA) : Matrix (Fin S.rank) (Fin A.rank) (AE D)) (Formalism.L2.Theta.mt A a) := by
  have e : (rat (d.i₀ * o.iA) : Mx D S.rank A.rank) = HMul.hMul d.j0 o.jA := rat_mul _ _
  rw [e, embA_apply, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]

theorem embA_cols_at {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A) (τ : D.what₂.Tau) :
    (Formalism.L2.Theta.mt S (embA d o a)).map (Formalism.IndefR.Eqv.psiT D τ) * (d.i₀ * o.iA).map (tauE D τ) =
      (d.i₀ * o.iA).map (tauE D τ) * (Formalism.L2.Theta.mt A a).map (Formalism.IndefR.Eqv.psiT D τ) := by
  have e : (d.i₀ * o.iA).map (tauE D τ) =
      (rat (d.i₀ * o.iA) : Mx D S.rank A.rank).map (Formalism.IndefR.Eqv.psiT D τ) := by
    ext i j
    exact (psiT_incA τ _).symm
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, embA_cols]

theorem act_gen {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hιE : ∀ x : I.E, HEq (ιE x) x) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (hr : (D.sp.Y 0).rank = I.n) (k : GA D (D.sp.Y 0))
    (τ : D.what₂.Tau) {m : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin m) D.host.E) (M : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin m → Fin I.n → I.E) (hx : ∀ i j, C i j = ιE (x j (Fin.cast hr i)))
    (hC : (Formalism.L2.Theta.mt (D.sp.Y 0) k).map (Formalism.IndefR.Eqv.psiT D τ) * C.map (tauE D τ) = C.map (tauE D τ) * M) (b : Fin m) :
    uMat (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).1 (pl.symm τ)) *ᵥ rv I (pl.symm τ) (x b) =
      ∑ i, M i b • rv I (pl.symm τ) (x i) := by
  subst h
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hιE x)
  have key : ∀ τ τ' : D.what₂.Tau, embS D τ = embS D τ' → τ = τ' :=
    fun τ τ' e => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := Equiv.ext fun v => key _ _ (RingHom.ext fun x => by
    have e := hφ v x
    have e2 : embS D (pl v) (ιE x) = embS D (pl v) x := congrArg _ (hι x)
    exact (e2.symm.trans e.symm).trans (SeeReal.phi_inst v x))
  have hcol : ∀ j, (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ (pl.symm τ) (x j i)) =
      fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j := by
    intro j
    funext i
    rw [hφ, Equiv.apply_symm_apply]
    exact (congrArg (tauE D τ) (hx i j)).symm
  subst hpl
  have hT : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)) k =
      Formalism.IndefR.RationalEmbedding.iota D k := rfl
  have hP := Formalism.L2.SG.EvalTIota.P_isUnit_det' (D := D) (Formalism.L2.Host.tauPl D τ)
  have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i (Formalism.IndefR.RationalEmbedding.iota D k) τ
  rw [ContinuousMulEquiv.symm_apply_apply, Formalism.IndefR.Eqv.infMat_thetaC] at hbr
  have hu := SeeReal.eq_of_conj hP hbr.symm
  have hrv : ∀ j, rv (Formalism.L2.SG.InstExistsPf.instOf D) ((Formalism.L2.Host.tauPl D).symm.symm τ) (x j) =
      (Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j := by
    intro j
    rw [← hcol j]
    rfl
  have main : Formalism.L2.SG.EvalTIota.uM' (Formalism.IndefR.RationalEmbedding.iota D k) (Formalism.L2.Host.tauPl D τ) *ᵥ
      ((Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i b) =
      ∑ j, M j b • ((Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j) := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (Formalism.L2.SG.EvalTIota.Pi _), Matrix.mul_nonsing_inv _ hP,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum]
    congr 1
    funext i
    have e := congrFun (congrFun hC i) b
    simp only [Matrix.mul_apply] at e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact e.trans (Finset.sum_congr rfl fun j _ => mul_comm _ _)
  refine (congrArg (fun w => Formalism.L2.SG.EvalTIota.uM' (Formalism.IndefR.RationalEmbedding.iota D k) (Formalism.L2.Host.tauPl D τ) *ᵥ w) (hrv b)).trans ?_
  exact main.trans (Finset.sum_congr rfl fun j _ => congrArg (fun w => M j b • w) (hrv j).symm)

theorem gramQ_isUnit (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : (∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y) ∧ (∀ a, wt (X.eX a) = D.sp.hypE a) ∧
      (∀ a, wt (X.fY a) = D.sp.hypF a) ∧ wt (X.zu u) = D.zmOf u) (v : InfinitePlace X.B.I.F) :
    IsUnit (Formalism.L2.SG.ColDict.gramQ X wt v).det := by
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hQq, -, -, -, hG', hblk⟩ := GlobalTheory.St.qFrame_basis_gram D X u wt hW
  set φ := X.B.I.φ v with hφ
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hGdef
  have hgram : Formalism.L2.SG.ColDict.gramQ X wt v = G.map φ := by
    ext a b
    have h1 := congrFun (congrFun hblk (Sum.inl a)) (Sum.inl b)
    rw [Matrix.fromBlocks_apply₁₁] at h1
    rw [Matrix.map_apply, ← h1]
    simp only [Formalism.L2.SG.ColDict.gramQ, Matrix.of_apply, Formalism.L2.SG.ColDict.rvV]
    have := PI.ScPiFrameW.hJ_rv X.B.I v (X.crd (Formalism.L2.SG.ColDict.qFr wt a)) (X.crd (Formalism.L2.SG.ColDict.qFr wt b))
    refine this.trans ?_
    congr 1
    simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hQq, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdetG : G.det ≠ 0 := by
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.mpr X.B.I.J_det
    have hJinv : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJu
    have hR : Matrix.fromBlocks G 0 0 G' *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      rw [← hblk]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J, hJinv, Matrix.one_mul,
        ← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hd := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fromBlocks_zero₂₁] at hd
    exact left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hd)
  have hm : (G.map φ).det = φ G.det := (RingHom.map_det φ G).symm
  rw [hgram, hm, isUnit_iff_ne_zero, map_ne_zero]
  exact hdetG

end GlobalTheory.Core.Mi.RealMat

open GlobalTheory.Core.Mi.RealMat in

theorem GlobalTheory.Core.Mi.sTil_toH_eq_infM : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (θ : InfFam D), IsInfFam θ → IdE X → B.Adapted tr.wt → ∀ (a : GA D (D.sp.X 0)) (τ : D.what₂.Tau), Formalism.L2.SG.ColDict.sTil X tr.wt ((B.toH a).1 : X.B.I.Ginf) τ = GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ := by
  intro D X h u ψ B F tr θ hθ hE hA a τ
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hdetQ := gramQ_isUnit X u tr.wt ⟨tr.wt_isom, tr.wt_e, tr.wt_f, tr.weight_z⟩ (X.pl.symm τ)
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  have hact := act_gen h X.ιE hE X.pl X.φ_eq (rank_eq X h) (embA B.d B.o a) τ (B.d.i₀ * B.o.iA) _
    (fun j => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast hn j))) hA (embA_cols_at B.d B.o a τ)
  have hlin : ∀ b, uMat (((B.toH a).1 : X.B.I.Ginf) (X.pl.symm τ)) *ᵥ
      Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt b) =
      ∑ i, GlobalTheory.AdForm.infM (Formalism.IndefR.Eqv.thetaC D) (D.sp.X 0) hn a τ i b •
        Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt i) := by
    intro b
    refine (hact (Fin.cast hn.symm b)).trans ?_
    exact Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl
  have hM : (Matrix.of fun a' b => hJ (X.B.I.ε (X.pl.symm τ))
      (Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt a'))
      (uMat (((B.toH a).1 : X.B.I.Ginf) (X.pl.symm τ)) *ᵥ
        Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt b))) =
      Formalism.L2.SG.ColDict.gramQ X tr.wt (X.pl.symm τ) * GlobalTheory.AdForm.infM (Formalism.IndefR.Eqv.thetaC D) (D.sp.X 0) hn a τ := by
    ext a' b
    rw [Matrix.of_apply, hlin, Matrix.mul_apply]
    simp only [hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, Formalism.L2.SG.ColDict.gramQ,
      Matrix.of_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  show (Formalism.L2.SG.ColDict.gramQ X tr.wt (X.pl.symm τ))⁻¹ * _ = _
  rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetQ, Matrix.one_mul]

end
