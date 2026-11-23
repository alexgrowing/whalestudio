import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormEqOrientedHomSymplecticForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtThetaTransformHeisenbergRealLine

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaDer

theorem schr_comp_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' Φ) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') Φ x := by
  have hh : ⅟(2 : R) + ⅟(2 : R) = 1 := by rw [← two_mul, mul_invOf_self]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, add_assoc]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * hh

theorem exists_equiv {A : Type} [CommRing A] {m k d : ℕ} {G H : Matrix (Fin m) (Fin m) A} (hHG : H * G = 1)
    (hGH : G * H = 1) (e : Fin k ≃ Fin d) :
    ∃ T : Matrix (Fin m) (Fin k) A ≃+ Matrix (Fin d) (Fin m) A,
      (∀ u, T u = uᵀ.submatrix e.symm id * G) ∧ ∀ x, T.symm x = ((x * H)ᵀ).submatrix id e := by
  refine ⟨{ toFun := fun u => uᵀ.submatrix e.symm id * G
            invFun := fun x => ((x * H)ᵀ).submatrix id e
            left_inv := fun u => ?_
            right_inv := fun x => ?_
            map_add' := fun u v => ?_ }, fun u => rfl, fun x => rfl⟩
  · ext i j
    simp [Matrix.mul_assoc, hGH]
  · simp [Matrix.transpose_submatrix, Matrix.submatrix_submatrix, Matrix.mul_assoc, hHG]
  · simp [Matrix.transpose_add, Matrix.submatrix_add, Matrix.add_mul]

private theorem rho_add_twisted_operators {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar R ℂ) (p q : W)
    (Φ : (κ → R) → ℂ) (z : κ → R) :
    co.rho ψ (p + q) Φ z = ψ (-(⅟(2 : R) * B p q)) * co.rho ψ p (co.rho ψ q Φ) z := by
  simp only [GlobalTheory.WeilM.Darboux.rho]
  rw [schr_comp_apply, ← co.form, map_add, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]

set_option maxHeartbeats 6400000 in
private theorem tendsto_add_smul_punctured_of_differentiableAt {D : D7} {n d m : ℕ} (u₀ : Matrix (Fin n) (Fin d) (AE D)) (e' : Fin d ≃ Fin m)
    (G : Matrix (Fin n) (Fin n) (AE D)) :
    Continuous fun t : ℝ => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e'.symm id * G := by
  have c0 : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F) := GlobalTheory.ThetaLineDeriv.continuous_realAd
  have c1 : Continuous fun t : ℝ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀ := c0.smul continuous_const
  exact (c1.matrix_transpose.matrix_submatrix _ _).matrix_mul continuous_const

private theorem fin_realAd_smul_eq_zero {D : D7} (t : ℝ) (a : AE D) :
    finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • a) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have h0 : finPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t)) = 0 := by
    show finPart D ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    have hs : sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 := rfl
    simp only [Formalism.L2.Theta.finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, hs,
      TensorProduct.zero_tmul]
  rw [h0, zero_mul]

set_option maxHeartbeats 1600000 in

theorem thO_pure_deriv {D : D7} (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hVJ : Vs.J = -S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : ∀ i j, D.sp.cm.sig (Vs.J j i) = Vs.J i j)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ)
    (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin S.rank × Fin d → Fv D.host.F v) → ℂ)
    (u₀ : Matrix (Fin S.rank) (Fin d) (AE D)) (g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (hact : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ u₀) g g₁)
    (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    ∃ L : ℝ →+ WO S X, Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧
      GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) =
        fun x => deriv (fun t : ℝ => heisO Bs.ψ S X (L t)
          (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) x) 0 := by
  classical
  have hTR : NumberField.IsTotallyReal D.host.F := hBs.cm.1
  have hCh : IsCharAF D.host.F Bs.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hBs.std
  have hdet : IsUnit S.gram.det := isUnit_iff_ne_zero.mpr (gram_det_ne S)
  have hinc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet]
    simp
  have hinc' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet]
    simp
  obtain ⟨T, hT, hTs⟩ := exists_equiv (A := AE D) hinc' hinc e
  have hpt : ∀ x, GlobalTheory.TripleRead.ptO S.gram e x = T.symm x := fun x => (hTs x).symm
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F v} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have hΦ := GlobalTheory.TensUniq.pure_mem_schA g φ hφ hstd
  have hΦ' := GlobalTheory.TensUniq.pure_mem_schA g₁ φ hφ hstd
  have hd : ∀ z, HasDerivAt (fun t : ℝ => M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ z) 0 :=
    fun z => hact _ (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφ hstd) z

  have hG : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram)ᵀ := by
    ext i j
    have h1 := hV j i
    rw [hVJ] at h1
    simp only [Matrix.neg_apply, map_neg, neg_inj] at h1
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, inclR, h1]
  have h2 : (⅟(2 : AF D.host.F)) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [show (2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  have hphase : ∀ (x : WO S X) (q : Matrix (Fin S.rank) (Fin d) (AE D)),
      symplOH S X x (T q) = ⅟(2 : AF D.host.F) * GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (T.symm x) q := by
    intro x q
    conv_lhs => rw [← T.apply_symm_apply x]
    have hh := GlobalTheory.SquareAgree.hTens_transpose_mul (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e.symm
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram) (inclR (F := D.host.F) (AF D.host.F) D.host.xi0) hinc' hG (T.symm x) q
    rw [← hT, ← hT] at hh
    have hs := GlobalTheory.WeilSchrodinger.symp_eq_symplO D S X (X.gramᵀ) (D.host.xi0 • S.gram⁻¹) 1 rfl (by rw [one_smul])
      (T (T.symm x)) (T q)
    simp only [symplOH, ← hs, h2, GlobalTheory.WeilM.symp, one_mul, neg_one_mul, map_neg]
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hVJ]
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 • Matrix.reindex e.symm e.symm (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hJW, Matrix.reindex_apply, map_mul]
    have e3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, map_mul]
    have e4 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [e4, e3, hh, e1, e2, map_neg]

  let ln : ℝ →+ Matrix (Fin S.rank) (Fin d) (AE D) :=
    AddMonoidHom.mk' (fun t => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)
      (fun s t => by simp only [GlobalTheory.ThetaLineDeriv.realAd_add, add_smul])
  refine ⟨T.toAddMonoidHom.comp ln, ?_, ?_, ?_⟩
  · have hfun : (fun t => (T.toAddMonoidHom.comp ln) t) =
        fun t => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e.symm id * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram :=
      funext fun t => hT _
    show Continuous fun t => (T.toAddMonoidHom.comp ln) t
    rw [hfun]
    exact tendsto_add_smul_punctured_of_differentiableAt u₀ e _
  · intro t
    show (T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)).map (finPart D) = 0
    rw [hT, Matrix.map_mul]
    have hz : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e.symm id).map (finPart D) = 0 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, fin_realAd_smul_eq_zero,
        Matrix.zero_apply]
    rw [hz, Matrix.zero_mul]
  · funext x
    have hfun : (fun t : ℝ => heisO Bs.ψ S X ((T.toAddMonoidHom.comp ln) t)
        (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) x) =
        fun t => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ (T.symm x)
          (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))) := by
      funext t
      show heisO Bs.ψ S X (T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)) _ x = _
      simp only [heisO, GlobalTheory.TripleRead.thO, hpt, map_add, T.symm_apply_apply]
      rw [show M.co.rho Bs.ψ (T.symm x + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) =
        fun z => Bs.ψ (-(⅟(2 : AF D.host.F) * GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (T.symm x)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀))) *
          M.co.rho Bs.ψ (T.symm x) (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) z
        from funext (rho_add_twisted_operators M.co Bs.ψ _ _ _)]
      simp only [GlobalTheory.WeilM.thetaSum]
      rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul, hphase, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]
    rw [hfun, (GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho M.co Bs.ψ hTR hCh u₀ _ hΦ _ hΦ' hd (T.symm x)).deriv]
    simp only [GlobalTheory.TripleRead.thO, hpt]

theorem thO_pure_deriv_first : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
          (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ)
          (u : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E))
          (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank))), f ∈ Γ.M.Pol Bs.ψ Bs.emb →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Γ.M.heisLine Bs.ψ u) f f₁ →
          (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
          ∃ L : ℝ →+ WO (sgn true W) X, Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧
            GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) =
              fun x => deriv (fun t : ℝ => heisO ψ (sgn true W) X (L t) (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) x) 0 := by
  intro _ _ D ψ θ _ _ W W₁ X A A₁ B α β _ ωA ωB _ _ e Bs Γ Xc om om' h _ _ R Rf hm f φ u f₁ _ _ hact hφ hvac
  have hVJ : Γ.V.J = -(sgn true W).gram := by
    rw [h.JW, one_smul]
    ext i j
    simp [sgn, Formalism.BasicNotions.HSpace.gram]
  rw [← h.ψ]
  exact thO_pure_deriv (sgn true W) X e Bs hm.triple.base Γ.V Γ.W hVJ h.JX hm.triple.geo.hV.herm Γ.M
    hm.triple.geo.hM f φ u f₁ hact hφ hvac

end GlobalTheory.ThetaDer

end
