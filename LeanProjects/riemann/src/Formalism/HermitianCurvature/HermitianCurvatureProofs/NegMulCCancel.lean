import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictUpperNeg

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section defs

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

abbrev XP (k p ρ : ℕ) : Type := (Mt k ρ × Mt k ρ) × U.RC k p ρ

def muXP (Bj : B.RealPlaceData k ρ Wp Wq) : Measure (XP k p ρ) := (Bj.μW.prod Bj.μN).prod (U.muRC k p ρ)

def GoodP (Bj : B.RealPlaceData k ρ Wp Wq) (x : XP k p ρ) : Prop :=
  (Matrix.of x.1.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z ∧ (Matrix.of x.1.2 : B.Mat k ρ) ∈ Nset k ρ

open Classical in

def sP (Bj : B.RealPlaceData k ρ Wp Wq) (x : XP k p ρ) : B.Mat k (p + ρ) :=
  if GoodP Bj x then
    U.Rn k p ρ (-x.2) * U.embG k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹)
  else 1

def cP (Bj : B.RealPlaceData k ρ Wp Wq) (x : XP k p ρ) : ℂ :=
  psi k ρ Bj.z cStd (Matrix.of x.1.2) * psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ x.2)

def pbI (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n) (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (g : B.Mat k n) (x : XP k p ρ) : Wq →L[ℂ] Wp :=
  cP Bj x • (Bj.π (Matrix.of x.1.1)).comp (PBG.Kr B0 H (D.castM e (sP Bj x) * g))

def pbF (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n) (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (g : B.Mat k n) : Wq →L[ℂ] Wp :=
  ∫ x, pbI Bj B0 e H g x ∂(muXP Bj)

end defs

section right

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pbF_right (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (g m : B.Mat k n) (hm : m ∈ QuantumDeterminants.Nset k n) :
    pbF Bj B0 e H (g * m) = psi k n B0.z' cStd m • pbF Bj B0 e H g := by
  unfold pbF
  rw [← integral_smul]
  congr 1
  funext x
  unfold pbI
  rw [← Matrix.mul_assoc, PBG.kr_rightEq B0 H _ m hm, ContinuousLinearMap.comp_smul, smul_comm]

end right

section rc

variable {k p ρ : ℕ}

local instance bsS : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
local instance bsRC : BorelSpace (U.RC k p ρ) := Prod.borelSpace
local instance bsRC2 : BorelSpace (U.RC k p ρ × U.RC k p ρ) := Prod.borelSpace

theorem psi_rn_mulC (z : Fin (2 * ρ + k + 1) → ℂ) (hz : inWb k ρ z) (x y : U.RC k p ρ) :
    psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ (StabilizerDisintegration.HC.mulC x y)) =
      psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x) * psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ y) := by
  rw [← StabilizerDisintegration.HC.rn_mul]
  exact PBG.psi_mul_nset _ (LeftFubiniLemmas.inWb_liftVec hz) _ (LeftFubiniLemmas.rn_nset x) (LeftFubiniLemmas.rn_nset y)

theorem cont_kap (c1 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) :
    Continuous (fun c : Fin (2 * ρ + k + 1) → Fin p → ℂ => StabilizerDisintegration.HC.kap c1 (Matrix.of c)) := by
  unfold StabilizerDisintegration.HC.kap StabilizerDisintegration.HC.skc
  have hM : Continuous (fun c : Fin (2 * ρ + k + 1) → Fin p → ℂ =>
      (1 / 2 : ℂ) • ((Matrix.of c)ᴴ * Hpk k ρ * c1 - c1ᴴ * Hpk k ρ * Matrix.of c)) := by
    have hof : Continuous (fun c : Fin (2 * ρ + k + 1) → Fin p → ℂ =>
        (Matrix.of c : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ)) := continuous_id
    have h1 : Continuous (fun c : Fin (2 * ρ + k + 1) → Fin p → ℂ => (Matrix.of c)ᴴ * Hpk k ρ * c1) :=
      ((hof.matrix_conjTranspose).matrix_mul (continuous_const (y := Hpk k ρ))).matrix_mul
        (continuous_const (y := c1))
    have h2 : Continuous (fun c : Fin (2 * ρ + k + 1) → Fin p → ℂ => c1ᴴ * Hpk k ρ * Matrix.of c) :=
      (continuous_const (y := c1ᴴ * Hpk k ρ)).matrix_mul hof
    exact (h1.sub h2).const_smul (1 / 2 : ℂ)
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun q => (continuous_apply _).comp ((continuous_apply _).comp hM)
  · exact continuous_pi fun a => Complex.continuous_im.comp ((continuous_apply _).comp ((continuous_apply _).comp hM))

theorem mp_mulC (d : U.RC k p ρ) :
    MeasurePreserving (StabilizerDisintegration.HC.mulC d) (U.muRC k p ρ) (U.muRC k p ρ) := by
  unfold U.muRC
  rw [Measure.volume_eq_prod]
  have hf : MeasurePreserving (fun c : Fin (2 * ρ + k + 1) → Fin p → ℂ => d.1 + c) volume volume :=
    measurePreserving_add_left volume d.1
  have hg : Measurable (Function.uncurry fun (c : Fin (2 * ρ + k + 1) → Fin p → ℂ)
      (S : (G.UT p → ℂ) × (Fin p → ℝ)) => (d.2 + StabilizerDisintegration.HC.kap (Matrix.of d.1) (Matrix.of c)) + S) := by
    refine Continuous.measurable ?_
    exact ((continuous_const.add ((cont_kap _).comp continuous_fst)).add continuous_snd)
  have := hf.skew_product hg (Filter.Eventually.of_forall fun c => map_add_left_eq_self volume _)
  convert this using 1
  funext x
  simp only [StabilizerDisintegration.HC.mulC]
  congr 1
  abel

theorem cont_mulC_left {X : Type*} [TopologicalSpace X] {d : X → U.RC k p ρ} (hd : Continuous d) :
    Continuous (fun q : X × U.RC k p ρ => StabilizerDisintegration.HC.mulC (d q.1) q.2) := by
  unfold StabilizerDisintegration.HC.mulC StabilizerDisintegration.HC.kap StabilizerDisintegration.HC.skc
  have hc1 : Continuous (fun q : X × U.RC k p ρ => (Matrix.of (d q.1).1 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ)) :=
    (hd.comp continuous_fst).fst
  have hc2 : Continuous (fun q : X × U.RC k p ρ => (Matrix.of q.2.1 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ)) :=
    continuous_snd.fst
  have hM : Continuous (fun q : X × U.RC k p ρ => (1 / 2 : ℂ) • ((Matrix.of q.2.1)ᴴ * Hpk k ρ *
      Matrix.of (d q.1).1 - (Matrix.of (d q.1).1)ᴴ * Hpk k ρ * Matrix.of q.2.1)) := by
    have h1 := ((hc2.matrix_conjTranspose).matrix_mul (continuous_const (y := Hpk k ρ))).matrix_mul hc1
    have h2 := ((hc1.matrix_conjTranspose).matrix_mul (continuous_const (y := Hpk k ρ))).matrix_mul hc2
    exact (h1.sub h2).const_smul (1 / 2 : ℂ)
  refine Continuous.prodMk ((continuous_fst.comp (hd.comp continuous_fst)).add continuous_snd.fst) ?_
  refine ((continuous_snd.comp (hd.comp continuous_fst)).add continuous_snd.snd).add (Continuous.prodMk ?_ ?_)
  · exact continuous_pi fun q => (continuous_apply _).comp ((continuous_apply _).comp hM)
  · exact continuous_pi fun a => Complex.continuous_im.comp ((continuous_apply _).comp ((continuous_apply _).comp hM))

theorem rn_neg_eq_inv (x : U.RC k p ρ) : U.Rn k p ρ (-x) = (U.Rn k p ρ x)⁻¹ :=
  (Matrix.inv_eq_right_inv (PBM.rn_mul_neg x)).symm

theorem rn_inj {x y : U.RC k p ρ} (h : U.Rn k p ρ x = U.Rn k p ρ y) : x = y :=
  (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).1 h

theorem mulC_neg_cancel (d x : U.RC k p ρ) : StabilizerDisintegration.HC.mulC d (StabilizerDisintegration.HC.mulC (-d) x) = x := by
  apply rn_inj
  rw [← StabilizerDisintegration.HC.rn_mul, ← StabilizerDisintegration.HC.rn_mul, ← Matrix.mul_assoc, PBM.rn_mul_neg, Matrix.one_mul]

theorem neg_mulC_cancel (d x : U.RC k p ρ) : StabilizerDisintegration.HC.mulC (-d) (StabilizerDisintegration.HC.mulC d x) = x := by
  have := mulC_neg_cancel (-d) x
  rwa [neg_neg] at this

end rc

section left

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def yA (q : Mt k ρ × Mt k ρ) : B.Mat k ρ :=
  (Hpk k ρ * (Matrix.of q.1 : B.Mat k ρ)ᴴ * Hpk k ρ) * (Hpk k ρ * (Matrix.of q.2 : B.Mat k ρ)ᴴ * Hpk k ρ)

def dOf (d0 : U.RC k p ρ) (q : Mt k ρ × Mt k ρ) : U.RC k p ρ := LeftFubiniLemmas.rcAct (yA q) d0

theorem cont_dOf (d0 : U.RC k p ρ) : Continuous (dOf (k := k) d0) := by
  unfold dOf LeftFubiniLemmas.rcAct yA
  refine Continuous.prodMk ?_ continuous_const
  refine continuous_pi fun v => continuous_pi fun a => ?_
  have hq1 : Continuous (fun q : Mt k ρ × Mt k ρ => (Matrix.of q.1 : B.Mat k ρ)) := continuous_fst
  have hq2 : Continuous (fun q : Mt k ρ × Mt k ρ => (Matrix.of q.2 : B.Mat k ρ)) := continuous_snd
  have h : Continuous (fun q : Mt k ρ × Mt k ρ => ((Hpk k ρ * (Matrix.of q.1 : B.Mat k ρ)ᴴ * Hpk k ρ) *
      (Hpk k ρ * (Matrix.of q.2 : B.Mat k ρ)ᴴ * Hpk k ρ)) * Matrix.of d0.1) :=
    (((continuous_const.matrix_mul hq1.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
      ((continuous_const.matrix_mul hq2.matrix_conjTranspose).matrix_mul continuous_const)).matrix_mul continuous_const
  exact (h.matrix_elem v a)

def shearE (d0 : U.RC k p ρ) : XP k p ρ ≃ᵐ XP k p ρ where
  toFun x := (x.1, StabilizerDisintegration.HC.mulC (-(dOf d0 x.1)) x.2)
  invFun x := (x.1, StabilizerDisintegration.HC.mulC (dOf d0 x.1) x.2)
  left_inv x := by simp only [mulC_neg_cancel]
  right_inv x := by simp only [neg_mulC_cancel]
  measurable_toFun := by
    have := bsRC (k := k) (p := p) (ρ := ρ)
    exact measurable_fst.prodMk (cont_mulC_left (cont_dOf d0).neg |>.measurable)
  measurable_invFun := by
    have := bsRC (k := k) (p := p) (ρ := ρ)
    exact measurable_fst.prodMk (cont_mulC_left (cont_dOf d0) |>.measurable)

theorem shearE_apply (d0 : U.RC k p ρ) (x : XP k p ρ) :
    shearE d0 x = (x.1, StabilizerDisintegration.HC.mulC (-(dOf d0 x.1)) x.2) := rfl

theorem mp_shearE (Bj : B.RealPlaceData k ρ Wp Wq) (d0 : U.RC k p ρ) :
    MeasurePreserving (shearE d0) (muXP Bj) (muXP Bj) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have := bsRC (k := k) (p := p) (ρ := ρ)
  have hg : Measurable (Function.uncurry fun (q : Mt k ρ × Mt k ρ) (c : U.RC k p ρ) =>
      StabilizerDisintegration.HC.mulC (-(dOf d0 q)) c) := (cont_mulC_left (cont_dOf d0).neg).measurable
  have := (MeasurePreserving.id (Bj.μW.prod Bj.μN)).skew_product hg
    (Filter.Eventually.of_forall fun q => (mp_mulC (-(dOf d0 q))).map_eq)
  unfold muXP
  exact this

variable {Bj : B.RealPlaceData k ρ Wp Wq}

theorem yA_eq {q : Mt k ρ × Mt k ρ}
    (hq : (Matrix.of q.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z ∧ (Matrix.of q.2 : B.Mat k ρ) ∈ Nset k ρ) :
    yA q = (Matrix.of q.1 : B.Mat k ρ)⁻¹ * (Matrix.of q.2 : B.Mat k ρ)⁻¹ := by
  unfold yA
  rw [Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose hq.1.1, Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose hq.2.1]

theorem yA_unitary {q : Mt k ρ × Mt k ρ}
    (hq : (Matrix.of q.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z ∧ (Matrix.of q.2 : B.Mat k ρ) ∈ Nset k ρ) :
    (yA q)ᴴ * Hpk k ρ * yA q = Hpk k ρ := by
  rw [yA_eq hq]
  exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hq.1.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hq.2.1)

theorem psi_dOf (hz : inWb k ρ Bj.z) {q : Mt k ρ × Mt k ρ}
    (hq : (Matrix.of q.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z ∧ (Matrix.of q.2 : B.Mat k ρ) ∈ Nset k ρ) (d0 : U.RC k p ρ) :
    psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ (dOf d0 q)) =
      psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ d0) := by
  have hsplit : dOf d0 q = LeftFubiniLemmas.rcAct ((Matrix.of q.1 : B.Mat k ρ)⁻¹)
      (LeftFubiniLemmas.rcAct ((Matrix.of q.2 : B.Mat k ρ)⁻¹) d0) := by
    unfold dOf
    rw [yA_eq hq]
    unfold LeftFubiniLemmas.rcAct
    simp only [Matrix.of_apply, Matrix.mul_assoc]
    rfl
  rw [hsplit, LeftFubiniLemmas.psi_right_action_comm k p ρ Bj.z _ _ hz (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hq.1)]
  set ν := (Matrix.of q.2 : B.Mat k ρ) with hν
  have hνi : ν⁻¹ ∈ Nset k ρ := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hq.2
  have hu : (ν⁻¹)ᴴ * Hpk k ρ * ν⁻¹ = Hpk k ρ := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hq.2.1
  have e := LeftFubiniLemmas.embedded_group_right_action k p ρ ν⁻¹ d0 hu
  have hz0 := LeftFubiniLemmas.inWb_liftVec (p := p) hz
  have hE : U.embG k p ρ ν⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ) := LeftFubiniLemmas.embG_nset hνi
  have h1 := congrArg (psi k (p + ρ) (liftVec k p ρ Bj.z) cStd) e
  rw [PBG.psi_mul_nset _ hz0 _ hE (LeftFubiniLemmas.rn_nset d0), PBG.psi_mul_nset _ hz0 _ (LeftFubiniLemmas.rn_nset _) hE] at h1
  have hne : psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.embG k p ρ ν⁻¹) ≠ 0 := Complex.exp_ne_zero _
  have := mul_left_cancel₀ hne (h1.trans (mul_comm _ _))
  exact this.symm

theorem leftFactor_mul_eq_shear {x : XP k p ρ} (hx : GoodP Bj x) (d0 : U.RC k p ρ) :
    sP Bj x * U.Rn k p ρ d0 = sP Bj (shearE d0 x) := by
  rw [shearE_apply]
  have hx' : GoodP Bj (x.1, StabilizerDisintegration.HC.mulC (-(dOf d0 x.1)) x.2) := hx
  unfold sP
  rw [if_pos hx, if_pos hx']
  simp only []
  rw [Matrix.mul_assoc, ← yA_eq hx, LeftFubiniLemmas.embedded_group_right_action k p ρ _ d0 (yA_unitary hx), ← Matrix.mul_assoc]
  congr 1
  rw [rn_neg_eq_inv x.2, rn_neg_eq_inv (StabilizerDisintegration.HC.mulC _ x.2), ← StabilizerDisintegration.HC.rn_mul, Matrix.mul_inv_rev,
    rn_neg_eq_inv (dOf d0 x.1), Matrix.nonsing_inv_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (LeftFubiniLemmas.rn_nset _).1)]
  rfl

theorem characterProduct_shear (hz : inWb k ρ Bj.z) {x : XP k p ρ} (hx : GoodP Bj x) (d0 : U.RC k p ρ) :
    cP Bj x = psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ d0) * cP Bj (shearE d0 x) := by
  rw [shearE_apply]
  unfold cP
  simp only []
  rw [psi_rn_mulC _ hz, ← psi_dOf hz hx d0]
  have hz0 := LeftFubiniLemmas.inWb_liftVec (p := p) hz
  have h1 : psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ (dOf d0 x.1)) *
      psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ (-(dOf d0 x.1))) = 1 := by
    rw [← PBG.psi_mul_nset _ hz0 _ (LeftFubiniLemmas.rn_nset _) (LeftFubiniLemmas.rn_nset _), PBM.rn_mul_neg,
      Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one hz0]
  calc _ = (psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ (dOf d0 x.1)) *
        psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ (-(dOf d0 x.1)))) *
        (psi k ρ Bj.z cStd (Matrix.of x.1.2) * psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ x.2)) := by
          rw [h1, one_mul]
    _ = _ := by ring

theorem ae_goodP (Bj : B.RealPlaceData k ρ Wp Wq) : ∀ᵐ x ∂(muXP (p := p) Bj), GoodP Bj x := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have w1 := Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarW
  have w2 := Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarN
  unfold muXP
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae w1),
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae w2)] with x a b
  exact ⟨a, b⟩

theorem castM_mul {a b : ℕ} (e : a = b) (g h : B.Mat k a) : D.castM e (g * h) = D.castM e g * D.castM e h := by
  subst e; simp [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem pbF_left_rn (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n) (hz : inWb k ρ Bj.z)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (d0 : U.RC k p ρ) (g : B.Mat k n) :
    pbF Bj B0 e H (D.castM e (U.Rn k p ρ d0) * g) =
      psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ d0) • pbF Bj B0 e H g := by
  unfold pbF
  rw [← (mp_shearE Bj d0).integral_comp' (pbI Bj B0 e H g), ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [ae_goodP Bj] with x hx
  unfold pbI
  rw [← Matrix.mul_assoc, ← castM_mul, leftFactor_mul_eq_shear hx d0, characterProduct_shear hz hx d0, mul_smul]
  rfl

end left

end Formalism.FourierDecayAlt.P.PBQ
