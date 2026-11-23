import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPin
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.JointPinNorm

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf
  Formalism.L2.SG.Pf.Carrier.JointQuot Formalism.L2.SG.Pf.Carrier.EnergyFinal Formalism.L2.SG.Pf.Carrier.EnergyPlace
  Formalism.L2.SG.Pf.Carrier.JointPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Bessel

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def qDiag (q : (Fin r → ℂ) × ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.diagonal (Fin.snoc (α := fun _ => ℂ) q.1 q.2)

def OrbDirac : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r),
    γ ∈ Formalism.FourierDecayAlt.B.GV k r → ∀ F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp),
      Formalism.FourierDecayAlt.D.orbJ D γ (Measure.dirac (Matrix.of.symm (1 : Formalism.FourierDecayAlt.B.Mat k r))) F = Formalism.FourierDecayAlt.B.JF D F γ

def HSsgs : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (p : Formalism.FourierDecayAlt.B.SS k r), D.inSS p → ∀ g : Formalism.FourierDecayAlt.B.Mat k r,
      ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF D F (Formalism.FourierDecayAlt.B.sgs p g))‖ = ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF D F g)‖

def CosetOf : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r),
    γ ∈ Formalism.FourierDecayAlt.B.GV k r → ∀ q ∈ Formalism.FourierDecayAlt.JF.QDom k r D.z D.z', Formalism.QuantumDeterminants.Zhat k r D.z D.z' γ = qDiag q →
      ∃ p, D.inSS p ∧ γ = Formalism.FourierDecayAlt.B.sgs p (Formalism.FourierDecayAlt.B.gq D q)

def RelDiag : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (d : Fin (r + 1) → ℂ),
    γ ∈ Formalism.FourierDecayAlt.B.GV k r → (∀ a, d a ≠ 0) → Formalism.QuantumDeterminants.Zhat k r D.z D.z' γ = Matrix.diagonal d →
      Formalism.FourierDecayAlt.C6.IsRelevant D γ

end Bessel

section BesselPf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem star_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mat k r) :
    star (psi k r z c g) = (psi k r z c g)⁻¹ := by
  unfold psi
  rw [← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

theorem norm_xiTau (D : RealPlaceData k r Wp Wq) (p : SS k r) : ‖xiTau D (1, 1) p‖ = 1 := by
  unfold xiTau
  rw [Complex.norm_exp]
  simp

theorem orbIntegrand_eq [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (γ : Mat k r) (F : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) :
    Formalism.FourierDecayAlt.D.orbIntegrand D γ F p =
      (psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2))) •
        ((D.π (Matrix.of p.1.1)).comp
          ((F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1)).comp
            (D.π' (Matrix.of p.2.1)⁻¹))) := by
  unfold Formalism.FourierDecayAlt.D.orbIntegrand
  rw [Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.xiTau_eq, star_psi]
  rfl

theorem hs_left [FiniteDimensional ℂ Wq] (A : Wp →L[ℂ] Wp) (hA : ∀ v, ‖A v‖ = ‖v‖) (X : Wq →L[ℂ] Wp) :
    ‖hsVec (A.comp X)‖ = ‖hsVec X‖ := by
  simp only [hsVec, PiLp.norm_eq_of_L2, ContinuousLinearMap.comp_apply, hA]

theorem hs_right [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (U : Wq →L[ℂ] Wq) (hU : ∀ v, ‖U v‖ = ‖v‖)
    (X : Wq →L[ℂ] Wp) : ‖hsVec (X.comp U)‖ = ‖hsVec X‖ := by
  let li : Wq →ₗᵢ[ℂ] Wq := ⟨U.toLinearMap, hU⟩
  let e : Wq ≃ₗᵢ[ℂ] Wq := li.toLinearIsometryEquiv rfl
  have h := Formalism.L2.SG.RealObj.InfCut.hsb_indep ((stdOrthonormalBasis ℂ Wq).map e) (stdOrthonormalBasis ℂ Wq) X
  simp only [OrthonormalBasis.map_apply] at h
  simp only [hsVec, PiLp.norm_eq_of_L2, ContinuousLinearMap.comp_apply]
  congr 1

theorem hs_smul [FiniteDimensional ℂ Wq] (c : ℂ) (hc : ‖c‖ = 1) (X : Wq →L[ℂ] Wp) :
    ‖hsVec (c • X)‖ = ‖hsVec X‖ := by
  simp only [hsVec, PiLp.norm_eq_of_L2, ContinuousLinearMap.smul_apply, norm_smul, hc, one_mul]

theorem hSsgs_holds : HSsgs := by
  intro k r Wp Wq _ _ _ _ _ _ D F p hp g
  have hj := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.jf_equiv D F p hp g
  unfold rho at hj
  have hh : Matrix.of p.1.1 ∈ UWset k r D.z := hp.1
  have hh' : (Matrix.of p.2.1)⁻¹ ∈ UWset k r D.z' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hp.2.2.1
  calc ‖hsVec (JF D F (sgs p g))‖
        = ‖hsVec ((D.π (Matrix.of p.1.1)).comp ((JF D F (sgs p g)).comp (D.π' (Matrix.of p.2.1)⁻¹)))‖ := by
          rw [hs_left _ (D.π_unitary _ hh), hs_right _ (D.π'_unitary _ hh')]
    _ = ‖hsVec ((xiTau D (1, 1) p)⁻¹ • JF D F g)‖ := by rw [hj]
    _ = ‖hsVec (JF D F g)‖ := hs_smul _ (by rw [norm_inv, norm_xiTau, inv_one]) _

theorem orbDirac_holds : OrbDirac := by
  intro k r Wp Wq _ _ _ _ _ D γ hγ F
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hγ
  have hinv : γ⁻¹ * γ = 1 := by
    first
    | exact Matrix.nonsing_inv_mul γ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
    | exact Matrix.nonsing_inv_mul γ hu
  have hact : ∀ p, Formalism.FourierDecayAlt.C6.actR γ (Matrix.of (Matrix.of.symm (1 : Mat k r))) p = p := by
    intro p
    simp only [Formalism.FourierDecayAlt.C6.actR, Equiv.apply_symm_apply, Matrix.mul_one, Matrix.one_mul, hinv]
    rfl
  have hnc1 : Formalism.FourierDecayAlt.D.IsNormCut D γ (Measure.dirac (Matrix.of.symm (1 : Mat k r))) (fun _ => (1 : ℝ)) :=
    ⟨measurable_const, fun _ => zero_le_one, fun p _ => by simp⟩
  have hJF : JF D F γ = ∫ p, Formalism.FourierDecayAlt.D.orbIntegrand D γ F p ∂D.μSS := by
    have h := orbIntegrand_eq D γ F
    simp only [h]
    rfl
  unfold Formalism.FourierDecayAlt.D.orbJ
  split_ifs with h
  · obtain ⟨hnc, -⟩ := h.choose_spec
    rw [hJF]
    apply integral_congr_ae
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
    have h1 := hnc.2.2 p hp
    rw [integral_dirac, hact] at h1
    simp [h1]
  · rw [hJF]
    symm
    apply integral_undef
    intro hi
    exact h ⟨fun _ => 1, hnc1, by simpa using hi⟩

theorem dmin_diag (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (x : Fin (r + 1) → ℂ)
    (hZ : Formalism.QuantumDeterminants.Zhat k r z z' γ = Matrix.diagonal x) (l : Fin (r + 2)) :
    Dmin k r z z' γ l = ∏ i : Fin l, x (Fin.castLE (Nat.le_of_lt_succ l.isLt) i) := by
  unfold Dmin
  rw [hZ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  rfl

theorem prod_castLE_succ (x : Fin (r + 1) → ℂ) (m : ℕ) (hm : m + 1 ≤ r + 1) :
    ∏ i : Fin (m + 1), x (Fin.castLE hm i) =
      (∏ i : Fin m, x (Fin.castLE (by omega) i)) * x ⟨m, by omega⟩ := by
  rw [Fin.prod_univ_castSucc]
  rfl

theorem prod_castLE_ne (x : Fin (r + 1) → ℂ) (hx : ∀ a, x a ≠ 0) (m : ℕ) (hm : m ≤ r + 1) :
    ∏ i : Fin m, x (Fin.castLE hm i) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => hx _

theorem cosetOf_holds : CosetOf := by
  intro k r Wp Wq _ _ _ _ D γ hγ q hq hZ
  set x : Fin (r + 1) → ℂ := Fin.snoc (α := fun _ => ℂ) q.1 q.2 with hxdef
  have hT := mul_pos D.T_pos D.T'_pos
  have hq2 : q.2 ≠ 0 := by
    intro h; have := hq.2; rw [h, map_zero] at this; exact absurd this (not_lt.2 hT.le)
  have hx : ∀ a, x a ≠ 0 := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [hxdef, Fin.snoc_last]; exact hq2
    · simp only [hxdef, Fin.snoc_castSucc]; exact hq.1 i
  have hZ' : Formalism.QuantumDeterminants.Zhat k r D.z D.z' γ = Matrix.diagonal x := hZ
  have hD := dmin_diag D.z D.z' γ x hZ'

  have hDr1 : Dmin k r D.z D.z' γ (Fin.last (r + 1)) = Dmin k r D.z D.z' γ ⟨r, by omega⟩ * q.2 := by
    rw [hD, hD]
    have := prod_castLE_succ x r (le_refl _)
    simp only [Fin.val_last] at *
    rw [this]
    congr 1
    show x (Fin.last r) = q.2
    simp [hxdef]
  have hOm : γ ∈ Formalism.FourierDecayAlt.JF.Om k r D.z D.z' := by
    refine ⟨hγ, fun l _ => by rw [hD]; exact prod_castLE_ne x hx _ _, ?_⟩
    unfold Gf
    rw [hDr1, map_mul]
    have h0 : 0 < Complex.normSq (Dmin k r D.z D.z' γ ⟨r, by omega⟩) := by
      rw [hD]; exact Complex.normSq_pos.2 (prod_castLE_ne x hx _ _)
    nlinarith [hq.2]
  obtain ⟨p, hp, q', hq', he⟩ := Formalism.FourierDecayAlt.Final.jf_psiOnto k r Wp Wq D γ hOm
  refine ⟨p, hp, ?_⟩
  have hcm : ∀ a : Fin r, cmin k r D.z D.z' γ a = q.1 a := by
    intro a
    unfold cmin
    rw [hD, hD]
    have := prod_castLE_succ x a.val (by omega)
    simp only at this ⊢
    rw [this, mul_div_cancel_left₀ _ (prod_castLE_ne x hx _ _)]
    show x (Fin.castSucc a) = q.1 a
    simp [hxdef]
  have hzt : zeta k r D.z D.z' γ = q.2 := by
    unfold zeta
    rw [hDr1, mul_div_cancel_left₀ _ (by rw [hD]; exact prod_castLE_ne x hx _ _)]
  have hqq : q' = q := by
    have h1 : ∀ a, cmin k r D.z D.z' γ a = q'.1 a := by
      intro a; rw [he]; unfold cmin; simp only [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp]
      exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.cmin_gq D hq' a
    have h2 : zeta k r D.z D.z' γ = q'.2 := by
      rw [he]; unfold zeta; simp only [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp]
      exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.zeta_gq D hq'
    ext a
    · rw [← h1, hcm]
    · rw [← h2, hzt]
  rw [he, hqq]

theorem ptEntry_ones (l : List ℂ) : ∀ a b : ℕ,
    Formalism.FourierDecayAlt.D.ptEntry (l.map fun t => (1, t)) a b = if a = b then l.getD a 0 else 0 := by
  induction l with
  | nil => intro a b; simp [Formalism.FourierDecayAlt.D.ptEntry]
  | cons t l ih =>
    intro a b
    cases a <;> cases b <;> simp [Formalism.FourierDecayAlt.D.ptEntry, ih]

theorem relDiag_holds : RelDiag := by
  intro k r Wp Wq _ _ _ _ D γ d hγ hd hZ
  refine Formalism.FourierDecayAlt.Final.d_ptRelevant k r Wp Wq D ((List.ofFn d).map fun t => (1, t)) γ ⟨?_, ?_⟩ hγ ?_
  · intro b hb
    simp only [List.mem_map, List.mem_ofFn] at hb
    obtain ⟨t, ⟨a, rfl⟩, rfl⟩ := hb
    exact ⟨le_refl _, hd a⟩
  · simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  · rw [hZ]
    ext i j
    show Matrix.diagonal d i j = Formalism.FourierDecayAlt.D.ptEntry _ i.val j.val
    rw [ptEntry_ones, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp only [if_true]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    · simp [h, Fin.val_inj]

end BesselPf

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def StOne (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    StSet (NV X u v) (NV X u' v) g = {1}

def ZhatTr (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  P.FromX → 0 < P.S.g →
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    trG (P.Q v) (P.Qi v) g ∈ Formalism.FourierDecayAlt.B.GV P.S.G.k P.S.G.r ∧
    Formalism.QuantumDeterminants.Zhat P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z (P.T (P.τ.symm v)).base.z' (trG (P.Q v) (P.Qi v) g) =
      qDiag (phiQ P hr cv) ∧
    phiQ P hr cv ∈ Formalism.FourierDecayAlt.JF.QDom P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z (P.T (P.τ.symm v)).base.z'

theorem trMeas_dirac (P : Parts X u u') (v : InfinitePlace X.B.I.F) (hQ : P.Qi v * P.Q v = 1) :
    trMeas P v (Measure.dirac 1) = Measure.dirac (Matrix.of.symm (1 : Formalism.FourierDecayAlt.B.Mat P.S.G.k P.S.G.r)) := by
  unfold trMeas
  have h1 : Continuous (fun s : Formalism.REAL.UJ (X.B.I.ε v) => ((s : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) := Units.continuous_val.comp continuous_subtype_val
  have hm : Measurable (fun s : Formalism.REAL.UJ (X.B.I.ε v) => Matrix.of.symm (trG (P.Q v) (P.Qi v) s)) := by
    refine Continuous.measurable ?_
    exact (continuous_const.matrix_mul h1).matrix_mul continuous_const
  rw [Measure.map_dirac' hm]
  congr 1
  simp [trG, uMat, hQ]

theorem normBridge_of (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hOD : OrbDirac) (hHS : HSsgs) (hCo : CosetOf)
    (hRel : RelDiag) (hSt : StOne X u u') (hZ : ZhatTr P hr) : NormBridge P hr := by
  intro hFX hBuilt hg v g cv hcv hZg
  obtain ⟨hGV, hZB, hq⟩ := hZ hFX hg v g cv hcv hZg
  have hQ : P.Qi v * P.Q v = 1 := (hFX v).1.1
  have hS := hSt v g cv hcv hZg
  refine ⟨Measure.dirac 1, Formalism.REAL.muG _, ⟨?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · rw [hZg]; exact hcv.2
  · rw [hZg]
    exact ⟨1, cv, hcv.1, by ext i a; simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.diagonal_apply, Matrix.of_apply, Equiv.Perm.coe_one, id]; split_ifs with h <;> simp_all⟩
  · exact hRel _ _ _ _ _ _ (Fin.snoc (α := fun _ => ℂ) (phiQ P hr cv).1 (phiQ P hr cv).2) hGV
      (fun a => by
        refine Fin.lastCases ?_ (fun i => ?_) a
        · simp only [Fin.snoc_last]; intro h; have := hq.2; rw [h, map_zero] at this
          exact absurd this (not_lt.2 (mul_pos (P.T (P.τ.symm v)).base.T_pos (P.T (P.τ.symm v)).base.T'_pos).le)
        · simp only [Fin.snoc_castSucc]; exact hq.1 i) hZB
  · rw [hS]
    refine ⟨inferInstance, Measure.dirac_ne_zero, ?_, ?_⟩
    · simp
    · intro s hs; rw [Set.mem_singleton_iff.1 hs]; simp
  · intro f hf
    simp [lintegral_dirac]
  · rw [trMeas_dirac P v hQ, hOD _ _ _ _ _ _ hGV]
    obtain ⟨p, hp, hγ⟩ := hCo _ _ _ _ _ _ hGV _ hq hZB
    rw [hγ]
    exact hHS _ _ _ _ _ _ _ hp _

theorem normBridge_of_two (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hSt : StOne X u u') (hZ : ZhatTr P hr) :
    NormBridge P hr :=
  normBridge_of P hr orbDirac_holds hSsgs_holds cosetOf_holds relDiag_holds hSt hZ

end Formalism.L2.SG.Pf.Carrier.JointPinNorm
