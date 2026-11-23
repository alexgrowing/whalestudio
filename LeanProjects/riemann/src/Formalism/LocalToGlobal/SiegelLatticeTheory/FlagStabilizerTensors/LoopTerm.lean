import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOfInhab
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittExistsHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPinG
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormRepX
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

noncomputable section

open scoped Classical
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTieOf

namespace Formalism.L2.SG.LoopTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PartB

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def locB (large₂ : SizeData₂ D) (C1 : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word)
    (hθ : normWin D large₂ C1 θ) (hW : ∀ τ, GoodW D τ u u' θ (locW C u u' τ))
    (hS : ∀ τ, GoodS D (lamD D τ) (locS hB u u' τ)) : LoopLocDat D large₂ u u' C1 where
  θ := θ
  θ_win := hθ
  W := fun τ => locW C u u' τ
  goodW := hW
  A := fun τ => locS hB u u' τ
  goodS := hS
  deg_eq := fun _ => rfl

end PartB

section Point

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF))

theorem tu_ne (u' : D.what₂.Word) : ((Tu D u' : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero

def IsFrameLift {u u' : D.what₂.Word} (t : D.s.Term u u') (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, g ((X.Fu u').e a) = (repF (tc hI t)).fl.e a) ∧
    g (X.Fu u').z = (repF (tc hI t)).fl.z

def linOf {u u' : D.what₂.Word} (t : D.s.Term u u') : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  if h : ∃ g, IsFrameLift hI t g then h.choose else LinearEquiv.refl D.host.E (VS D).V

def ptR {u u' : D.what₂.Word} (t : D.s.Term u u') : X.B.I.GA :=
  if h : ∃ x, Formalism.L2.SG.TermOp.RatLink X x (linOf hI t) then h.choose else 1

variable {θ : ℝ} (C : Choice X θ)

def gamR {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau) : MatKR D.R.k D.R.rS :=
  Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((ptR hI t).1 (vOf X τ))

def pt0 (D : D7) : Point ℂ (D.R.rS + 1) := ⟨[(1, D.R.rS + 1)], by simp, by simp⟩

def ptC {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau) : Point ℂ (D.R.rS + 1) :=
  if h : ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamR hI C t τ) p then h.choose else pt0 D

def nu1 {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau) : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  if h : ∃ ν, RMeas D (locW C u u' τ) (gamR hI C t τ) 1 ν then h.choose else 0

end Point

section Stmts

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF)) {θ : ℝ}
  (C : Choice X θ)

def FrameLiftEx (u u' : D.what₂.Word) : Prop := ∀ t : D.s.Term u u', ∃ g, IsFrameLift hI t g

def GramTr (u u' : D.what₂.Word) : Prop :=
  ∀ (t : D.s.Term u u') (τ : D.what₂.Tau) (a b : Fin (D.R.rS + 1)),
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamR hI C t τ) a b =
      ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (ZhatL (lf D (FlagOfWord W u)) (fl'Of W hI t) a b)

def RelPtEx (u u' : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamR hI C t τ) p

def RMeasEx (u u' : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ, ∃ ν, RMeas D (locW C u u' τ) (gamR hI C t τ) 1 ν

def IsFundR {u u' : D.what₂.Word} (s : TT Y u u') (K : Set X.B.I.Ginf) : Prop :=
  MeasurableSet K ∧
    ∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset s, ∃! q, q ∈ Formalism.L2.SG.TermOp.ROinf s ∧ q * r ∈ K

def HasPin {u u' : D.what₂.Word} (s : TT Y u u') : Prop :=
  ∃ x : Point D.host.E (D.R.rS + 1) × Measure X.B.I.Ginf × Set X.B.I.Ginf,
    s.toTerm.atPt x.1 ∧ Formalism.L2.SG.VolPin.IsPinnedR s x.1 x.2.1 ∧ IsFundR s x.2.2

def covR {u u' : D.what₂.Word} (s : TT Y u u') : ℝ :=
  if h : HasPin s then (h.choose.2.1 h.choose.2.2).toReal else 1

def volRC {u u' : D.what₂.Word} (t : D.s.Term u u') : ℝ :=
  if h : D.s.relevant t ∧ D.s.Gterm t ≠ 0 ∧ ∃ s : TT Y u u', s.toTerm = tc hI t then covR h.2.2.choose else 1

def PinAll (u u' : D.what₂.Word) : Prop :=
  ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → HasPin s

def CovolPos (u u' : D.what₂.Word) : Prop :=
  ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ w μR K, s.toTerm.atPt w → Formalism.L2.SG.VolPin.IsPinnedR s w μR →
    IsFundR s K → 0 < (μR K).toReal

variable (hB : WuBessel C)

def j1 {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau) : ℝ :=
  hsNormSq ((locS hB u u' τ).J (nu1 hI C t τ) (gamR hI C t τ))

def P1 {u u' : D.what₂.Word} (t : D.s.Term u u') : ℝ := ∏ τ, j1 hI C hB t τ

def thetaS {u u' : D.what₂.Word} (t : D.s.Term u u') : ℝ :=
  if 0 < hsNormSq (JtOf hI t) ∧ 0 < P1 hI C hB t then
    (volRC hI t ^ 2 * P1 hI C hB t / hsNormSq (JtOf hI t)) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau))
  else 1

def nuR {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau) : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  (ENNReal.ofReal (thetaS hI C hB t))⁻¹ • nu1 hI C t τ

def JZeroIff (u u' : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → (hsNormSq (JtOf hI t) = 0 ↔ P1 hI C hB t = 0)

def ThetaWin (large₂ : SizeData₂ D) (C1 : ℝ) (u u' : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → normWin D large₂ C1 (thetaS hI C hB t)

end Stmts

section Lemmas

open scoped ComplexConjugate

theorem hsNormSq_nonneg {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  first
    | (rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re]; positivity)
    | exact inner_self_nonneg (𝕜 := ℂ)
    | simp

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (c • A) = Complex.normSq c * hsNormSq A := by
  unfold hsNormSq hsInner
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
  have hx : ∀ z : ℂ, (starRingEnd ℂ) c * (c * z) = (Complex.normSq c : ℂ) * z := fun z => by
    rw [← mul_assoc, Complex.normSq_eq_conj_mul_self]
  have hy : ∀ z : ℂ, c * ((starRingEnd ℂ) c * z) = (Complex.normSq c : ℂ) * z := fun z => by
    rw [← mul_assoc, Complex.mul_conj]
  simp only [hx, hy]
  rw [← Finset.mul_sum, Complex.re_ofReal_mul]

theorem isQuotMeas_smul {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : IsQuotMeas μG μS ν) {c : ENNReal}
    (h0 : c ≠ 0) (hT : c ≠ ⊤) : IsQuotMeas μG (c • μS) (c⁻¹ • ν) := by
  unfold IsQuotMeas at h ⊢
  intro f hf
  rw [h f hf]
  simp only [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ hT, ← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]

theorem locJ_smul {k r : ℕ} {W : LocW k r} (A : LocS W) (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (c : ENNReal)
    (γ : MatKR k r) : A.J (c • ν) γ = ((c.toReal : ℝ) : ℂ) • A.J ν γ := by
  unfold Formalism.MainNotions.S.LocS.J Formalism.MainNotions.S.ampJ
  rw [MeasureTheory.integral_smul_measure, Complex.coe_smul]
  exact smul_comm _ _ _

end Lemmas

section Clauses

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)

theorem jt_irr (hA : Formalism.L2.SG.TermOp.Vanish.AvgCore) (hK : Formalism.L2.SG.TermOp.Vanish.ChiTrivialC)
    (h3 : Formalism.L2.SG.TermOp.Vanish.RCocompactC) (h4 : Formalism.L2.SG.TermOp.Vanish.NonRelCharC)
    {u u' : D.what₂.Word} (t : D.s.Term u u') (hn : ¬ D.s.relevant t) : JtOf hI t = 0 := by
  unfold JtOf
  split_ifs with h
  · have hs : ¬ h.choose.relevant := by
      intro hr
      apply hn
      rw [hI.relevant t]
      unfold Formalism.L2.SG.TermOp.GTerm.relevant at hr
      rw [h.choose_spec] at hr
      exact hr
    have h0 := Formalism.L2.SG.TermOp.Vanish.ooVanish_of hA Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds hK
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds h3 h4 Y h.choose hs
    unfold Formalism.L2.SG.TermOp.ampN
    rw [h0]
    simp
  · rfl

theorem volRC_pos {u u' : D.what₂.Word} (hPin : PinAll (Y := Y) u u') (hCv : CovolPos (Y := Y) u u') (t : D.s.Term u u') :
    0 < volRC hI t := by
  unfold volRC
  split_ifs with h
  · have hs := h.2.2.choose_spec
    have hr : (h.2.2.choose).relevant := by
      show (h.2.2.choose).toTerm.relevant
      rw [hs]
      exact (hI.relevant t).1 h.1
    have hg : (h.2.2.choose).G ≠ 0 := by
      show (h.2.2.choose).toTerm.G ≠ 0
      rw [hs]
      intro h0
      apply h.2.1
      apply (algebraMap D.host.F D.host.E).injective
      rw [gterm_val hI t, h0, map_zero]
    have hp := hPin _ hr hg
    unfold covR
    rw [dif_pos hp]
    exact hCv _ hr hg _ _ _ hp.choose_spec.1 hp.choose_spec.2.1 hp.choose_spec.2.2
  · exact one_pos

theorem ptC_spec {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau)
    (h : ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamR hI C t τ) p) :
    RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamR hI C t τ) (ptC hI C t τ) := by
  rw [ptC, dif_pos h]
  exact h.choose_spec

variable (hB : WuBessel C)

theorem productNorm_nonneg {u u' : D.what₂.Word} (t : D.s.Term u u') : 0 ≤ P1 hI C hB t := by
  unfold P1 j1
  exact Finset.prod_nonneg fun τ _ => Formalism.L2.SG.LoopTerm.hsNormSq_nonneg _

theorem thetaS_pos {u u' : D.what₂.Word} (hPin : PinAll (Y := Y) u u') (hCv : CovolPos (Y := Y) u u') (t : D.s.Term u u') : 0 < thetaS hI C hB t := by
  unfold thetaS
  split_ifs with h
  · exact Real.rpow_pos_of_pos (div_pos (mul_pos (pow_pos (volRC_pos hI hPin hCv t) 2) h.2) h.1) _
  · exact one_pos

theorem rmeas_nuR {u u' : D.what₂.Word} (hPin : PinAll (Y := Y) u u') (hCv : CovolPos (Y := Y) u u') (t : D.s.Term u u') (τ : D.what₂.Tau)
    (h : ∃ ν, RMeas D (locW C u u' τ) (gamR hI C t τ) 1 ν) :
    RMeas D (locW C u u' τ) (gamR hI C t τ) (thetaS hI C hB t) (nuR hI C hB t τ) := by
  have hν : RMeas D (locW C u u' τ) (gamR hI C t τ) 1 (nu1 hI C t τ) := by
    unfold nu1
    rw [dif_pos h]
    exact h.choose_spec
  obtain ⟨p, μR, hp, hq⟩ := hν
  have hθ := thetaS_pos hI C hB hPin hCv t
  refine ⟨p, μR, hp, ?_⟩
  rw [ENNReal.ofReal_one, one_smul] at hq
  exact isQuotMeas_smul hq (ENNReal.ofReal_pos.2 hθ).ne' ENNReal.ofReal_ne_top

theorem jnorm {u u' : D.what₂.Word} (hPin : PinAll (Y := Y) u u') (hCv : CovolPos (Y := Y) u u') (hZ : JZeroIff hI C hB u u')
    (hTau : Nonempty D.what₂.Tau) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hr : D.s.relevant t) :
    hsNormSq (JtOf hI t) = volRC hI t ^ 2 *
      ∏ τ, hsNormSq ((locS hB u u' τ).J (nuR hI C hB t τ) (gamR hI C t τ)) := by
  have hθ := thetaS_pos hI C hB hPin hCv t
  have hv := volRC_pos hI hPin hCv t
  have hterm : ∀ τ, hsNormSq ((locS hB u u' τ).J (nuR hI C hB t τ) (gamR hI C t τ)) =
      (thetaS hI C hB t)⁻¹ ^ 2 * j1 hI C hB t τ := by
    intro τ
    unfold nuR j1
    rw [locJ_smul, hsNormSq_smul, Complex.normSq_ofReal, ENNReal.toReal_inv, ENNReal.toReal_ofReal hθ.le]
    ring
  have hP1 : ∏ τ, j1 hI C hB t τ = P1 hI C hB t := rfl
  rw [Finset.prod_congr rfl (fun τ _ => hterm τ), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hP1]
  by_cases hpos : 0 < hsNormSq (JtOf hI t) ∧ 0 < P1 hI C hB t
  · have hcard : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos_iff.2 hTau
    have hn : 2 * Fintype.card D.what₂.Tau ≠ 0 := by omega
    have hx : 0 ≤ volRC hI t ^ 2 * P1 hI C hB t / hsNormSq (JtOf hI t) :=
      div_nonneg (mul_nonneg (sq_nonneg _) hpos.2.le) hpos.1.le
    have h2f : thetaS hI C hB t ^ (2 * Fintype.card D.what₂.Tau) =
        volRC hI t ^ 2 * P1 hI C hB t / hsNormSq (JtOf hI t) := by
      unfold thetaS
      rw [if_pos hpos]
      rw [show (1 : ℝ) / (2 * Fintype.card D.what₂.Tau) = ((2 * Fintype.card D.what₂.Tau : ℕ) : ℝ)⁻¹ by
        push_cast; ring]
      exact Real.rpow_inv_natCast_pow hx hn
    rw [← pow_mul, inv_pow, h2f]
    have h1 : hsNormSq (JtOf hI t) ≠ 0 := hpos.1.ne'
    have h2 : P1 hI C hB t ≠ 0 := hpos.2.ne'
    have h3 : volRC hI t ≠ 0 := hv.ne'
    field_simp
  · have hs0 : hsNormSq (JtOf hI t) = 0 ∧ P1 hI C hB t = 0 := by
      have a := Formalism.L2.SG.LoopTerm.hsNormSq_nonneg (JtOf hI t)
      have b := productNorm_nonneg hI C hB t
      have hz := hZ t hG hr
      by_cases ha : hsNormSq (JtOf hI t) = 0
      · exact ⟨ha, hz.1 ha⟩
      · have hb : P1 hI C hB t ≠ 0 := fun hb => ha (hz.2 hb)
        exact absurd ⟨lt_of_le_of_ne a (Ne.symm ha), lt_of_le_of_ne b (Ne.symm hb)⟩ hpos
    rw [hs0.1, hs0.2]
    simp

end Clauses

section Gram

open scoped ComplexConjugate

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF)) {θ : ℝ}
  (C : Choice X θ)

theorem star_dot_conjT {n m : Type*} [Fintype n] [Fintype m] (Q : Matrix n m ℂ) (x : m → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (Qᴴ *ᵥ y) = star (Q *ᵥ x) ⬝ᵥ y := by
  first
    | rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]
    | rw [dotProduct_mulVec, Matrix.star_mulVec]

theorem hJ_smul_real {n : ℕ} (ε : Fin n → Bool) (r s : ℝ) (x y : Fin n → ℂ) :
    hJ ε ((r : ℂ) • x) ((s : ℂ) • y) = ((r * s : ℝ) : ℂ) * hJ ε x y := by
  simp only [hJ]
  simp [Matrix.mulVec_smul, star_smul] <;> ring

theorem frS_pow (D : D7) (a : Fin (D.R.rS + 1)) (h : a.val < D.R.rS) :
    frS D ^ (D.R.rS - a.val) = ((rhoF D a : ℝ) : ℂ) := by
  have hk : D.host.ka / (2 * Real.pi) = D.host.rdE⁻¹ := by
    simp only [Formalism.BasicNotions.Host.ka, Formalism.BasicNotions.Host.v]
    rcases eq_or_ne D.host.rdE 0 with h0 | h0
    · simp [h0]
    · have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
  have hr : 0 ≤ D.host.rdE := Real.rpow_nonneg (abs_nonneg _) _
  unfold frS rhoF
  rw [← Complex.ofReal_pow, hk]
  congr 1
  rw [Real.rpow_neg hr, show (D.R.rS : ℝ) - ((a : ℕ) : ℝ) = ((D.R.rS - a.val : ℕ) : ℝ) by
    rw [Nat.cast_sub h.le], Real.rpow_natCast, inv_pow]

theorem rhoF_last (D : D7) : rhoF D (Fin.last D.R.rS) = 1 := by
  simp [rhoF]

theorem Q_fvec (u : D.what₂.Word) (τ : D.what₂.Tau) (a : Fin (D.R.rS + 1)) :
    C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a =
      ((rhoF D a : ℝ) : ℂ) • rv X.B.I (vOf X τ) (X.crd ((X.Fu u).fvec a)) := by
  obtain ⟨_, hQQi, _, hfr⟩ := C.isT τ
  unfold Formalism.QuantumDeterminants.fvec
  split_ifs with h
  · have e := (hfr ⟨a.val, h⟩ ⟨a.val, h⟩ rfl).1
    unfold Formalism.QuantumDeterminants.bvec
    rw [e, frS_pow D a h]
    have hv : (X.Fu u).fvec a = X.eX ⟨a.val, h⟩ := by
      have ha : a = Fin.castSucc ⟨a.val, h⟩ := Fin.ext rfl
      conv_lhs => rw [ha]
      rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e u]
    rw [hv]
    rfl
  · have ha : a = Fin.last D.R.rS := Fin.ext (by rw [Fin.val_last]; have := a.isLt; omega)
    subst ha
    rw [rhoF_last, Complex.ofReal_one, one_smul]
    unfold zB
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec, FlagG.fvec, Fin.snoc_last, X.flagZVector u]
    rfl

theorem gram_holds {u u' : D.what₂.Word} (hL : FrameLiftEx hI u u') : GramTr W hI C u u' := by
  intro t τ a b
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hlin : IsFrameLift hI t (linOf hI t) := by
    unfold linOf
    rw [dif_pos (hL t)]
    exact (hL t).choose_spec
  have hrat : Formalism.L2.SG.TermOp.RatLink X (ptR hI t) (linOf hI t) := by
    have hex := Formalism.L2.SG.Pf.ratPt_holds D X (linOf hI t) hlin.1
    unfold ptR
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨M, _, hM1, _, hM3⟩ := hrat
  have hA : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamR hI C t τ) a b =
      hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a)
        (uMat ((ptR hI t).1 (vOf X τ)) *ᵥ (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) b)) := by
    unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm gamR Formalism.L2.SG.RealObj.trG hJ
    rw [← hH, ← star_dot_conjT]
    congr 1
    simp only [Matrix.mulVec_mulVec]
    congr 1
    rw [show (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ *
        (C.Qi τ * uMat ((ptR hI t).1 (vOf X τ)) * C.Q τ) =
      (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) * uMat ((ptR hI t).1 (vOf X τ)) * C.Q τ by
        simp only [Matrix.mul_assoc], hQQi]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hC : ∀ y, uMat ((ptR hI t).1 (vOf X τ)) *ᵥ rv X.B.I (vOf X τ) y =
      rv X.B.I (vOf X τ) ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
    intro y
    rw [hM1 (vOf X τ)]
    exact Formalism.L2.SG.Pf.Level.rv_mulVec X (vOf X τ) _ y
  have hfr : linOf hI t ((X.Fu u').fvec b) = (repF (tc hI t)).fl.fvec b := by
    refine Fin.lastCases ?_ (fun b' => ?_) b
    · simp only [FlagG.fvec, Fin.snoc_last]
      exact hlin.2.2
    · simp only [FlagG.fvec, Fin.snoc_castSucc]
      exact hlin.2.1 b'
  rw [hA, Q_fvec C u τ a, Q_fvec C u' τ b, Matrix.mulVec_smul, hC, ← hM3, hfr, hJ_smul_real,
    Formalism.L2.SG.Pf.Level.hJ_rv, X.φ_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
  refine congrArg (fun z => ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ z) ?_
  refine Eq.trans ?_ (congrFun (congrFun (zhatL_mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) (repF (tc hI t))) a) b).symm
  exact Formalism.L2.SG.PoincareInHH.Cut.hform_crd X _ _

end Gram

section Witt

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF))

theorem frameLiftEx_holds (u u' : D.what₂.Word) : FrameLiftEx hI u u' := fun t =>
  Formalism.L2.SG.Pf.WittFlags.flag_witt (tu_ne u') rfl (X.Fu u') (repF (tc hI t)).fl

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  first
    | (unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; positivity)
    | (unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; omega)
    | (simp [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]; omega)
    | (simp [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n])
    | (unfold Formalism.BasicNotions.Ranks.f Formalism.HC.Frame.n; positivity)
    | (unfold Formalism.BasicNotions.Ranks.f Formalism.HC.Frame.n; omega)
    | (simp [Formalism.BasicNotions.Ranks.f, Formalism.HC.Frame.n])
    | (unfold Formalism.BasicNotions.Ranks.f; positivity)

end Witt

section UHmem

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)

private theorem conjTranspose_QiUQ_preserves_QJQ {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ)
    (Qi : Matrix (Fin m) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hQQi : Q * Qi = 1) (hU : Uᴴ * J * U = J) :
    (Qi * U * Q)ᴴ * (Qᴴ * J * Q) * (Qi * U * Q) = Qᴴ * J * Q := by
  have h1 : Qiᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQQi, Matrix.conjTranspose_one]
  calc (Qi * U * Q)ᴴ * (Qᴴ * J * Q) * (Qi * U * Q)
      = Qᴴ * (Uᴴ * (Qiᴴ * Qᴴ) * J * (Q * Qi) * U) * Q := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Qᴴ * J * Q := by rw [h1, hQQi, Matrix.mul_one, Matrix.mul_one, hU]

theorem trG_mem {n m : ℕ} {ε : Fin n → Bool} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (H : Matrix (Fin m) (Fin m) ℂ) (hQQi : Q * Qi = 1) (hH : Qᴴ * Formalism.REAL.Jm ε * Q = H) (g : Formalism.REAL.UJ ε) :
    Formalism.L2.SG.RealObj.trG Q Qi g ∈ Formalism.QuantumDeterminants.UH H := by
  show (Qi * _ * Q)ᴴ * H * (Qi * _ * Q) = H
  subst hH
  exact conjTranspose_QiUQ_preserves_QJQ _ Q Qi _ hQQi g.2

theorem gamR_mem {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau) :
    gamR hI C t τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  unfold gamR
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  exact trG_mem (C.Q τ) (C.Qi τ) _ hQQi hH ((ptR hI t).1 (vOf X τ))

end UHmem

section Scale

theorem rdE_pos (D : D7) : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.rpow_pos_of_pos
  exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))

variable {K : Type*} [Field K] (e : K →+* ℂ) (c : ℕ → ℂ)

def scaleBl : List (K × ℕ) → ℕ → List (ℂ × ℕ)
  | [], _ => []
  | (t, s) :: bs, o => (c (2 * o + s - 1) * e t, s) :: scaleBl bs (o + s)

theorem ptEntry_scaleBl (bs : List (K × ℕ)) (o i j : ℕ) :
    ptEntry (scaleBl e c bs o) i j = c (2 * o + i + j) * e (ptEntry bs i j) := by
  induction bs generalizing o i j with
  | nil => simp [scaleBl, ptEntry]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [scaleBl, ptEntry]
    split_ifs with h1 h2 h3
    · rw [show 2 * o + s - 1 = 2 * o + i + j by omega]
    · simp
    · rw [ih, show 2 * (o + s) + (i - s) + (j - s) = 2 * o + i + j by omega]
    · simp

theorem snd_scaleBl (bs : List (K × ℕ)) (o : ℕ) : (scaleBl e c bs o).map Prod.snd = bs.map Prod.snd := by
  induction bs generalizing o with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp [scaleBl, ih]

theorem mem_scaleBl (hc : ∀ n, c n ≠ 0) (bs : List (K × ℕ)) (hb : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (o : ℕ) :
    ∀ b ∈ scaleBl e c bs o, b.1 ≠ 0 ∧ 1 ≤ b.2 := by
  induction bs generalizing o with
  | nil => simp [scaleBl]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro x hx
    simp only [scaleBl, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have hts := hb (t, s) (List.mem_cons_self ..)
      exact ⟨mul_ne_zero (hc _) ((map_ne_zero e).2 hts.1), hts.2⟩
    · exact ih (fun b hb' => hb b (List.mem_cons_of_mem _ hb')) _ x hx

def scalePt (hc : ∀ n, c n ≠ 0) {N : ℕ} (w : Point K N) : Point ℂ N :=
  ⟨scaleBl e c w.1 0, mem_scaleBl e c hc w.1 w.2.1 0, by rw [snd_scaleBl]; exact w.2.2⟩

theorem ptMat_scalePt (hc : ∀ n, c n ≠ 0) {N : ℕ} (w : Point K N) (a b : Fin N) :
    ptMat (scalePt e c hc w) a b = c (a + b) * e (ptMat w a b) := by
  show ptEntry (scaleBl e c w.1 0) a.val b.val = _
  rw [ptEntry_scaleBl]
  simp [ptMat]

theorem inCell_scale {N : ℕ} (ρ : Fin N → ℂ) (hρ : ∀ a, ρ a ≠ 0) (hc : ∀ n, c n ≠ 0) (hρc : ∀ a b, ρ a * ρ b = c (a + b))
    (Z : Matrix (Fin N) (Fin N) K) (w : Point K N) (h : IsInCell Z w) :
    IsInCell (Matrix.of fun a b => ρ a * ρ b * e (Z a b)) (scalePt e c hc w) := by
  obtain ⟨L, U, hL, hU, hZ⟩ := h
  have hi1 : Matrix.diagonal (fun i => (ρ i)⁻¹) * Matrix.diagonal ρ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hρ i)
  have hi2 : Matrix.diagonal ρ * Matrix.diagonal (fun i => (ρ i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hρ i)
  refine ⟨Matrix.diagonal ρ * e.mapMatrix L * Matrix.diagonal (fun i => (ρ i)⁻¹),
    Matrix.diagonal (fun i => (ρ i)⁻¹) * e.mapMatrix U * Matrix.diagonal ρ, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, (hL i j).1 hij]
    · subst hij
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, (hL i i).2 rfl, hρ i]
  · intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, (hU i j).1 hij]
    · subst hij
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, (hU i i).2 rfl, hρ i]
  · have hP : ptMat (scalePt e c hc w) = Matrix.diagonal ρ * e.mapMatrix (ptMat w) * Matrix.diagonal ρ := by
      ext a b
      rw [ptMat_scalePt, ← hρc]
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
      ring
    have hZ' : (Matrix.of fun a b => ρ a * ρ b * e (Z a b)) =
        Matrix.diagonal ρ * e.mapMatrix Z * Matrix.diagonal ρ := by
      ext a b
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
      ring
    rw [hZ', hP, hZ, map_mul, map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal fun i => (ρ i)⁻¹) (Matrix.diagonal ρ), hi1, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.diagonal ρ) (Matrix.diagonal fun i => (ρ i)⁻¹), hi2, Matrix.one_mul]

end Scale

section Rel

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF)) {θ : ℝ}
  (C : Choice X θ)

theorem det_scaled {K : Type*} [Field K] {N : ℕ} (ρ : Fin N → ℂ) (M : Matrix (Fin N) (Fin N) K) (e : K →+* ℂ) :
    (Matrix.of fun i j => ρ i * ρ j * e (M i j)).det = (∏ i, ρ i) ^ 2 * e M.det := by
  have hM : (Matrix.of fun i j => ρ i * ρ j * e (M i j)) =
      Matrix.diagonal ρ * e.mapMatrix M * Matrix.diagonal ρ := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det]
  ring

theorem zhat_eq {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamR hI C t τ) =
      Matrix.of fun a b => ((rhoF D a : ℝ) : ℂ) * ((rhoF D b : ℝ) : ℂ) *
        embS D τ (ZhatL (lf D (FlagOfWord W u)) (fl'Of W hI t) a b) := by
  ext a b
  rw [gram_holds W hI C (frameLiftEx_holds hI u u') t τ a b, Matrix.of_apply]
  push_cast
  ring

theorem rhoF_pos (D : D7) (a : Fin (D.R.rS + 1)) : 0 < rhoF D a := by
  unfold rhoF
  exact Real.rpow_pos_of_pos (rdE_pos D) _

def cRho (D : D7) (n : ℕ) : ℂ := ((D.host.rdE ^ (-(2 * (D.R.rS : ℝ) - n)) : ℝ) : ℂ)

theorem cRho_ne (D : D7) (n : ℕ) : cRho D n ≠ 0 := by
  unfold cRho
  exact Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (rdE_pos D) _).ne'

theorem rho_mul (D : D7) (a b : Fin (D.R.rS + 1)) :
    ((rhoF D a : ℝ) : ℂ) * ((rhoF D b : ℝ) : ℂ) = cRho D (a + b) := by
  unfold cRho
  rw [← Complex.ofReal_mul]
  congr 1
  unfold rhoF
  rw [← Real.rpow_add (rdE_pos D)]
  congr 1
  push_cast
  ring

include W in

theorem inCell_real (hAt : ∀ u u', AtSome Y u u') {u u' : D.what₂.Word} (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hr : D.s.relevant t) (τ : D.what₂.Tau) :
    IsInCell (Formalism.MainNotions.S.ZhatO D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamR hI C t τ))
      (scalePt (embS D τ) (cRho D) (cRho_ne D) (D.s.ptOf t)) := by
  have hc := pt_cellC W hI hAt t hG hr
  have h := inCell_scale (embS D τ) (cRho D) (fun a => ((rhoF D a : ℝ) : ℂ))
    (fun a => Complex.ofReal_ne_zero.2 (rhoF_pos D a).ne') (cRho_ne D) (rho_mul D) _ _ hc
  convert h using 1
  ext a b
  unfold Formalism.MainNotions.S.ZhatO
  rw [zhat_eq W hI C t τ, Matrix.of_apply, Matrix.of_apply]
  unfold ZhatOM
  rw [map_mul, map_pow, map_neg, map_one]
  ring

end Rel

section GfSec

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF)) {θ : ℝ}
  (C : Choice X θ)

theorem tz_zB (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) = ((Tu D u : ℕ) : ℝ) := by
  obtain ⟨_, _, hH, _⟩ := C.isT τ
  have hz : Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) (Fin.last D.R.rS) = zB X (C.Qi τ) u τ := by
    unfold Formalism.QuantumDeterminants.fvec
    rw [dif_neg (by simp)]
  have hQ := Q_fvec C u τ (Fin.last D.R.rS)
  rw [hz, rhoF_last, Complex.ofReal_one, one_smul] at hQ
  have hl : (X.Fu u).fvec (Fin.last D.R.rS) = X.zu u := by
    rw [FlagG.fvec, Fin.snoc_last, X.flagZVector u]
  rw [hl] at hQ
  unfold Formalism.QuantumDeterminants.Tz Formalism.QuantumDeterminants.herm
  rw [← hH, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, star_dot_conjT, hQ]
  have h2 := Formalism.L2.SG.Pf.Level.hJ_rv X (vOf X τ) (X.crd (X.zu u)) (X.crd (X.zu u))
  unfold hJ at h2
  rw [h2, X.φ_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
  have h3 := Formalism.L2.SG.PoincareInHH.Cut.hform_crd X (X.zu u) (X.zu u)
  have h4 : (VS D).hT (X.zu u) (X.zu u) = -((Tu D u : ℕ) : D.host.E) := by
    have := (X.Fu u).z_norm
    rwa [X.flagZVector u] at this
  rw [show X.ιE (Formalism.L2.SG.Pf.Level.hE X (X.crd (X.zu u)) (X.crd (X.zu u))) = (VS D).hT (X.zu u) (X.zu u) from h3, h4]
  simp

theorem dmin_eq {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau) (l : Fin (D.R.rS + 2)) :
    Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamR hI C t τ) l =
      (∏ i : Fin l.val, ((rhoF D (Fin.castLE (Nat.le_of_lt_succ l.isLt) i) : ℝ) : ℂ)) ^ 2 *
        embS D τ ((ZhatL (lf D (FlagOfWord W u)) (fl'Of W hI t)).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
          (Fin.castLE (Nat.le_of_lt_succ l.isLt))).det := by
  unfold Formalism.QuantumDeterminants.Dmin
  rw [zhat_eq W hI C t τ]
  rw [← det_scaled]
  rfl

end GfSec

section GfNe

theorem embS_star' (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embS D τ (star x) = starRingEnd ℂ (embS D τ x) := by
  rw [Formalism.BasicNotions.bridge_star_holds D.R D.host x]
  exact Formalism.MainNotions.BesselShellMomentBounds.plEmb_conj D τ x

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF)) {θ : ℝ}
  (C : Choice X θ)

theorem prod_rho_last (D : D7) :
    (∏ i : Fin (Fin.last (D.R.rS + 1)).val, ((rhoF D (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt) i) : ℝ) : ℂ)) =
      ∏ i : Fin (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).val,
        ((rhoF D (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt) i) : ℝ) : ℂ) := by
  show (∏ i : Fin (D.R.rS + 1), ((rhoF D i : ℝ) : ℂ)) = ∏ i : Fin D.R.rS, ((rhoF D (Fin.castSucc i) : ℝ) : ℂ)
  rw [Fin.prod_univ_castSucc, rhoF_last, Complex.ofReal_one, mul_one]

theorem normSq_sub_scaled_eq_zero {P x y : ℂ} {T T' : ℝ}
    (h : Complex.normSq (P ^ 2 * x) - T * T' * Complex.normSq (P ^ 2 * y) = 0) (hP : P ≠ 0) :
    Complex.normSq x - T * T' * Complex.normSq y = 0 := by
  have hP' : Complex.normSq (P ^ 2) ≠ 0 := fun h0 => pow_ne_zero 2 hP (Complex.normSq_eq_zero.1 h0)
  rw [Complex.normSq_mul, Complex.normSq_mul] at h
  have h2 : Complex.normSq (P ^ 2) * (Complex.normSq x - T * T' * Complex.normSq y) = 0 := by
    linear_combination h
  exact (mul_eq_zero.1 h2).resolve_left hP'

include W in

theorem gf_ne {u u' : D.what₂.Word} (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamR hI C t τ) ≠ 0 := by
  have hGv : Gval (lf D (FlagOfWord W u)) (fl'Of W hI t) ≠ 0 := by
    rw [← G_eqC W hI t]
    intro h0
    apply hG
    exact (algebraMap D.host.F D.host.E).injective (by rw [h0, map_zero])
  unfold Formalism.QuantumDeterminants.Gf
  rw [dmin_eq W hI C t τ, dmin_eq W hI C t τ, tz_zB C u τ, tz_zB C u' τ, prod_rho_last D]
  intro h0
  have hP0 : (∏ i : Fin (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).val,
      ((rhoF D (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt) i) : ℝ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Complex.ofReal_ne_zero.2 (rhoF_pos D _).ne'
  have h1 := normSq_sub_scaled_eq_zero h0 hP0
  apply hGv
  apply (embS D τ).injective
  show embS D τ (Gflag (FlagOfWord W u) (fl'Of W hI t).fl) = embS D τ 0
  unfold Gflag Dl leadMinorE
  rw [dif_pos le_rfl, dif_pos (Nat.le_succ _), map_zero, map_sub, map_mul, map_mul, map_mul, map_mul,
    embS_star' D τ, embS_star' D τ, Complex.mul_conj, Complex.mul_conj, map_natCast,
    map_natCast]
  exact_mod_cast h1

theorem relPtEx_holds (u u' : D.what₂.Word) : RelPtEx hI C u u' := by
  obtain ⟨W⟩ := Formalism.L2.SG.Pf.WittFlags.WittExists_holds D X
  intro t hG hr τ
  exact ⟨_, gamR_mem hI C t τ, inCell_real W hI C (Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y) t hG hr τ,
    gf_ne W hI C t hG τ⟩

end GfNe

section Cons

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

def loopTermOf (H : TieHyp W hI) (A : AmpDat X) (hV : PvalForm W hI A) (large₂ : SizeData₂ D) (C1 : ℝ) {θ : ℝ}
    (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (hθ : normWin D large₂ C1 θ)
    (hW : ∀ τ, GoodW D τ u u' θ (locW C u u' τ)) (hS : ∀ τ, GoodS D (lamD D τ) (locS hB u u' τ))
    (hR : RMeasEx hI C u u') (hPin : PinAll (Y := Y) u u') (hCv : CovolPos (Y := Y) u u')
    (hZ : JZeroIff hI C hB u u') (hT : ThetaWin hI C hB large₂ C1 u u')
    :
    LoopTermDat D large₂ (termTieOf W hI H A hV) u u' C1 (locB large₂ C1 C hB u u' hθ hW hS) where
  γ := gamR hI C
  pt := ptC hI C
  θR := fun t _ => thetaS hI C hB t
  νR := nuR hI C hB
  volR := volRC hI
  volR_pos := volRC_pos hI hPin hCv
  gram := gram_holds W hI C (frameLiftEx_holds hI u u')
  rel := fun t hg hr τ => ⟨ptC_spec hI C t τ (relPtEx_holds hI C u u' t hg hr τ), hT t hg hr, rmeas_nuR hI C hB hPin hCv t τ (hR t hg hr τ)⟩
  J_irr := fun t _ hn => jt_irr hI Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
    Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds t hn
  J_norm := fun t hg hr => jnorm hI C hB hPin hCv hZ (tau_nonempty D) t hg hr

end Cons

section ThetaCut

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C)

def dnB (D : D7) (θ : ℝ) : Measure (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := Measure.pi fun _ => muNB D θ

def trInf (x : X.B.I.Ginf) : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun τ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ)))

def covN (u : D.what₂.Word) : ℝ := (dnB D θ (trInf C '' Y.FN u)).toReal

def ThetaEqN (u u' : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → 0 < hsNormSq (JtOf hI t) → 0 < P1 hI C hB t →
    thetaS hI C hB t ^ (2 * Fintype.card D.what₂.Tau) = covN (Y := Y) C u * covN (Y := Y) C u'

def CovWinN (large₂ : SizeData₂ D) (C1 : ℝ) (u u' : D.what₂.Word) : Prop :=
  normWin D large₂ C1 ((covN (Y := Y) C u * covN (Y := Y) C u') ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)))

theorem thetaWin_of {large₂ : SizeData₂ D} {C1 : ℝ} {u u' : D.what₂.Word} (hPin : PinAll (Y := Y) u u')
    (hCv : CovolPos (Y := Y) u u') (hE : ThetaEqN hI C hB u u') (hW : CovWinN (Y := Y) C large₂ C1 u u')
    (h1 : normWin D large₂ C1 1) : ThetaWin hI C hB large₂ C1 u u' := by
  intro t hG hr
  by_cases h : 0 < hsNormSq (JtOf hI t) ∧ 0 < P1 hI C hB t
  · have hE' := hE t hG hr h.1 h.2
    have hcard : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos_iff.2 (tau_nonempty D)
    have h0 : 0 ≤ thetaS hI C hB t := (thetaS_pos hI C hB hPin hCv t).le
    have hth : thetaS hI C hB t =
        (covN (Y := Y) C u * covN (Y := Y) C u') ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
      rw [← hE', ← Real.rpow_natCast, ← Real.rpow_mul h0]
      have he : ((2 * Fintype.card D.what₂.Tau : ℕ) : ℝ) * ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) = 1 := by
        have : (Fintype.card D.what₂.Tau : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
        push_cast
        field_simp
      rw [he, Real.rpow_one]
    rw [hth]
    exact hW
  · unfold thetaS
    rw [if_neg h]
    exact h1

end ThetaCut

section Assembly

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

def loopTieOf (H : TieHyp W hI) (A : AmpDat X) (hV : PvalForm W hI A) (hRR : RowRepsIso D) (large₂ : SizeData₂ D) (C1 : ℝ)
    {θ : ℝ} (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word)
    (hTI : FrameEqvInj (termTieOf W hI H A hV) (u' := u') (FlagOfWord W u)) (hθ : normWin D large₂ C1 θ)
    (hW : ∀ τ, GoodW D τ u u' θ (locW C u u' τ)) (hS : ∀ τ, GoodS D (lamD D τ) (locS hB u u' τ))
    (hR : RMeasEx hI C u u') (hPin : PinAll (Y := Y) u u') (hCv : CovolPos (Y := Y) u u')
    (hZ : JZeroIff hI C hB u u') (hT : ThetaWin hI C hB large₂ C1 u u') :
    LoopTie D large₂ (termTieOf W hI H A hV) u u' C1 :=
  loopTieOfParts (loopRowsOf W hI H A hV hRR u u' hTI) (locB large₂ C1 C hB u u' hθ hW hS)
    (loopTermOf W hI H A hV large₂ C1 C hB u u' hθ hW hS hR hPin hCv hZ hT)

end Assembly

section Fact

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C)

def JFactN (u u' : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    hsNormSq (JtOf hI t) * (covN (Y := Y) C u * covN (Y := Y) C u') = volRC hI t ^ 2 * P1 hI C hB t

theorem jZeroIff_of {u u' : D.what₂.Word} (hPin : PinAll (Y := Y) u u') (hCv : CovolPos (Y := Y) u u')
    (hJ : JFactN hI C hB u u') (hc : 0 < covN (Y := Y) C u * covN (Y := Y) C u') : JZeroIff hI C hB u u' := by
  intro t hG hr
  have h := hJ t hG hr
  have hv := volRC_pos hI hPin hCv t
  constructor
  · intro h0
    rw [h0, zero_mul] at h
    exact (mul_eq_zero.1 h.symm).resolve_left (pow_ne_zero 2 hv.ne')
  · intro h0
    rw [h0, mul_zero] at h
    exact (mul_eq_zero.1 h).resolve_right hc.ne'

theorem thetaEqN_of {u u' : D.what₂.Word} (hJ : JFactN hI C hB u u') : ThetaEqN hI C hB u u' := by
  intro t hG hr hJ0 hP0
  have h := hJ t hG hr
  have hcard : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos_iff.2 (tau_nonempty D)
  have hn : 2 * Fintype.card D.what₂.Tau ≠ 0 := by omega
  have hx : 0 ≤ volRC hI t ^ 2 * P1 hI C hB t / hsNormSq (JtOf hI t) :=
    div_nonneg (mul_nonneg (sq_nonneg _) hP0.le) hJ0.le
  unfold thetaS
  rw [if_pos ⟨hJ0, hP0⟩]
  rw [show (1 : ℝ) / (2 * Fintype.card D.what₂.Tau) = ((2 * Fintype.card D.what₂.Tau : ℕ) : ℝ)⁻¹ by
    push_cast; ring]
  rw [Real.rpow_inv_natCast_pow hx hn, div_eq_iff hJ0.ne']
  linear_combination -h

def loopTermOfN {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))
    (H : TieHyp W hI) (A : AmpDat X) (hV : PvalForm W hI A) (large₂ : SizeData₂ D) (C1 : ℝ) {θ : ℝ}
    (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (hθ : normWin D large₂ C1 θ)
    (hW : ∀ τ, GoodW D τ u u' θ (locW C u u' τ)) (hS : ∀ τ, GoodS D (lamD D τ) (locS hB u u' τ))
    (hR : RMeasEx hI C u u') (hPin : PinAll (Y := Y) u u') (hCv : CovolPos (Y := Y) u u')
    (hJ : JFactN hI C hB u u') (hc : 0 < covN (Y := Y) C u * covN (Y := Y) C u')
    (hCW : CovWinN (Y := Y) C large₂ C1 u u') (h1 : normWin D large₂ C1 1) :
    LoopTermDat D large₂ (termTieOf W hI H A hV) u u' C1 (locB large₂ C1 C hB u u' hθ hW hS) :=
  loopTermOf W hI H A hV large₂ C1 C hB u u' hθ hW hS hR hPin hCv (jZeroIff_of hI C hB hPin hCv hJ hc)
    (thetaWin_of hI C hB hPin hCv (thetaEqN_of hI C hB hJ) hCW h1)

end Fact

section Covol

open Set

variable {D : D7} {X : HidaSetting D} {Y : Full X}

theorem sinf_norm {u : D.what₂.Word} {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) {n : X.B.I.Ginf} (hn : n ∈ X.NinfU u) :
    a * n * a⁻¹ ∈ X.NinfU u := by
  obtain ⟨h, hh, n0, hn0, rfl⟩ := Formalism.L2.SG.Pf.Sinf.levi X u ha
  let hS := Formalism.L2.SG.Pf.NinfSub (I := X.B.I) X.eR (X.zR u)
  have h1 : n0 * n * n0⁻¹ ∈ X.NinfU u :=
    hS.mul_mem (hS.mul_mem (show n0 ∈ hS from hn0) (show n ∈ hS from hn)) (hS.inv_mem (show n0 ∈ hS from hn0))
  have h2 := Formalism.L2.SG.Pf.Sinf.conj_ninf X u hh h1
  have e : h * n0 * n * (h * n0)⁻¹ = h * (n0 * n * n0⁻¹) * h⁻¹ := by group
  rw [e]
  exact h2

theorem stInf_conj {u u' : D.what₂.Word} {γ γw s s' : X.B.I.Ginf} (hs : s ∈ X.SinfU u) (hs' : s' ∈ X.SinfU u')
    (hf : γ = s * γw * s'⁻¹) {x : X.B.I.Ginf} (hx : x ∈ Formalism.L2.SG.RealObj.StInf X u u' γw) :
    s * x * s⁻¹ ∈ X.NinfU u ∧ γ⁻¹ * (s * x * s⁻¹) * γ ∈ X.NinfU u' := by
  obtain ⟨hx1, hx2⟩ := hx
  subst hf
  refine ⟨sinf_norm hs hx1, ?_⟩
  have h2 : (s * γw * s'⁻¹)⁻¹ * (s * x * s⁻¹) * (s * γw * s'⁻¹) = s' * (γw⁻¹ * x * γw) * s'⁻¹ := by
    group
  rw [h2]
  exact sinf_norm hs' hx2

theorem stInf_conj_inv {u u' : D.what₂.Word} {γ γw s s' : X.B.I.Ginf} (hs : s ∈ X.SinfU u) (hs' : s' ∈ X.SinfU u')
    (hf : γ = s * γw * s'⁻¹) {y : X.B.I.Ginf} (hy : y ∈ X.NinfU u ∧ γ⁻¹ * y * γ ∈ X.NinfU u') :
    s⁻¹ * y * s ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := by
  obtain ⟨hy1, hy2⟩ := hy
  subst hf
  have hsi : s⁻¹ ∈ X.SinfU u := by
    first
      | exact (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)).inv_mem hs
      | exact (Formalism.L2.SG.Pf.SinfSub X.eR (X.zR u)).inv_mem hs
  have hs'i : s'⁻¹ ∈ X.SinfU u' := by
    first
      | exact (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u')).inv_mem hs'
      | exact (Formalism.L2.SG.Pf.SinfSub X.eR (X.zR u')).inv_mem hs'
  show s⁻¹ * y * s ∈ X.NinfU u ∧ γw⁻¹ * (s⁻¹ * y * s) * γw ∈ X.NinfU u'
  refine ⟨?_, ?_⟩
  · have h1 := sinf_norm hsi hy1
    rwa [inv_inv] at h1
  · have h2 := sinf_norm hs'i hy2
    have h3 : γw⁻¹ * (s⁻¹ * y * s) * γw =
        s'⁻¹ * ((s * γw * s'⁻¹)⁻¹ * y * (s * γw * s'⁻¹)) * s'⁻¹⁻¹ := by
      group
    rw [h3]
    exact h2

end Covol

end Formalism.L2.SG.LoopTerm
