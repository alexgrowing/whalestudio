import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Formalism.HermitianCurvature.BesselNonvanishingReduction

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped InnerProductSpace Classical ENNReal
open Matrix

namespace Formalism.L2.SG.LocWSOf

section Tr

variable {D : D7} (X : HidaSetting D)

def vOf (τ : D.what₂.Tau) : InfinitePlace X.B.I.F := X.pl.symm τ

def zB (Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Fin (2 * D.R.rS + D.R.k + 1) → ℂ :=
  Qi *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I (vOf X τ) (X.zR u)

def sigB (Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ) (τ : D.what₂.Tau)
    (m : MatKR D.R.k D.R.rS) : X.B.H (vOf X τ) →L[ℂ] X.B.H (vOf X τ) :=
  X.B.σ (vOf X τ) (Q * m * Qi)

def piB (Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (m : MatKR D.R.k D.R.rS) : X.Vloc u (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ) :=
  X.piLoc u (vOf X τ) (Formalism.L2.SG.RealObj.matQ (X.B.I.ε (vOf X τ)) (X.wfr u (vOf X τ)) (Q * m * Qi))

def muGB (Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ) (τ : D.what₂.Tau) :
    Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ))

end Tr

def muNB (D : D7) (θ : ℝ) : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) (kapN D θ)

def IsTranspC {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (lam : ℂ) (k r : ℕ)
    (Q : Matrix (Fin X.B.I.n) (Fin (2 * r + k + 1)) ℂ) (Qi : Matrix (Fin (2 * r + k + 1)) (Fin X.B.I.n) ℂ) : Prop :=
  Qi * Q = 1 ∧ Q * Qi = 1 ∧ Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q = Formalism.QuantumDeterminants.Hpk k r ∧
  ∀ (a : Fin r) (b : Fin D.R.rS), (a : ℕ) = b →
    Q *ᵥ Pi.single (Formalism.QuantumDeterminants.eI k r a) 1 = lam ^ (r - (a : ℕ)) • Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR b) ∧
    Q *ᵥ Pi.single (Formalism.QuantumDeterminants.esI k r a) 1 = (star (lam ^ (r - (a : ℕ))))⁻¹ • Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR b)

theorem isTransp_iff {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (g : ℝ) (k r : ℕ)
    (Q : Matrix (Fin X.B.I.n) (Fin (2 * r + k + 1)) ℂ) (Qi : Matrix (Fin (2 * r + k + 1)) (Fin X.B.I.n) ℂ) :
    Formalism.L2.SG.RealObj.IsTransp X v g k r Q Qi ↔
      IsTranspC X v (-(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ))) k r Q Qi := by
  first
  | exact Iff.rfl
  | (unfold Formalism.L2.SG.RealObj.IsTransp IsTranspC; exact Iff.rfl)

def frS (D : D7) : ℂ := ((D.host.ka / (2 * Real.pi) : ℝ) : ℂ)

def cfS (D : D7) : ℂ := -(Complex.I * ((((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)) : ℂ)) / (2 * (Real.pi : ℂ))

def torS (μ : ℂ) (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.diagonal fun i =>
    if i.val < r then μ ^ (r - i.val)
    else if r + k < i.val then (star (μ ^ (r - (2 * r + k - i.val))))⁻¹ else 1

def muT (D : D7) : ℂ := cfS D / frS D

def TorTie {D : D7} (X : HidaSetting D) : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ),
    IsTranspC X v (frS D) D.R.k D.R.rS Q Qi →
      IsTranspC X v (cfS D) D.R.k D.R.rS (Q * torS (muT D) D.R.k D.R.rS) (torS (muT D)⁻¹ D.R.k D.R.rS * Qi)

structure Choice {D : D7} (X : HidaSetting D) (θ : ℝ) where
  Q : D.what₂.Tau → Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ
  Qi : D.what₂.Tau → Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ
  isT : ∀ τ, IsTranspC X (vOf X τ) (frS D) D.R.k D.R.rS (Q τ) (Qi τ)
  y : D.what₂.Tau → MatKR D.R.k D.R.rS
  y_mem : ∀ τ, y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)
  y_low : ∀ τ, ∃ P, IsCayleyU D.R.k D.R.rS (epsSH D.R) P ∧
    sigB X (Q τ) (Qi τ) τ (y τ) (X.B.w (vOf X τ)) ∈
      lowKSub (epsSH D.R) (lamD D τ) (fun g => sigB X (Q τ) (Qi τ) τ (P⁻¹ * g * P))
  muW : D.what₂.Word → D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
  muW_haar : ∀ u τ, Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (Qi τ) u τ)) (muW u τ)
  muW_one : ∀ u τ, muW u τ Set.univ = 1
  nuS : D.what₂.Word → D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
  nuS_q : ∀ u τ, Formalism.MainNotions.S.IsQuotMeas (muGB X (Q τ) (Qi τ) τ) (muS (muW u τ) (muNB D θ)) (nuS u τ)

def ChoiceExists {D : D7} (X : HidaSetting D) (θ : ℝ) : Prop := 0 < θ → Nonempty (Choice X θ)

def Qcs {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) :
    Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ := C.Q τ * torS (muT D) D.R.k D.R.rS

def Qics {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ := torS (muT D)⁻¹ D.R.k D.R.rS * C.Qi τ

theorem isTransp_cs {D : D7} {X : HidaSetting D} {θ : ℝ} (h : TorTie X) (C : Choice X θ) (τ : D.what₂.Tau) :
    Formalism.L2.SG.RealObj.IsTransp X (vOf X τ) (((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)) D.R.k D.R.rS (Qcs C τ) (Qics C τ) :=
  (isTransp_iff X (vOf X τ) _ D.R.k D.R.rS (Qcs C τ) (Qics C τ)).2 (h (vOf X τ) (C.Q τ) (C.Qi τ) (C.isT τ))

section LocWSec

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def locW (C : Choice X θ) (u u' : D.what₂.Word) (τ : D.what₂.Tau) : LocW D.R.k D.R.rS where
  Wp := X.Vloc u (vOf X τ)
  Wq := X.Vloc u' (vOf X τ)
  π := piB X (C.Q τ) (C.Qi τ) u τ
  π' := piB X (C.Q τ) (C.Qi τ) u' τ
  z := zB X (C.Qi τ) u τ
  z' := zB X (C.Qi τ) u' τ
  μG := muGB X (C.Q τ) (C.Qi τ) τ
  μW := C.muW u τ
  μW' := C.muW u' τ
  μN := muNB D θ
  νS := C.nuS u τ
  νS' := C.nuS u' τ

def ColsTypeTr (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  IsColsType D u τ (zB X (C.Qi τ) u τ) (piB X (C.Q τ) (C.Qi τ) u τ)

def ZTr (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ) ∧ Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) = Tr D u

def HaarTr (C : Choice X θ) (τ : D.what₂.Tau) : Prop :=
  Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (muGB X (C.Q τ) (C.Qi τ) τ)

def PsiTr (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ m ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS,
    Formalism.L2.SG.HidaSetting.psiR (X.B.I.ε (vOf X τ)) X.B.g (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I (vOf X τ) (X.eR a))
      (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I (vOf X τ) (X.fR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I (vOf X τ) (X.zR u))
      (C.Q τ * m * C.Qi τ) = psiS D (zB X (C.Qi τ) u τ) m

theorem goodW_of (C : Choice X θ) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hc : ColsTypeTr C u τ) (hc' : ColsTypeTr C u' τ) (hz : ZTr C u τ) (hz' : ZTr C u' τ) (hh : HaarTr C τ) :
    GoodW D τ u u' θ (locW C u u' τ) := by
  have hz1 : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ) ∧ Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) = Tr D u := hz
  have hz2 : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (zB X (C.Qi τ) u' τ) ∧ Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u' τ) = Tr D u' := hz'
  unfold GoodW
  exact ⟨hc, hc', hz1.1, hz2.1, hz1.2, hz2.2, hh, C.muW_haar u τ, C.muW_one u τ, C.muW_haar u' τ, C.muW_one u' τ, rfl,
    C.nuS_q u τ, C.nuS_q u' τ⟩

end LocWSec

section LocSSec

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def WuBessel (C : Choice X θ) : Prop :=
  ∀ (u : D.what₂.Word) (τ : D.what₂.Tau), ∃ B : X.B.H (vOf X τ) → X.Vloc u (vOf X τ),
    IsBesselMapSm (k := D.R.k) (r := D.R.rS) (zB X (C.Qi τ) u τ) (psiS D (zB X (C.Qi τ) u τ))
      (sigB X (C.Q τ) (C.Qi τ) τ) (piB X (C.Q τ) (C.Qi τ) u τ) B ∧
    ∀ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), X.Wloc u (vOf X τ) γ = B (X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ)))

def bOf {C : Choice X θ} (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    X.B.H (vOf X τ) → X.Vloc u (vOf X τ) :=
  (hB u τ).choose

def v0Of (C : Choice X θ) (τ : D.what₂.Tau) : X.B.H (vOf X τ) :=
  sigB X (C.Q τ) (C.Qi τ) τ (C.y τ) (X.B.w (vOf X τ))

def phiOf {C : Choice X θ} (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) (m : MatKR D.R.k D.R.rS) :
    X.Vloc u (vOf X τ) :=
  bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ))

def cOf {C : Choice X θ} (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal / (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ)

def sclOf {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) : ℂ :=
  ((Real.sqrt (cOf hB u τ * (Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℝ) /
    (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal) : ℝ) : ℂ)

theorem isBesselMapSm_smul {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ}
    {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {B : H → Wp} (s : ℂ)
    (h : IsBesselMapSm (k := k) (r := r) z ψ σ π B) :
    IsBesselMapSm (k := k) (r := r) z ψ σ π (fun v => s • B v) := by
  obtain ⟨hadd, hsm, heq, hcw⟩ := h
  unfold IsBesselMapSm
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h' hh m hm v hv => ?_, ?_⟩
  · beta_reduce
    rw [hadd v hv w hw, smul_add]
  · beta_reduce
    rw [hsm c v hv, smul_comm]
  · beta_reduce
    rw [heq h' hh m hm v hv, map_smul, smul_comm]
  · obtain ⟨Cc, Ws, hW, hb⟩ := hcw
    unfold IsCWCont
    refine ⟨‖s‖ * Cc, Ws, hW, fun v hv => ?_⟩
    beta_reduce
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v hv) (norm_nonneg s)

def locS {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) : LocS (locW C u u' τ) where
  H := X.B.H (vOf X τ)
  σ := sigB X (C.Q τ) (C.Qi τ) τ
  B := bOf hB u τ
  B' := fun v => sclOf hB u u' τ • bOf hB u' τ v
  v0 := v0Of C τ
  cN := cOf hB u τ
  deg := D.dsig τ

theorem deg_eq {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    (locS hB u u' τ).deg = D.dsig τ := rfl

def GoodSRest {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam (lamD D τ) ∧
  IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ) ∧
  v0Of C τ ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) ∧ v0Of C τ ≠ 0 ∧
  0 < cOf hB u τ ∧
  l2SG (C.nuS u τ) (locS hB u u' τ).Φ =
    ENNReal.ofReal (cOf hB u τ * Module.finrank ℂ (X.Vloc u (vOf X τ))) ∧
  l2SG (C.nuS u' τ) (locS hB u u' τ).Φ' =
    ENNReal.ofReal (cOf hB u τ * Module.finrank ℂ (X.Vloc u' (vOf X τ))) ∧
  ∃ P, IsCayley D.R.k D.R.rS (epsSH D.R) P ∧
    IsFdeg (((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
      (fun g => sigB X (C.Q τ) (C.Qi τ) τ (P⁻¹ * g * P)) (D.dsig τ)

theorem goodS_of {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (h : GoodSRest hB u u' τ) : GoodS D (lamD D τ) (locS hB u u' τ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold GoodS
  exact ⟨h1, h2, (hB u τ).choose_spec.1, isBesselMapSm_smul _ (hB u' τ).choose_spec.1, h3, h4, C.y_low τ, h5, h6, h7, h8⟩

end LocSSec

section Wloc

open Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas

def BesselOfW : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (lam : Fin (2 * r + k + 1) → ℝ)
    (ε : Fin (2 * r + k + 1) → Bool) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h →
    Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → c ≠ 0 →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r ε lam σ w →
  ∀ μG μW μN ν : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r),
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → IsQuotMeas μG (muS μW μN) ν →
  ∀ W : Mat k r → Vp, ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) →
    IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W →
    (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x) →
    l2SG ν W ≠ 0 → l2SG ν W < ⊤ →
  ∃ B : H → Vp, IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B ∧
    ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x = B (σ x w)

def wT {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) (m : MatKR D.R.k D.R.rS) :
    X.Vloc u (vOf X τ) :=
  if h : ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ = C.Q τ * m * C.Qi τ then X.Wloc u (vOf X τ) h.choose else 0

def LocFactor {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) : Prop :=
  ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    X.B.w (vOf X τ) ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) ∧ ‖X.B.w (vOf X τ)‖ = 1 ∧
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ)) (muS (C.muW u τ) (muNB D θ)) ∧
    ContinuousOn (wT C u τ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    IsSPsiEquiv (zB X (C.Qi τ) u τ) (psiS D (zB X (C.Qi τ) u τ)) (piB X (C.Q τ) (C.Qi τ) u τ) (wT C u τ) ∧
    (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
        eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ) (X.B.w (vOf X τ)) (Matrix.of g) •
          wT C u τ (x * Matrix.of g)) (muGB X (C.Q τ) (C.Qi τ) τ) ∧
      rconv (muGB X (C.Q τ) (C.Qi τ) τ) (eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ)
        (X.B.w (vOf X τ))) (wT C u τ) x = wT C u τ x) ∧
    l2SG (C.nuS u τ) (wT C u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (wT C u τ) < ⊤

def WuBesselOfLoc {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → BesselOfW → LocFactor C →
    (∀ τ, IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ)) →
    (∀ τ, HaarTr C τ) → (∀ u τ, ColsTypeTr C u τ) → WuBessel C

end Wloc

end Formalism.L2.SG.LocWSOf
