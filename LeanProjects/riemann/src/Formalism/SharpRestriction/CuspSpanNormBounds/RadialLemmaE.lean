import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl

open Matrix MeasureTheory Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.RadialRuleConsequences

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (Jop scalMat mulAfter Op4 op4Mul tens1 tens2 RhOp thLog fsFun Umat modL JL TmatVStar ncGap
  IsPosDefZ zpt fhat headEl headLt levOf haarOf cutF energy Std lenI mid3 wnormSq IsKFinCoefT)

def adm1 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaB CB

def WittOrbitTheorem (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_gauge

def adm2b (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stA_herm C

def adm2c (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_capelli

def adm3a (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanTopCondition

def IntegralityRemainder (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_signs

def RTTRelation (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_rtt

def adm5 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_det

def HeckeCorrespondenceReflex (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_module C

def TelescopingFormStatement (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_tele

def ConjugateSelfDualCharacter (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_entry

def DualityInequality (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_dual C

def PlaneWaveIsometry (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanWaveCondition

def FrameIntegrationFormula (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stD C

def PositivityTheoremP (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stE C

def ArithmeticRiemannRochThetaCond (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stLetters

def LogThetaIdentity (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stThLog

def PlaneWaveLetters (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stWaveLetters

def CapelliEigenvalueAlt (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stCapEig

def adm2 (D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := WittOrbitTheorem D ∧ adm2b D CB ∧ adm2c D ∧ CapelliEigenvalueAlt D

def adm3b (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.DiagonalEntryIdentity

def adm3 (D : Formalism.BasicNotions.D7) : Prop := adm3a D ∧ adm3b D ∧ IntegralityRemainder D

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) : Prop := ArithmeticRiemannRochThetaCond D ∧ RTTRelation D

def TorsionSectionsReflex (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_rrherm C

def adm6 (D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := HeckeCorrespondenceReflex D CB ∧ TorsionSectionsReflex D CB

def adm7 (D : Formalism.BasicNotions.D7) : Prop := TelescopingFormStatement D ∧ ConjugateSelfDualCharacter D

def DualityForLists (_D : Formalism.BasicNotions.D7) (C Co Cd : ℝ) : Prop := 0 < Co ∧ S.UnitaryLevelOperators.stDualList C Co Cd

def adm8 (D : Formalism.BasicNotions.D7) (CB Co Cd : ℝ) : Prop := DualityInequality D CB ∧ DualityForLists D CB Co Cd

def IntegrationByPartsAlt (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stIBP

def adm9 (D : Formalism.BasicNotions.D7) : Prop := IntegrationByPartsAlt D ∧ LogThetaIdentity D

def adm10 (D : Formalism.BasicNotions.D7) : Prop := PlaneWaveLetters D ∧ PlaneWaveIsometry D

def adm11 (_D : Formalism.BasicNotions.D7) (CB Cv C1 C2 : ℝ) : Prop := 0 < C1 ∧ S.UnitaryLevelOperators.stLevel CB Cv C1 C2

def SliceBoundC (_D : Formalism.BasicNotions.D7) (Cs : ℝ) : Prop := S.UnitaryLevelOperators.stSlices Cs

def SmoothnessTheoremP (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := S.UnitaryLevelOperators.stSmooth CB

def SliceBoundE (_D : Formalism.BasicNotions.D7) (Cs : ℝ) : Prop := S.GramWordSpace.Slices Cs

def adm12 (D : Formalism.BasicNotions.D7) (CB Cs : ℝ) : Prop :=
  FrameIntegrationFormula D CB ∧ PositivityTheoremP D CB ∧ SliceBoundC D Cs ∧ SmoothnessTheoremP D CB ∧ SliceBoundE D Cs

def adm13 (D : Formalism.BasicNotions.D7) (c C₁ : ℝ) : Prop := S.UnitaryLevelOperators.stDecay D c C₁

def adm14 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stMarkov

def adm15 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stHerglotz

def adm16 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stPoisson

def adm17 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stStatPhase

def adm18 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stJSZ1

def Conclusion1 (D : Formalism.BasicNotions.D7) (Cg CI : ℝ) : Prop :=
  ∀ (k0 : ℕ) (hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS)
    (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) (I : Set ℝ) (N : ℕ)
    (f : Matrix (Fin (2 * D.R.rS + (k0 + 1) + 1)) (Fin (2 * D.R.rS + (k0 + 1) + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (χ : ℝ → ℝ) (w : Word),
    Std D hk L μsec I →
    InterlaceS (by omega : k0 + 1 ≤ 2 * D.R.rS + (k0 + 1) + 1) L.u L.lam →
    InterlaceS (by omega : k0 + 1 ≤ 2 * D.R.rS + (k0 + 1) + 1) L.u' L.lam →
    GapAtLeast L.ε L.lam (Cg * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * ((N : ℝ) * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3)) →
    D.R.rS + 1 ≤ N →
    CI * ((D.R.k : ℝ) * N * ((D.R.rS : ℝ) + 1) ^ 2 + (N : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2) ≤ sSup I - sInf I →
    IsKFinCoefT L.σ f → IsCutoff χ → Admissible I w → w.length ≤ N →
    Tendsto (fun ε : ℝ => energy L μsec I w (cutF L.z L.z' χ ε f)) (𝓝[>] 0)
      (𝓝 ((brkW L.lam (w.map Prod.snd) : ℂ) * L.beta μsec f f))

def Conclusion2 (D : Formalism.BasicNotions.D7) (C0 CA : ℝ) : Prop := S.UnitaryLevelOperators.stLemE' D C0 CA

def admitted (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) : Prop :=
  adm1 D CB ∧ adm2 D CB ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D CB ∧ adm7 D ∧ adm8 D CB Co Cd ∧ adm9 D ∧ adm10 D ∧
    adm11 D CB Cv C1 C2 ∧ adm12 D CB Cs ∧ adm13 D c C₁ ∧ adm14 D ∧ adm15 D ∧ adm16 D ∧ adm17 D ∧ adm18 D

def Stmt (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA : ℝ) : Prop :=
  admitted D CB Co Cd Cv C1 C2 Cs c C₁ → Conclusion1 D Cg CI ∧ Conclusion2 D C0 CA

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def admF1 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i) CB
def admF2 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i) CB
def admF3 : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)
def admF4 : Prop := ∀ x (i : Fm.Ix x), ArchimedeanSignatureMatching (Fm.D x i)
def admF5 : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i)
def admF6 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i) CB
def admF7 : Prop := ∀ x (i : Fm.Ix x), adm7 (Fm.D x i)
def admF8 (CB Co Cd : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm8 (Fm.D x i) CB Co Cd
def admF9 : Prop := ∀ x (i : Fm.Ix x), adm9 (Fm.D x i)
def FamilyRowsCountHypothesis : Prop := ∀ x (i : Fm.Ix x), adm10 (Fm.D x i)
def FamilyWeylAndVandermonde (CB Cv C1 C2 : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm11 (Fm.D x i) CB Cv C1 C2
def FamilyTwelfthHypothesis (CB Cs : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm12 (Fm.D x i) CB Cs
def FamilyThirteenthHypothesis (c C₁ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm13 (Fm.D x i) c C₁
def FamilyFourteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm14 (Fm.D x i)
def FamilyFifteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm15 (Fm.D x i)
def FamilySixteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm16 (Fm.D x i)
def FamilyStationaryPhase : Prop := ∀ x (i : Fm.Ix x), adm17 (Fm.D x i)
def FamilyBesselUniqueness : Prop := ∀ x (i : Fm.Ix x), adm18 (Fm.D x i)

def AdmF (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) : Prop :=
  admF1 Fm CB ∧ admF2 Fm CB ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm CB ∧ admF7 Fm ∧ admF8 Fm CB Co Cd ∧ admF9 Fm ∧
    FamilyRowsCountHypothesis Fm ∧ FamilyWeylAndVandermonde Fm CB Cv C1 C2 ∧ FamilyTwelfthHypothesis Fm CB Cs ∧ FamilyThirteenthHypothesis Fm c C₁ ∧ FamilyFourteenthHypothesis Fm ∧ FamilyFifteenthHypothesis Fm ∧ FamilySixteenthHypothesis Fm ∧
    FamilyStationaryPhase Fm ∧ FamilyBesselUniqueness Fm

def ConclusionF1 (Cg CI : ℝ) : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i) Cg CI

def ConclusionF2 (C0 CA : ℝ) : Prop := ∀ x (i : Fm.Ix x), Conclusion2 (Fm.D x i) C0 CA

def KudlaFamilyStatement (CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA : ℝ) : Prop :=
  AdmF Fm CB Co Cd Cv C1 C2 Cs c C₁ → ConclusionF1 Fm Cg CI ∧ ConclusionF2 Fm C0 CA

end Family

def UniformExportStatement : Prop :=
  ∀ CB Co Cd Cv C1 C2 Cs c C₁ : ℝ, ∃ Cg₀ CI₀ C0₀ CA₀ : ℝ, ∀ Cg ≥ Cg₀, ∀ CI ≥ CI₀, ∀ C0 ≥ C0₀, ∀ CA ≥ CA₀,
    ∀ D : Formalism.BasicNotions.D7, Stmt D CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA

theorem hsInner_smul_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (w : ℝ) (A B : Wq →L[ℂ] Wp) :
    hsInner ((w : ℂ) • A) ((w : ℂ) • B) = ((w ^ 2 : ℝ) : ℂ) * hsInner A B := by
  simp only [hsInner, _root_.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

theorem hsInner_zero_left {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (B : Wq →L[ℂ] Wp) : hsInner (0 : Wq →L[ℂ] Wp) B = 0 := by
  simp [hsInner]

theorem weight_eq (k0 r : ℕ) (T T' : ℝ) (x : Fin (r + 1) → ℂ) (hx : x ∈ OmX (r + 1))
    (hz : T * T' < Complex.normSq (zOf x)) :
    bcWeight (k0 + 1) r T T' (cOf x, zOf x) =
      (∏ a : Fin r, Complex.normSq (cOf x a))⁻¹ *
        ((∏ a : Fin r, ‖cOf x a‖ ^ (Mdim (k0 + 1) r a - 1)) *
          (Complex.normSq (zOf x) - T * T') ^ ((((k0 + 1 : ℕ) : ℝ) - 1) / 2)) ^ 2 := by
  have hG : 0 < Complex.normSq (zOf x) - T * T' := by linarith
  have h1 : ((Complex.normSq (zOf x) - T * T') ^ ((((k0 + 1 : ℕ) : ℝ) - 1) / 2)) ^ 2 =
      (Complex.normSq (zOf x) - T * T') ^ (k0 + 1 - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hG.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    simp
  have h2 : (∏ a : Fin r, Complex.normSq (cOf x a))⁻¹ * (∏ a : Fin r, ‖cOf x a‖ ^ (Mdim (k0 + 1) r a - 1)) ^ 2 =
      ∏ a : Fin r, ‖cOf x a‖ ^ (2 * (Mdim (k0 + 1) r a - 2)) := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hc : ‖cOf x a‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact hx _
    obtain ⟨n, hn⟩ : ∃ n, Mdim (k0 + 1) r a = n + 2 := ⟨2 * (r - a.val) + k0, by unfold Mdim; omega⟩
    rw [hn, Complex.normSq_eq_norm_sq]
    have e1 : n + 2 - 1 = n + 1 := by omega
    have e2 : n + 2 - 2 = n := by omega
    rw [e1, e2]
    field_simp
    ring
  unfold bcWeight
  rw [if_pos hz.le, mul_pow, h1, ← mul_assoc, h2]

theorem beta_eq_lbeta (k0 r : ℕ) (hk : 0 < k0) (L : LocBessel (k0 + 1) r)
    (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) (hc : L.c = cStd)
    (F F' : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) :
    L.beta μsec F F' = lbeta (levOf L μsec) (haarOf L μsec) F F' := by
  have hJ : ∀ G : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ → (L.Wq →L[ℂ] L.Wp),
      besselJ (k0 + 1) r L.z L.z' cStd L.π L.π' L.μW L.μN L.μW' G = L.J G := by
    intro G; funext g; simp only [LocBessel.J, hc]
  let e : (Fin (r + 1) → ℂ) ≃ᵐ (Fin r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℂ) (Fin.last r)).trans MeasurableEquiv.prodComm
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => ℂ) (Fin.last r)).trans
      (Measure.measurePreserving_swap (μ := (volume : Measure ℂ)) (ν := (volume : Measure (Fin r → ℂ))))
  have hex : ∀ x, e x = (cOf x, zOf x) := by
    intro x
    refine Prod.ext ?_ rfl
    funext a
    show x ((Fin.last r).succAbove a) = x a.castSucc
    rw [Fin.succAbove_last]
  unfold LocBessel.beta
  rw [← he.integral_comp' (g := fun p : (Fin r → ℂ) × ℂ =>
    (bcWeight (k0 + 1) r (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') p : ℂ) *
      hsInner (L.J F (bigCell (k0 + 1) r p.1 (μsec p.2))) (L.J F' (bigCell (k0 + 1) r p.1 (μsec p.2))))]
  show _ = ∫ x : Fin (r + 1) → ℂ, (((∏ a : Fin r, Complex.normSq (cOf x a))⁻¹ : ℝ) : ℂ) *
    hsInner (Wp := L.Wp) (Wq := L.Wq)
      (Btr (E := L.Wq →L[ℂ] L.Wp) (k0 + 1) r L.z L.z' μsec
        (besselJ (k0 + 1) r L.z L.z' cStd L.π L.π' L.μW L.μN L.μW' F) x)
      (Btr (E := L.Wq →L[ℂ] L.Wp) (k0 + 1) r L.z L.z' μsec
        (besselJ (k0 + 1) r L.z L.z' cStd L.π L.π' L.μW L.μN L.μW' F') x)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hex, hJ]
  by_cases hx : x ∈ BDom (k0 + 1) r L.z L.z'
  · simp only [Btr, if_pos hx]
    rw [hsInner_smul_smul, weight_eq k0 r _ _ x hx.1 hx.2]
    push_cast
    ring
  · simp only [Btr, if_neg hx, hsInner_zero_left, mul_zero]
    have hw : bcWeight (k0 + 1) r (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') (cOf x, zOf x) = 0 := by
      unfold bcWeight
      split_ifs with h
      · rcases h.lt_or_eq with h' | h'
        ·
          have hO : x ∉ OmX (r + 1) := fun hO => hx ⟨hO, h'⟩
          simp only [OmX, Set.mem_ofPred_eq, not_forall, not_not] at hO
          obtain ⟨l, hl⟩ := hO
          have hTT : 0 < Tz (k0 + 1) r L.z * Tz (k0 + 1) r L.z' := mul_pos L.hz.2 L.hz'.2
          have hl' : l ≠ Fin.last r := by
            rintro rfl
            have : Complex.normSq (zOf x) = 0 := by simp [zOf, hl]
            linarith
          obtain ⟨a, rfl⟩ : ∃ a : Fin r, a.castSucc = l := ⟨l.castPred hl', Fin.castSucc_castPred l hl'⟩
          have : (∏ a : Fin r, ‖cOf x a‖ ^ (2 * (Mdim (k0 + 1) r a - 2))) = 0 := by
            refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
            have : cOf x a = 0 := hl
            rw [this, norm_zero]
            refine zero_pow ?_
            have := a.isLt
            unfold Mdim; omega
          show (∏ a : Fin r, ‖cOf x a‖ ^ (2 * (Mdim (k0 + 1) r a - 2))) * _ = 0
          rw [this, zero_mul]
        · show _ * (Complex.normSq (zOf x) - _) ^ (k0 + 1 - 1) = 0
          rw [← h', sub_self, zero_pow (by omega), mul_zero]
      · rfl
    rw [hw]; simp

theorem levOf_Std {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ)
    (h : IsSection (k0 + 1) r L.z L.z' μsec) : (levOf L μsec).Std := ⟨L.hz.1, L.hz'.1, L.hz.2, L.hz'.2, h⟩

theorem lemma_E_mono_constants (D : Formalism.BasicNotions.D7) {Cg Cg' CI CI' : ℝ} (h1 : Cg ≤ Cg') (h2 : CI ≤ CI') (H : Conclusion1 D Cg CI) :
    Conclusion1 D Cg' CI' := by
  intro k0 hk L μsec I N f χ w hS hu hu' hg hN hI
  refine H k0 hk L μsec I N f χ w hS hu hu' ?_ hN ?_
  · intro a b hab
    refine le_trans ?_ (hg a b hab)
    gcongr
  · refine le_trans ?_ hI
    gcongr

theorem projector_bound_mono (D : Formalism.BasicNotions.D7) {C0 C0' CA CA' : ℝ} (h1 : C0 ≤ C0') (h2 : CA ≤ CA') (H : Conclusion2 D C0 CA) :
    Conclusion2 D C0' CA' := by
  intro k0 hk L μsec I N A p F0 χ w hS hN hA hF0 hp
  refine H k0 hk L μsec I N A p F0 χ w hS hN ?_ hF0 ?_
  · refine le_trans ?_ hA
    gcongr
  · refine le_trans ?_ hp
    gcongr

theorem Adm_of_AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {CB Co Cd Cv C1 C2 Cs c C₁ : ℝ}
    (hA : AdmF Fm CB Co Cd Cv C1 C2 Cs c C₁) (x : ℝ) (i : Fm.Ix x) : admitted (Fm.D x i) CB Co Cd Cv C1 C2 Cs c C₁ :=
  ⟨hA.1 x i, hA.2.1 x i, hA.2.2.1 x i, hA.2.2.2.1 x i, hA.2.2.2.2.1 x i, hA.2.2.2.2.2.1 x i, hA.2.2.2.2.2.2.1 x i,
    hA.2.2.2.2.2.2.2.1 x i, hA.2.2.2.2.2.2.2.2.1 x i, hA.2.2.2.2.2.2.2.2.2.1 x i, hA.2.2.2.2.2.2.2.2.2.2.1 x i,
    hA.2.2.2.2.2.2.2.2.2.2.2.1 x i, hA.2.2.2.2.2.2.2.2.2.2.2.2.1 x i, hA.2.2.2.2.2.2.2.2.2.2.2.2.2.1 x i,
    hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 x i, hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 x i,
    hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 x i, hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 x i⟩

theorem family_statement_of_parts {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA : ℝ}
    (H : ∀ D : Formalism.BasicNotions.D7, Stmt D CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA) :
    KudlaFamilyStatement Fm CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA := fun hA =>
  ⟨fun x i => (H _ (Adm_of_AdmF Fm hA x i)).1, fun x i => (H _ (Adm_of_AdmF Fm hA x i)).2⟩

theorem family_statement_of_uniform (H : UniformExportStatement) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) :
    ∃ Cg₀ CI₀ C0₀ CA₀ : ℝ, ∀ Cg ≥ Cg₀, ∀ CI ≥ CI₀, ∀ C0 ≥ C0₀, ∀ CA ≥ CA₀, ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps),
      KudlaFamilyStatement Fm CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA := by
  obtain ⟨a, b, c', d, h⟩ := H CB Co Cd Cv C1 C2 Cs c C₁
  exact ⟨a, b, c', d, fun Cg hg CI hI C0 h0 CA h1 _ Fm => family_statement_of_parts Fm (h Cg hg CI hI C0 h0 CA h1)⟩

theorem closed_statement_large_constants (𝒞 : Formalism.MainNotions.FamClass) (H : UniformExportStatement) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) :
    Formalism.MainNotions.Closed 𝒞 (fun Fm _ => KudlaFamilyStatement Fm CB Co Cd Cv C1 C2 Cs c C₁ (sCl Fm) (sCl Fm) (sCl Fm) (sCl Fm)) := by
  obtain ⟨a, b, c', d, h⟩ := H CB Co Cd Cv C1 C2 Cs c C₁
  refine ⟨1, one_pos, fun eps _ _ => ⟨{ pre := 0, t := fun _ => 0, mid := fun _ => 0, last := fun _ => max (max a b) (max c' d) }, fun Fm CH _ hL => ?_⟩⟩
  have hl : max (max a b) (max c' d) ≤ sCl Fm := (le_sC'_sCl hL).2
  exact family_statement_of_parts Fm (fun D => h _ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hl)
    _ (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hl)
    _ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hl)
    _ (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hl) D)

theorem levOf_HC {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ)
    (h : ∀ i, ∃ m : ℤ, L.u i - L.u' i = m) : (levOf L μsec).HC L.u L.u' := ⟨L.hπ, L.hπ', h⟩

theorem minWeight_pos (D : Formalism.BasicNotions.D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) : 0 < k0 := by
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  omega

end Formalism.MainNotions.RadialRuleConsequences
