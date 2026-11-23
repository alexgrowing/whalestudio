import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.HermitianLattices.StatementMass
import Formalism.ThetaLiftIndependence.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

noncomputable section

open NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.LatticeIndexAndWeightTheory

export Formalism.MainNotions.S.UnitaryVolumeMass (KTwoParameterConditions TermsPP Kpp hNC CloudNodeShape q0 minkM)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Hyps

variable (D : D7) (large₂ : SizeData₂ D)

def Hyp (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0

end Hyps

def IsInertiaCyclotomicGeneratorElement {D : D7} {u u' : D.what₂.Word} (t : D.s.Term u u') : Prop :=
  D.s.relevant t ∧ D.s.Gterm t = 0 ∧ ¬ D.s.isId t

section TermObj

variable {D : D7} (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u')

def Iof : Submodule D.host.E (hS D).V := Isp (X.fl t).fl (X.fl' t).fl

def OrthogonalComplementV0 : Submodule D.host.E (hS D).V := perpS (hS D) (Xplus (X.fl t) ⊔ Xplus (X.fl' t))

def jOf : ℕ := D.R.rS - Module.finrank D.host.E (Iof X t)

def NDl (l : ℕ) : ℝ := (Nloc (ddS D) D.R.rS l (Dl (X.fl t).fl (X.fl' t).fl l) : ℝ)

def DelJ : ℝ := NDl X t (jOf X t)

def ends : Finset ℕ := blockEnds (X.fl t).fl (X.fl' t).fl (jOf X t)

def Db : ℝ := ∏ l ∈ ends X t, NDl X t l

def sg (H1 : ℝ) (τ : D.what₂.Tau) : ℝ :=
  (ends X t).fold max 1 (fun l =>
    absReal D.host.rdE (embS D τ) D.R.rS l (Dl (X.fl t).fl (X.fl' t).fl l) / (2 * H1) ^ (2 * D.R.rS))

def SublatticeInterSubspace : Submodule (𝓞 D.host.E) (hS D).V :=
  L0sub (X.abelian₂ t) (X.fl t) ⊓ toO (hS D) (Hp (X.abelian₂ t) (X.fl t) (X.fl' t))

def LaP : Submodule (𝓞 D.host.E) (hS D).V := La (X.abelian₂ t) (gS D) (X.fl t) (X.fl' t)

def ThP : Submodule (𝓞 D.host.E) (hS D).V :=
  Thp (X.abelian₂ t) (X.fl t) (X.fl' t) ⊔ toO (hS D) (Iof X t)

def gT : ℕ := idx (hS D) (SublatticeInterSubspace X t) (LaP X t)

def iT : ℕ := idx (hS D) (LaP X t) (ThP X t)

def b1T : ℕ :=
  idx (hS D) (XLam (X.abelian₂ t) (X.fl t))
    ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl t) (jOf X t))) ⊔ (X.abelian₂ t ⊓ toO (hS D) (Iof X t)))

def FrameHyp : Prop :=
  (X.fl t).fl.e = D.sp.hypE ∧ (X.fl t).fl.z = D.zmOf u ∧ IsRowLat D (X.fl t).fl (X.abelian₂ t) ∧
    FrameOK D (X.abelian₂ t) (X.fl' t)

end TermObj

def NF {D : D7} (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') : Prop :=
  ∃ j : ℕ, j ≤ D.R.rS ∧ (u = u' → 1 ≤ j) ∧
    (∀ a : ℕ, (∃ x ∈ Iof X t, x ≠ 0 ∧ (X.fl t).fl.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ D.R.rS)) ∧
    (∀ a : ℕ, (∃ x ∈ Iof X t, x ≠ 0 ∧ (X.fl' t).fl.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ D.R.rS)) ∧
    (∃ c : D.host.E, (X.fl' t).fl.z - c • (X.fl t).fl.z ∈ Xsp (X.fl t) ⊔ Xsp (X.fl' t) ∧
      c * star c * ((Tu D u : ℕ) : D.host.E) = ((Tu D u' : ℕ) : D.host.E)) ∧
    Dl (X.fl t).fl (X.fl' t).fl j ≠ 0 ∧
    (OrthogonalComplementV0 X t ⊓ Xsp (X.fl t) = Iof X t ∧ OrthogonalComplementV0 X t ⊔ Xsp (X.fl t) = (X.fl t).fl.XplusPerp) ∧
    (OrthogonalComplementV0 X t ⊓ Xsp (X.fl' t) = Iof X t ∧ OrthogonalComplementV0 X t ⊔ Xsp (X.fl' t) = (X.fl' t).fl.XplusPerp)

section Datum

variable {D : D7} (X : TermTie D) {u u' : D.what₂.Word}

def SameDC {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T) (F₁ F₂ : LFlag (hS D) D.R.rS T') : Prop :=
  ∃ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT,
    (∀ a : Fin D.R.rS, σ (F.fl.e a) - F.fl.e a ∈ Xflag F a.val) ∧ σ F.fl.z - F.fl.z ∈ Xsp F ∧
    (∀ a : Fin D.R.rS, σ (F₁.fl.e a) - F₂.fl.e a ∈ Xflag F₂ a.val) ∧ σ F₁.fl.z - F₂.fl.z ∈ Xsp F₂

def EtaOne (p : D.s.Pair u u') : Prop :=
  Lat.Th (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.beta p) =
    Hp (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p))

def SameDatum (t₁ t₂ : D.s.Term u u') : Prop :=
  ∃ p : D.s.Pair u u', D.s.pfst p = t₁ ∧ D.s.psnd p = t₂ ∧ EtaOne X p

def TermInj (u : D.what₂.Word) : Prop :=
  ∀ t t' : D.s.Term u u, X.abelian₂ t = X.abelian₂ t' → TEqv D (X.abelian₂ t) (X.fl t) (X.fl' t) (X.fl' t') → t = t'

def NormOK (u : D.what₂.Word) : Prop :=
  (∀ p : D.s.Pair u u, X.wRow p = Formalism.MainNotions.S.wRow D (X.fl (D.s.pfst p)).fl (X.abelian₂ (D.s.pfst p))) ∧
  ∀ t : D.s.Term u u, IsInertiaCyclotomicGeneratorElement t → ∃ p : D.s.Pair u u, D.s.pfst p = t ∧ D.s.psnd p = t ∧
    X.beta p = LinearEquiv.refl D.host.E (hS D).V ∧
    D.s.pval p = ((Formalism.MainNotions.S.wRow D (X.fl t).fl (X.abelian₂ t) * hsNormSq (X.Jt t) : ℝ) : ℂ)

def IndW (D : D7) (σ : (hS D).V ≃ₗ[D.host.E] (hS D).V) (h : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : Prop :=
  ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (h w) ∈ Submodule.span D.host.E (Set.range D.sp.hypE)

def AmpOK : Prop :=
  (∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), (X.fl t).fl.e = D.sp.hypE ∧ (X.fl t).fl.z = D.zmOf u) ∧
  ∃ (ρ : ∀ u : D.what₂.Word, ((D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) → (X.Hpi u →L[ℂ] X.Hpi u))
    (δ : ∀ u u' : D.what₂.Word, D.s.Term u u' → ((hS D).V ≃ₗ[D.host.E] (hS D).V)),
    (∀ u, ρ u 1 = ContinuousLinearMap.id ℂ (X.Hpi u) ∧
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ρ u (h * h') = (ρ u h).comp (ρ u h')) ∧
    (∀ u (K : Submodule ℂ (X.Hpi u)), (∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ x ∈ K, ρ u h x ∈ K) → K = ⊥ ∨ K = ⊤) ∧
    (∀ u u', u ≠ u' → ∀ P : X.Hpi u' →L[ℂ] X.Hpi u,
      (∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, (ρ u h).comp P = P.comp (ρ u' h)) → P = 0) ∧
    (∀ u u' (t : D.s.Term u u'), δ u u' t ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT ∧
      (∀ a, δ u u' t (D.sp.hypE a) = (X.fl' t).fl.e a) ∧ δ u u' t (D.zmOf u') = (X.fl' t).fl.z) ∧
    (∀ u u' (t : D.s.Term u u'), ∀ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT,
      (∀ x ∈ Xplus (X.fl t) ⊔ Xplus (X.fl' t), σ x = x) →
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
        IndW D σ h → IndW D ((δ u u' t)⁻¹ * σ * δ u u' t) h' → (ρ u h).comp (X.Jt t) = (X.Jt t).comp (ρ u' h')) ∧
    ∀ u (t : D.s.Term u u), IsInertiaCyclotomicGeneratorElement t → NF X t → ∀ x ∈ OrthogonalComplementV0 X t, δ u u t x - x ∈ Xsp (X.fl' t)

def TieOK (u : D.what₂.Word) : Prop :=
  (∀ t : D.s.Term u u, FrameHyp X t) ∧ TermInj X u ∧ NormOK X u ∧ AmpOK X

def aboveSet (t₀ : D.s.Term u u) (i0 b0 : ℕ) : Set (D.s.Term u u) :=
  {t | IsInertiaCyclotomicGeneratorElement t ∧ SameDatum X t₀ t ∧ SameDC (X.fl t₀) (X.fl' t₀) (X.fl' t) ∧ iT X t = i0 ∧ b1T X t = b0}

theorem sameDatum_self {D : D7} {X : TermTie D} {u : D.what₂.Word} (hN : NormOK X u) {t : D.s.Term u u} (ht : IsInertiaCyclotomicGeneratorElement t) :
    SameDatum X t t := by
  unfold NormOK at hN
  obtain ⟨p, h1, h2, hb, -⟩ := hN.2 t ht
  unfold SameDatum
  refine ⟨p, h1, h2, ?_⟩
  unfold EtaOne
  rw [hb, h2, h1]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hy.1.1.1
  · intro x hx
    refine ⟨(x, x), ⟨⟨⟨hx, hx⟩, ?_⟩, ?_⟩, rfl⟩
    · simp
    · simp

end Datum

theorem frameHyp_of_loop {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u : D.what₂.Word} {C1 : ℝ}
    (Y : LoopTie D large₂ X u u C1) (t : D.s.Term u u) : FrameHyp X t := by
  have hfl := Y.fl_eq t
  unfold FrameHyp
  rw [hfl]
  exact ⟨Y.flag_e_eq_hyperbolic, Y.formsAtZero, Y.isRows.1 _ (Y.Lam_mem t), Y.frame_ok t⟩

section Terms

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

def adm1 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.st2aAny D large₂ C' Cl Cg cb Cu cT CT C0

def adm3 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stExpId D large₂ C' Cl Cg cb Cu cT CT C0

def ArchimedeanSignatureMatching (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stGpos D large₂ X C' Cl Cg cb Cu cT CT C0

def adm6 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stIdFlag D large₂ X C' Cl Cg cb Cu cT CT C0

def adm11 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stIrr D large₂ C' Cl Cg cb Cu cT CT C0

def adm7 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stCells D large₂ X C' Cl Cg cb Cu cT CT C0

end Terms

def adm5 : Prop :=
  UnitaryVolumeMass.stMinkM

def adm8 : Prop :=
  UnitaryVolumeMass.stSchurLem

section Size

variable (D : D7) (large₂ : SizeData₂ D)

def adm2 (C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH : ℝ) : Prop :=
  UnitaryVolumeMass.stSIZE D large₂ C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH

end Size

section Mass

variable (D : D7) (large₂ : SizeData₂ D)

def IntegrationByPartsAlt : Prop :=
  Formalism.HermitianLatticesTheory.IsCMUnram D.host.E → UnitaryVolumeMass.stMassRatio D

def LogThetaIdentity : Prop :=
  Formalism.HermitianLatticesTheory.IsCMUnram D.host.E → UnitaryVolumeMass.stMassL D

def RankTwoMassHypothesis (C' Cl Cg cb Cu cT CT C0 C : ℝ) : Prop :=
  UnitaryVolumeMass.stMass2K D large₂ C' Cl Cg cb Cu cT CT C0 C

def MassPairedLatticeBound (C' Cl Cg cb Cu cT CT C0 C : ℝ) : Prop :=
  (∀ (V V' : Type) [AddCommGroup V] [Module D.host.E V] [FiniteDimensional D.host.E V] [Module (𝓞 D.host.E) V]
      [IsScalarTower (𝓞 D.host.E) D.host.E V] [AddCommGroup V'] [Module D.host.E V'] [Module (𝓞 D.host.E) V']
      [IsScalarTower (𝓞 D.host.E) D.host.E V']
      (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (h' : V' →ₗ⋆[D.host.E] V' →ₗ[D.host.E] D.host.E)
      (M : Submodule (𝓞 D.host.E) V) (L' : Submodule (𝓞 D.host.E) V'),
      h.IsSymm → IsPosDef h → Module.finrank D.host.E V = 1 → Submodule.IsLattice D.host.E M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
      h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' 1 →
        Formalism.HermitianLatticesTheory.mass h M = Formalism.HermitianLatticesTheory.mass h' L') ∧
  (UnitaryVolumeMass.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ (V' : Type) [AddCommGroup V'] [Module D.host.E V'] [Module (𝓞 D.host.E) V'] [IsScalarTower (𝓞 D.host.E) D.host.E V']
      (h' : V' →ₗ⋆[D.host.E] V' →ₗ[D.host.E] D.host.E) (L' : Submodule (𝓞 D.host.E) V'),
      h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' 1 →
        Formalism.HermitianLatticesTheory.mass h' L' ≤ (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ C)

def DefiniteComplementMassVolumes (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig) : Prop :=
  UnitaryVolumeMass.stMassVol D G

def PlaneWaveLetters : Prop :=
  UnitaryVolumeMass.stLem3 D

def PlaneWaveIsometry : Prop :=
  ∀ u : D.what₂.Word, UnitaryVolumeMass.stLem3L0 D u

def adm12 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stFormK D large₂ C' Cl Cg cb Cu cT CT C0

end Mass

section Targets

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

def Conclusion1 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  (∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), IsInertiaCyclotomicGeneratorElement t → NF X t) ∧
  (∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), u ≠ u' → D.s.relevant t → D.s.Gterm t = 0 →
    D.s.aTerm u u' t = 0 ∧ (AmpOK X → X.Jt t = 0)) ∧
  (AmpOK X → ∀ (u : D.what₂.Word) (t : D.s.Term u u), IsInertiaCyclotomicGeneratorElement t → ∃ s : ℂ, X.Jt t = s • ContinuousLinearMap.id ℂ (X.Hpi u))

def T2 (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (CH Cs C : ℝ) : Prop :=
  ∀ u : D.what₂.Word, TieOK X u → ∀ t : D.s.Term u u, IsInertiaCyclotomicGeneratorElement t →
    Real.sqrt (hsNormSq (X.Jt t)) ≤ Real.sqrt (Module.finrank ℂ (X.Hpi u) : ℝ) *
      (om u t * (C / D.R.k) ^ ((jOf X t : ℝ) * ((D.R.k : ℝ) - 1 - jOf X t) * D.R.f) *
        DelJ X t ^ (-(((D.R.k : ℝ) - 1 - jOf X t) / 2)) *
        Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        ∏ τ, sg X t (large₂.sc.b ^ (CH * (D.R.m : ℝ))) τ ^ (-(Cs * D.R.k))) ∧
    DelJ X t ≤ Hb large₂.sc.b C D.R.m D.R.f * ∏ τ, sg X t (large₂.sc.b ^ (CH * (D.R.m : ℝ))) τ ^ 2 ∧
    ∀ l ∈ ends X t, NDl X t l ≤ Hb large₂.sc.b C D.R.m D.R.f * ∏ τ, sg X t (large₂.sc.b ^ (CH * (D.R.m : ℝ))) τ ^ 2

def LatticeIndicesFiniteBound : Prop :=
  ∀ u : D.what₂.Word, TieOK X u → ∀ t : D.s.Term u u, IsInertiaCyclotomicGeneratorElement t →
    0 < b1T X t ∧ 0 < gT X t ∧ 0 < iT X t ∧ (gT X t : ℝ) * (iT X t : ℝ) ^ 2 ≤ DelJ X t / (b1T X t : ℝ) ^ 2

def TermWeightSumAboveBound (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (C : ℝ) : Prop :=
  ∀ u : D.what₂.Word, TieOK X u → ∀ t₀ : D.s.Term u u, IsInertiaCyclotomicGeneratorElement t₀ → ∀ i0 b0 : ℕ, 1 ≤ i0 → 1 ≤ b0 →
    Summable (fun t : aboveSet X t₀ i0 b0 => om u t.1) ∧
    ∑' t : aboveSet X t₀ i0 b0, om u t.1 ≤
      ((i0 : ℝ) * b0) ^ (D.R.k : ℝ) * Hb large₂.sc.b C D.R.m D.R.f * (i0 : ℝ) ^ (1 + Real.logb 2 (2 * D.R.f)) *
        (Db X t₀ * DelJ X t₀ * NT D u) ^ (C * (D.R.rS : ℝ) ^ 3)

def Conclusion2 (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (C' Cl Cg cb Cu cT CT C0 CH Cs C : ℝ) : Prop :=
  Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → T2 D large₂ X om CH Cs C

def PointsLemma (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (C' Cl Cg cb Cu cT CT C0 C : ℝ) : Prop :=
  Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → LatticeIndicesFiniteBound D X ∧ TermWeightSumAboveBound D large₂ X om C

def TermWeightSummabilityBound (C' Cl Cg cb Cu cT CT C0 CH Cs C : ℝ) : Prop :=
  Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∃ om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ, (∀ u t, 0 < om u t) ∧
      T2 D large₂ X om CH Cs C ∧ LatticeIndicesFiniteBound D X ∧ TermWeightSumAboveBound D large₂ X om C

def Conclusion4 (C' Cl Cg cb Cu cT CT C0 C : ℝ) : Prop :=
  Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u : D.what₂.Word,
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
    ∀ reps : Finset (Submodule (𝓞 D.host.E) (D.sp.X 0).V),
      Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ (lf D F0)) reps →
    ∀ s : ℕ, 1 ≤ s → s < D.R.k → ∀ de : ℕ, 1 ≤ de →
      (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ *
          (cntPrim (D.sp.X 0).hT L' (D.R.k - s) de : ℝ≥0∞)) ≤
        (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹) *
          ENNReal.ofReal (C ^ (s * D.R.k * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ C *
            ((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (C * s + C * Real.log D.R.f))

def RelativePresentationLiterature (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stK2diag D large₂ C' Cl Cg cb Cu cT CT C0

def PairsWithFiniteGroup (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stK2off D large₂ C' Cl Cg cb Cu cT CT C0

def Conclusion5 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  RelativePresentationLiterature D large₂ C' Cl Cg cb Cu cT CT C0 ∧ PairsWithFiniteGroup D large₂ C' Cl Cg cb Cu cT CT C0

end Targets

theorem pairs_with_finite_group_of_parameters_bounds {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (h0 : adm11 D large₂ C' Cl Cg cb Cu cT CT C0) (h : Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0) :
    PairsWithFiniteGroup D large₂ C' Cl Cg cb Cu cT CT C0 := by
  unfold Conclusion1 at h
  unfold adm11 UnitaryVolumeMass.stIrr UnitaryVolumeMass.cIrr at h0
  intro hK u u' hne t hG
  by_cases hr : D.s.relevant t
  · exact ((h hK).2.1 u u' t hne hr hG).1
  · exact h0 hK.1 u u' t hr

section Packet

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

def admitted (C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH CM : ℝ) : Prop :=
  adm1 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH ∧ adm3 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm5 ∧
    adm6 D large₂ X C' Cl Cg cb Cu cT CT C0 ∧ adm7 D large₂ X C' Cl Cg cb Cu cT CT C0 ∧ adm8 ∧
    IntegrationByPartsAlt D ∧ LogThetaIdentity D ∧ RankTwoMassHypothesis D large₂ C' Cl Cg cb Cu cT CT C0 CM ∧ MassPairedLatticeBound D large₂ C' Cl Cg cb Cu cT CT C0 CM ∧ DefiniteComplementMassVolumes D G ∧
    PlaneWaveLetters D ∧ PlaneWaveIsometry D ∧
    adm11 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm12 D large₂ C' Cl Cg cb Cu cT CT C0

def Conclusion₂ (C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 : ℝ) : Prop :=
  Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0 ∧ TermWeightSummabilityBound D large₂ X C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity ∧
    Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 C4 ∧ Conclusion5 D large₂ C' Cl Cg cb Cu cT CT C0

def Stmt (C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH CM Cs ComplexParameterFamilyContinuity C4 : ℝ) : Prop :=
  admitted D large₂ X G C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH CM → (∀ u, TieOK X u) →
    Conclusion₂ D large₂ X C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4

def IntegralityFromMetric (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  adm6 D large₂ X C' Cl Cg cb Cu cT CT C0 ∧ adm8 ∧ adm11 D large₂ C' Cl Cg cb Cu cT CT C0 → AmpOK X → Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0

def ConsequenceOfAdmissibleConstants (C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH Cs ComplexParameterFamilyContinuity : ℝ) : Prop :=
  adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH ∧ adm3 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm7 D large₂ X C' Cl Cg cb Cu cT CT C0 →
    Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0 → TermWeightSummabilityBound D large₂ X C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity

def ThetaChernBoundOfLastLine (C' Cl Cg cb Cu cT CT C0 CM C4 : ℝ) : Prop :=
  IntegrationByPartsAlt D ∧ LogThetaIdentity D ∧ RankTwoMassHypothesis D large₂ C' Cl Cg cb Cu cT CT C0 CM ∧ MassPairedLatticeBound D large₂ C' Cl Cg cb Cu cT CT C0 CM ∧ DefiniteComplementMassVolumes D G ∧
    PlaneWaveLetters D ∧ PlaneWaveIsometry D →
    Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 C4

def GGFromIrreducibility (C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 : ℝ) : Prop :=
  adm1 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm3 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm5 ∧ adm11 D large₂ C' Cl Cg cb Cu cT CT C0 ∧
      adm12 D large₂ C' Cl Cg cb Cu cT CT C0 → (∀ u, TieOK X u) →
    Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0 → TermWeightSummabilityBound D large₂ X C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity →
    Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 C4 → Conclusion5 D large₂ C' Cl Cg cb Cu cT CT C0

end Packet

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))

def admF1 : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def admF2 : Prop := ∀ Cg cb Cu cT CT C0 Cθ C1 : ℝ, ∃ cq Cq CH : ℝ, 0 < cq ∧ 0 < Cq ∧
  OwnEv Fm fun C' Cl x i => adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH

def admF3 : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => adm3 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0
def admF6 : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, adm6 (Fm.D x i) (Fm.L x i) (At x hx i) C' Cl Cg cb Cu cT CT C0
def admF7 : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, adm7 (Fm.D x i) (Fm.L x i) (At x hx i) C' Cl Cg cb Cu cT CT C0
def FamilyMassFirstHypothesis : Prop := ∀ x (i : Fm.Ix x), IntegrationByPartsAlt (Fm.D x i)
def FamilyMassSecondHypothesis : Prop := ∀ x (i : Fm.Ix x), LogThetaIdentity (Fm.D x i)

def FamilyRankTwoMassHyp : Prop := ∀ Cg cb Cu cT CT C0 : ℝ, ∃ CM : ℝ,
  OwnEv Fm fun C' Cl x i => RankTwoMassHypothesis (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 CM

def FamilyMassLatticeBound : Prop := ∀ Cg cb Cu cT CT C0 : ℝ, ∃ CM : ℝ,
  OwnEv Fm fun C' Cl x i => MassPairedLatticeBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 CM

def FamilyComplementMassVolumes : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), DefiniteComplementMassVolumes (Fm.D x i) (Fm.ex x hx i).gauge
def FamilyRowsExist : Prop := ∀ x (i : Fm.Ix x), PlaneWaveLetters (Fm.D x i)

def FamilyWeylDimensionVandermondeQuotient : Prop := ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x), PlaneWaveIsometry (Fm.D x i)

def FamilyWeylAndVandermonde : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => adm11 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def FamilyTwelfthHypothesis : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => adm12 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def AdmF : Prop :=
  admF1 Fm ∧ admF2 Fm ∧ admF3 Fm ∧ adm5 ∧ admF6 Fm At ∧ admF7 Fm At ∧ adm8 ∧ FamilyMassFirstHypothesis Fm ∧ FamilyMassSecondHypothesis Fm ∧ FamilyRankTwoMassHyp Fm ∧
    FamilyComplementMassVolumes Fm ∧ FamilyRowsExist Fm ∧ FamilyWeylDimensionVandermondeQuotient Fm ∧ FamilyWeylAndVandermonde Fm ∧ FamilyTwelfthHypothesis Fm ∧ FamilyMassLatticeBound Fm

def TieF : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), TieOK (At x hx i) u

def Conclusion1Family : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, Conclusion1 (Fm.D x i) (Fm.L x i) (At x hx i) C' Cl Cg cb Cu cT CT C0

def FamilyTermWeightBounds : Prop := ∀ Cg cb Cu cT CT C0 Cs : ℝ, ∃ CH C : ℝ, 0 < C ∧
  OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, TermWeightSummabilityBound (Fm.D x i) (Fm.L x i) (At x hx i) C' Cl Cg cb Cu cT CT C0 CH Cs C

def SlopeLemmaFamily : Prop := ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, 0 < C ∧
  OwnEv Fm fun C' Cl x i => Conclusion4 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C

def FamilyKTwoFirstBound : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => RelativePresentationLiterature (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def FamilyKTwoSecondBound : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => PairsWithFiniteGroup (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def SlopeLossFamily : Prop := FamilyKTwoFirstBound Fm ∧ FamilyKTwoSecondBound Fm

def OrbitValuationBound : Prop := Conclusion1Family Fm At ∧ FamilyTermWeightBounds Fm At ∧ SlopeLemmaFamily Fm ∧ SlopeLossFamily Fm

def KudlaFamilyStatement : Prop := AdmF Fm At → TieF Fm At → OrbitValuationBound Fm At

def AmpF : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpOK (At x hx i)

def FamilyGlobalDerivation : Prop := admF6 Fm At ∧ adm8 ∧ FamilyWeylAndVandermonde Fm → AmpF Fm At → Conclusion1Family Fm At
def FamilyTermWeightImplication : Prop := admF2 Fm ∧ admF3 Fm ∧ admF7 Fm At → Conclusion1Family Fm At → FamilyTermWeightBounds Fm At
def FamilyMassToVolumeImplication : Prop :=
  FamilyMassFirstHypothesis Fm ∧ FamilyMassSecondHypothesis Fm ∧ FamilyRankTwoMassHyp Fm ∧ FamilyMassLatticeBound Fm ∧ FamilyComplementMassVolumes Fm ∧ FamilyRowsExist Fm ∧ FamilyWeylDimensionVandermondeQuotient Fm → SlopeLemmaFamily Fm
def FamilyProportionality : Prop :=
  admF1 Fm ∧ admF3 Fm ∧ adm5 ∧ FamilyWeylAndVandermonde Fm ∧ FamilyTwelfthHypothesis Fm → TieF Fm At → Conclusion1Family Fm At → FamilyTermWeightBounds Fm At → SlopeLemmaFamily Fm → SlopeLossFamily Fm

end Family

end Formalism.MainNotions.LatticeIndexAndWeightTheory

end
