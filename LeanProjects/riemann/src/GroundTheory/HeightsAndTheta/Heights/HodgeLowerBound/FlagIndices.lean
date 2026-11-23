import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.LineModel
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.LineMu
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDimX
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsZhangLowerX
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def AmpleOnGenericFibre (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  ∀ (W : Ideal (MRing ι)) (d : ℕ), 1 ≤ d → IsArithVar W (d + 1) → P ≤ W → 0 < geomDeg W A d

def OffBoundary (Bd : Set ((Σ k, ι k) → ℂ)) (W : Ideal (MRing ι)) : Prop :=
  ∀ z ∈ mcPts W, z ∉ Bd

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

structure ComponentSetting (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] where

  H : HodgeData D

  Cd : CuspData D O Lt

  M : XModel D

  S : LogLogRegularisationSetting M D.Xo (muLine H)

  S_tied : S.IsTied

  S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)

  S'_tied : S'.IsTied

  rd : ℝ

  Lval : ℝ

namespace ComponentSetting

variable {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
  (X : ComponentSetting D O Lt)

abbrev MUq (B p q : ℕ) (t' : ℝ) : HermLine ι := MUc X.H X.S' B p q t'

def La (B : ℕ) : ℝ := abelian₂ B X.rd X.Lval

end ComponentSetting

variable {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

def CuspBundlePos (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsSemipositiveH (mCoordIdeal D.y) (X.MUq B p q t') ∧
      NefOnFibres (mCoordIdeal D.y) (X.MUq B p q t').a ∧
      AmpleOnGenericFibre (mCoordIdeal D.y) (X.MUq B p q t')

def HtInterior (Ch : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * X.La B) - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W

def HtBoundary (Ch : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → ¬ OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * X.La B) - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W

def CuspMean (Cu : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  1 ≤ D.j' → 3 * D.j' + 1 ≤ D.N → ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B →
    meanU X.H X.Cd ≤ Cu * D.f * D.j' * X.La B

def StokesLimit.Hyp (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ) : Prop :=
  ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ((D.n + 1 : ℕ) : ℝ) * (a - (p : ℝ) / q * D.KA) * geomDegMUc X.H X.S' B p q t' ≤
      topMUc X.H X.S' B p q t'

def StokesLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ),
    IsIntersectionSystem II → 4 * D.f + 2 ≤ B → ArLimExists X.H X.S B → StokesLimit.Hyp X B a →
      ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B

def GrassmannianHeightZTwo.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (cf : ℚ) (e : ℝ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j ≤ N - 1 → 0 < Jint Ψ N j cf →
    (∀ Z : Matrix (Fin (N - j)) (Fin j) ℂ, (∀ a b, ‖Z a b‖ = 1) →
      1 / 2 * Real.log (1 + Z * Z.conjTranspose).det.re ≤ e) →
    -hFl Ψ N II (FA Ψ N j cf) ≤
      ((dimN Ψ N j + 1 : ℕ) : ℝ) * (Jint Ψ N j cf : ℝ) * (Fintype.card Ψ : ℝ) * e

def MUConjInvariant (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsConjInvariantH (X.MUq B p q t')

def slX (X : ComponentSetting D O Lt) (B : ℕ) : ℝ :=
  arLim X.H X.S B / (((D.n + 1 : ℕ) : ℝ) * degMu X.H)

def LowerBoundComponent.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (Ch Cu : ℝ),
    IsIntersectionSystem II → CuspBundlePos X → MUConjInvariant X → HtInterior Ch X → HtBoundary Ch X →
    CuspMean Cu X → 0 < degMu X.H → 3 * D.j' + 1 ≤ D.N →
    ∀ B : ℕ, 4 * D.f + 2 ≤ B → 4 * D.f * D.N ^ 2 ≤ B → ArLimExists X.H X.S B →
      -((Ch + Cu / 2) * D.f * D.j' * X.La B) ≤ slX X B

namespace Line

theorem grassmannianHeightZTwo_hypotheses :
    2 ≤ 2 ∧ 1 ≤ 1 ∧ 1 ≤ 2 - 1 ∧ 0 < Jint Unit 2 1 (-1) ∧
    ∀ Z : Matrix (Fin (2 - 1)) (Fin 1) ℂ, (∀ a b, ‖Z a b‖ = 1) →
      1 / 2 * Real.log (1 + Z * Z.conjTranspose).det.re ≤ 1 / 2 * Real.log 2 := by
  refine ⟨le_rfl, le_rfl, le_rfl, by rw [Jint_line]; norm_num, fun Z hZ => le_of_eq ?_⟩
  have h1 : ‖Z 0 0‖ = 1 := hZ 0 0
  have hdet : (1 + Z * Z.conjTranspose).det = 1 + Z 0 0 * starRingEnd ℂ (Z 0 0) := by
    have h := Matrix.det_fin_one (1 + Z * Z.conjTranspose : Matrix (Fin 1) (Fin 1) ℂ)
    refine h.trans ?_
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hdet, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
  norm_num

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

def projLineComponentSetting : ComponentSetting (lineData II hII) GaussianInt GaussianInt where
  H := lineHodge II hII
  Cd := gaussCusp II hII
  M := lineModel
  S := lineRegT II hII
  S_tied := lineRegT_tied II hII
  S' := lineBRegC II hII
  S'_tied := lineBRegC_tied II hII
  rd := 1
  Lval := 0

theorem projLineComponentSetting_La (B : ℕ) : (projLineComponentSetting II hII).La B = Real.log B := by
  simp [ComponentSetting.La, projLineComponentSetting, abelian₂]

theorem zero_hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ zeroSystem Unit (PBlk 2) W 1 ![fsLine 2] :=
  fun _ _ => le_rfl

theorem htInterior_line : HtInterior 1 (projLineComponentSetting zeroSystem zero_hII) := by
  intro B p q hB _ _
  refine ⟨1, one_pos, fun t' _ _ W _ _ _ => ?_⟩
  have hB1 : (1 : ℝ) ≤ B := by
    have : 1 ≤ B := le_trans (by norm_num [lineData, ComponentData.f]) hB
    exact_mod_cast this
  have hL : 0 ≤ Real.log B := Real.log_nonneg hB1
  rw [projLineComponentSetting_La]
  have h0 : htMUc (projLineComponentSetting zeroSystem zero_hII).H (projLineComponentSetting zeroSystem zero_hII).S' B p q t' W = 0 := by
    simp [htMUc, zeroSystem]
  rw [h0]
  have hKA : (lineData zeroSystem zero_hII).KA = 0 := rfl
  rw [hKA]
  have : (0 : ℝ) ≤ 1 * ((lineData zeroSystem zero_hII).f : ℝ) * ((lineData zeroSystem zero_hII).j' : ℝ) *
      Real.log B := by
    have hf : ((lineData zeroSystem zero_hII).f : ℝ) = 1 := by norm_num [ComponentData.f]
    have hj : ((lineData zeroSystem zero_hII).j' : ℝ) = 1 := by norm_num [ComponentData.j', lineData]
    rw [hf, hj]; linarith
  linarith

theorem htBoundary_line : HtBoundary 1 (projLineComponentSetting zeroSystem zero_hII) := by
  intro B p q hB hp hpq
  obtain ⟨t₀, ht₀, h⟩ := htInterior_line B p q hB hp hpq
  exact ⟨t₀, ht₀, fun t' ht0 ht1 W hW hXW _ => h t' ht0 ht1 W hW hXW fun z _ => Set.notMem_empty z⟩

theorem cuspMean_line : CuspMean 1 (projLineComponentSetting II hII) := by
  intro _ _ B hB
  have hB1 : (1 : ℝ) ≤ B := by
    have : 1 ≤ B := le_trans (by norm_num [lineData, ComponentData.f]) hB
    exact_mod_cast this
  rw [projLineComponentSetting_La]
  have h0 : meanU (projLineComponentSetting II hII).H (projLineComponentSetting II hII).Cd = 0 := meanU_line
  rw [h0]
  have hf : ((lineData II hII).f : ℝ) = 1 := by norm_num [ComponentData.f]
  have hj : ((lineData II hII).j' : ℝ) = 1 := by norm_num [ComponentData.j', lineData]
  rw [hf, hj]
  have := Real.log_nonneg hB1
  linarith

theorem stokesLimit_hyp_line (B : ℕ) : StokesLimit.Hyp (projLineComponentSetting zeroSystem zero_hII) B 0 := by
  intro p q _ _
  refine ⟨1, one_pos, fun t' _ _ => ?_⟩
  have hKA : (lineData zeroSystem zero_hII).KA = 0 := rfl
  have h0 : topMUc (projLineComponentSetting zeroSystem zero_hII).H (projLineComponentSetting zeroSystem zero_hII).S' B p q t' = 0 := by
    simp [topMUc, zeroSystem]
  rw [h0, hKA]
  simp

theorem arLimExists_line (B : ℕ) :
    ArLimExists (projLineComponentSetting zeroSystem zero_hII).H (projLineComponentSetting zeroSystem zero_hII).S B :=
  ⟨0, tendsto_const_nhds⟩

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
