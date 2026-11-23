import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CuspFamily
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E}

namespace ComponentFamilySetting

variable (X : ComponentFamilySetting D)

abbrev MUq (B p q : ℕ) (t' : ℝ) : HermLine ι := MUc X.H X.S' B p q t'

def NbarQ (B p q : ℕ) (t : ℝ) : HermLine ι :=
  smoothRep (mCoordIdeal D.y)
    (hermOfFun ι ((q : ℤ) • muTwDeg X.H B + (p : ℤ) • D.a') fun z =>
      (X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p)

def topN (B p q : ℕ) (t : ℝ) : ℝ :=
  II K ι (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B p q t) / (q : ℝ) ^ (D.n + 1)

def degN (B p q : ℕ) (t : ℝ) : ℝ :=
  geomDeg (mCoordIdeal D.y) (X.NbarQ B p q t) D.n / (q : ℝ) ^ D.n

def omN (B p q : ℕ) (t : ℝ) : Fin D.n → ((Σ k, ι k) → ℂ) → ℝ :=
  fun _ z => Real.log ((X.NbarQ B p q t).h z) / q

def wSt (B p q : ℕ) (t t' : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  (Real.log ((X.MUq B p q t').h z) - Real.log ((X.NbarQ B p q t).h z)) / q

def I0 (B p q : ℕ) (t t' : ℝ) : ℝ :=
  ptsIntegral (mCoordIdeal D.y) (X.omN B p q t) (X.wSt B p q t t')

def Vlim (B p q : ℕ) (t : ℝ) : ℝ :=
  ptsIntegral (mCoordIdeal D.y) (X.omN B p q t)
    (fun z => X.F.cuspCorr X.H z - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z)))

def Vb (B p q : ℕ) (t : ℝ) : ℝ :=
  ptsIntegral (mCoordIdeal D.y) (X.omN B p q t) (fun z => X.F.Uat z / 2)

def topNLim (B p q : ℕ) : ℝ := limUnder (𝓝[>] 0) (X.topN B p q)

def VbLim (B p q : ℕ) : ℝ := limUnder (𝓝[>] 0) (X.Vb B p q)

def degNLim (B p q : ℕ) : ℝ := limUnder (𝓝[>] 0) (X.degN B p q)

end ComponentFamilySetting

def CuspBundlePosFam (X : ComponentFamilySetting D) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsSemipositiveH (mCoordIdeal D.y) (X.MUq B p q t') ∧
      NefOnFibres (mCoordIdeal D.y) (X.MUq B p q t').a ∧
      AmpleOnGenericFibre (mCoordIdeal D.y) (X.MUq B p q t')

def StokesTelescopeFam.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (X : ComponentFamilySetting D) (B p q : ℕ) (t t' : ℝ),
    IsIntersectionSystem II → 1 ≤ q →
    IsSemipositiveH (mCoordIdeal D.y) (X.MUq B p q t') → IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t) →
      topMUc X.H X.S' B p q t' - X.topN B p q t ≤ ((D.n + 1 : ℕ) : ℝ) * X.I0 B p q t t'

def NbarSemiposFam.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (X : ComponentFamilySetting D) (B p q : ℕ),
    1 ≤ p → p ≤ q → ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t : ℝ, 0 < t → t ≤ t₁ →
      IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t)

def StokesLimitTpFam.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (X : ComponentFamilySetting D) (B p q : ℕ),
    1 ≤ p → p ≤ q → ∃ t₂ : ℝ, 0 < t₂ ∧ ∀ t : ℝ, 0 < t → t ≤ t₂ →
      IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t) →
      Tendsto (X.I0 B p q t) (𝓝[>] 0) (𝓝 (X.Vlim B p q t)) ∧ X.Vlim B p q t ≤ X.Vb B p q t

def StokesLimitTFam.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (X : ComponentFamilySetting D) (B p q : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B → 1 ≤ p → p ≤ q →
      Tendsto (X.topN B p q) (𝓝[>] 0) (𝓝 (X.topNLim B p q)) ∧
      Tendsto (X.Vb B p q) (𝓝[>] 0) (𝓝 (X.VbLim B p q)) ∧
      Tendsto (X.degN B p q) (𝓝[>] 0) (𝓝 (X.degNLim B p q))

def StokesLimitEpsFam.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (X : ComponentFamilySetting D) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      Tendsto (fun m : ℕ => X.topNLim B 1 (m + 1)) atTop (𝓝 (arLim X.H X.S B)) ∧
      Tendsto (fun m : ℕ => X.VbLim B 1 (m + 1)) atTop (𝓝 (X.F.meanU X.H * degMu X.H / 2)) ∧
      Tendsto (fun m : ℕ => X.degNLim B 1 (m + 1)) atTop (𝓝 (degMu X.H))

def StokesLimitFamPos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (X : ComponentFamilySetting D) (B : ℕ) (a : ℝ),
    IsIntersectionSystem II → CuspBundlePosFam X → 4 * D.f + 2 ≤ B → ArLimExists X.H X.S B →
      StokesLimitFam.Hyp X B a →
      ((D.n + 1 : ℕ) : ℝ) * (a - X.F.meanU X.H / 2) * degMu X.H ≤ arLim X.H X.S B

section Bridge

variable {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
  (X : ComponentSetting D O Lt) (hXo : D.Xo.Nonempty)

end Bridge

namespace Line

open GroundTheory.Heights₂.Heights.LowerBoundFree.Line

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

def projLineFamilySetting : ComponentFamilySetting (lineData II hII) :=
  ComponentFamilySetting.componentFamilySetting_ofSetting (projLineComponentSetting II hII) (lineData_Xo_nonempty II hII)

end Line

end GroundTheory.Heights₂.Heights.NineStatements
