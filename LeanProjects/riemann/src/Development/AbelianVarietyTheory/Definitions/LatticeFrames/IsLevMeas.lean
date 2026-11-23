import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks)

namespace GlobalTheory.ChainTw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

structure Twist (D : D7) where
  Pg : Finset (Pl D.host.E)
  Q : Finset (Pl D.host.E)
  chi : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ
  ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ

open Classical in

structure Twist.Is (c : Com D) (w : Twist D) : Prop where
  com : c.Is
  union : c.Pg = w.Pg ∪ w.Q
  disj : Disjoint w.Pg w.Q
  chiPg : ∀ j, ∀ PP ∈ w.Pg, c.chi j PP = w.chi j PP
  chiQ : ∀ j, ∀ PP ∈ w.Q, c.chi j PP = (w.ξ PP)⁻¹
  ne : ∀ PP ∈ w.Q, w.ξ PP ≠ 1
  grp : ∀ g, g ∈ c.P.H ↔ ∀ PP : c.Pg, PP.1 ∈ w.Pg → g PP = 1
  chr : c.P.chi = 1

def flat (c : Com D) (w : Twist D) (j : ℕ) (s : PiLocalization₂ D) (hr : D.R.r ≤ s.V.rank) : PiLocalization₂ D :=
  { s with L := Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B }

def IsStage (c : Com D) (w : Twist D) (j : ℕ) (s : PiLocalization₂ D) : Prop :=
  ∃ hr, s.L = Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B ∧ (flat c w j s hr).Is c j

variable {c : Com D} {s s' : PiLocalization₂ D}

structure IsStep (w : Twist D) (j : ℕ) (p : Step c s s') : Prop where
  weil : IsWeilDatumO c.ψ s.V s'.V (c.chS j) (c.chT j) p.ω
  vec : ∃ f₀, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (w.chi j) w.Q w.ξ f₀ p.f
  theta : ∀ φ, IsThetaFunO c.ψ s.V s'.V (p.pt φ)
  it : IsItW c.θ s.M s'.M p.ω p.pt p.It
  io : Lift.IsIo s'.ν s'.fd (thetaKO p.ω) p.pt p.It (s'.CC c) (s.CC c) p.io

def ForStageQ (D : D7) (Φ : ∀ (_ : Com D) (_ : Twist D) (_ : ℕ) (_ : PiLocalization₂ D), Prop) : Prop :=
  ∀ (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → Φ c w j s

def ForStepQ (D : D7) (Φ : ∀ (c : Com D) (_ : Twist D) (_ : ℕ) (s s' : PiLocalization₂ D) (_ : Step c s s'), Prop) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, ∀ s s' : PiLocalization₂ D, IsStage c w k s → IsStage c w (k + 1) s' →
    ∀ p : Step c s s', IsStep w (k + 1) p → Φ c w k s s' p

def IsLocUnif {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ) : Prop :=
  ∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = ϖ ∧
    ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) = ValuativeRel.uniformizer (Fv D.host.F v)

def IsChart (s : PiLocalization₂ D) (k : ℕ) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V) : Prop :=
  ∃ ε : Fin D.R.r ⊕ Blocks k D.R.t ≃ Fin s.V.rank, (∀ i, (ε (.inl i) : ℕ) = i) ∧
    ∀ y, gAt s.V (.inl v) (ι y) = ι y ∧ (grpCo φ s.V (frCo φ s.β) (ι y)).1.submatrix ε ε = y.1

def qPar (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) : Multiset ℂˣ :=
  Nat.rec 0 (fun i B => B.map (· * (Circle.toUnits (c.chS (i + 1) x) * (Circle.toUnits (c.chT (i + 1) x))⁻¹)) +
    GlobalTheory.LFun.seg PP (Circle.toUnits (c.chS (i + 1) x)) D.R.t) k

def IsQFun (c : Com D) (w : Twist D) (k : ℕ) (s : PiLocalization₂ D) (F : GA D s.V → ℂ) : Prop :=
  ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ x ϖ, IsLocUnif φ x ϖ →
    ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s k φ ι →
      GlobalTheory.ParHecke.IsGen ((GlobalTheory.PRep.rightReg ℂ (GA D s.V) ℂ).comp ι) ξl ϖ (qPar c PP x k) fun g => conj (F g)

def IsQ (w : Twist D) (k : ℕ) (u : s.CC c) : Prop := ∀ v, IsQFun c w k s (PiLocalization₂.val u v)

def blockL (c : Com D) (k : ℕ) (PP : Pl D.host.E) : ℂ :=
  ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 D.R.t,
    ((1 - (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP : ℂ) * ((Ideal.absNorm PP.asIdeal : ℂ) ^ n)⁻¹) *
      (1 - (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP : ℂ)⁻¹ * ((Ideal.absNorm PP.asIdeal : ℂ) ^ n)⁻¹))⁻¹

def zinv (PP : Pl D.host.E) (a b : ℕ) : ℝ := ∏ n ∈ Finset.Ioc a b, (1 - ((Ideal.absNorm PP.asIdeal : ℝ) ^ n)⁻¹)

def locQ (c : Com D) (w : Twist D) (k : ℕ) : ℂ := ∏ PP ∈ w.Q, blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)

def levSet (s : PiLocalization₂ D) : Set (GA D s.V) := {g | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}

def IsLevMeas (s : PiLocalization₂ D) (mR : Measure (GinfC s.V)) : Prop :=
  mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR →
    (∀ b : GinfC s.V, ∀ κ ∈ Lev.levG s.V s.β s.L, F ((b : GA D s.V) * κ) = f b) →
      IntegrableOn F (levSet s) s.ν ∧ ∫ g in levSet s, F g ∂s.ν = ∫ b, f b ∂mR

def zReal (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank) (v : s.M.Vec)
    (g : GinfC s.V) : ℂ :=
  coefW p.ω m X (p.pt φ) g *
    conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)

def IsMajOf (c : Com D) (s : PiLocalization₂ D) (a : GL (Fin s.V.rank) (AE D)) : Prop :=
  GlobalTheory.Doubling.IsMaj s.V a ∧ ∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1

def RealConv (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank) (v : s.M.Vec)
    (mR : Measure (GinfC s.V)) : Prop :=
  (∀ τ, (v τ : s.M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin s.M τ) ∧ ∀ a, IsMajOf c s a →
    ∃ s₁ : ℝ, s₁ < (D.R.t : ℝ) / 2 ∧ Integrable (fun g : GinfC s.V => zReal p m X φ v g *
      ((∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (g : GA D s.V)) : ℝ) : ℂ) ^
        ((s₁ : ℂ) - (D.R.t : ℂ) / 2)) mR

def flatInt (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V)) (a : GL (Fin s.V.rank) (AE D))
    (φ : PolF D s'.V.rank s.V.rank) (F₁ F₂ : GA D s.V → ℂ) (z : ℂ) : GA D s.V → ℂ :=
  GlobalTheory.Core.Rk.IP.integrand p.ω s.ν m X s.Λ a (p.pt φ) (p.pt φ) (fun g => conj (F₁ g)) (fun g => conj (F₂ g)) z

def IsAdjVec (p : Step c s s') (ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ) (ipD' : SmT s'.M →ₗ[ℂ] SmT s'.M →ₗ⋆[ℂ] ℂ)
    (φ : PolF D s'.V.rank s.V.rank) (v : SmT s.M) (w₀ : SmT s'.M) : Prop :=
  w₀ ∈ s'.KF ∧ ∀ w ∈ s'.KF, ipD' w w₀ = ipD (p.It φ w) v

def IsHval (c : Com D) (S : Set (HeightOneSpectrum (𝓞 D.host.F))) (k : ℕ) (H : ℂ) : Prop :=
  ∃ Λ : ℕ → ℂ → ℂ, (∀ i ∈ Finset.Icc 1 k, Differentiable ℂ (Λ i) ∧ ∀ z : ℂ, 1 < z.re → Λ i z =
      GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E S) (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) w}) z) ∧
    H = ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 D.R.t, Λ i n

def dS (S : Set (HeightOneSpectrum (𝓞 D.host.F))) (s s' : PiLocalization₂ D) : ℂ :=
  GlobalTheory.LFun.dSfun D.host.E S s.V.rank s'.V.rank ((D.R.t : ℂ) / 2)

def FlatLe (D : D7) : Prop := ForStageQ D fun c w j s => ∀ hr, s.CC c ≤ (flat c w j s hr).CC c

def SoftQ (D : D7) : Prop := ForStageQ D fun c _ _ s => FiniteDimensional ℂ (s.CC c) ∧ (∃ ipD ip, IsMet c s ipD ip) ∧
  (∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0) ∧
  ∀ (x : s.CC c) w B, PiLocalization₂.val x w ≠ 0 → ParFun c s (PiLocalization₂.val x w) B → IsPar x B

def LevelLawQ (D : D7) : Prop := ForStepQ D fun _ _ _ s s' p => ∀ φ,
  VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L) (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) (p.pt φ)

def UpSpanQ (D : D7) : Prop := ForStepQ D fun c _ _ s s' p => ∀ (u : s.CC c) φ, ∀ v ∈ s.KF,
  p.up φ (PiLocalization₂.val u v) ∈ Submodule.span ℂ {F | ∃ (y : s'.CC c), ∃ w ∈ s'.KF, F = PiLocalization₂.val y w}

def UpAdjQ (D : D7) : Prop := ForStepQ D fun c _ _ s s' p => ∀ (u : s.CC c) (y : s'.CC c) φ, ∀ v ∈ s.KF, ∀ w ∈ s'.KF,
  s'.pet (PiLocalization₂.val y w) (p.up φ (PiLocalization₂.val u v)) = s.pet (PiLocalization₂.val (p.io y) (p.It φ w)) (PiLocalization₂.val u v)

def UpParQ (D : D7) : Prop := ForStepQ D fun c _ k s s' p => ∀ (u : s.CC c) B φ, IsPar u B → ∀ v ∈ s.KF,
  p.up φ (PiLocalization₂.val u v) ≠ 0 → ParFun c s' (p.up φ (PiLocalization₂.val u v)) (stepPar (c.chS (k + 1)) (c.chT (k + 1)) D.R.t B)

def UpQ (D : D7) : Prop := ForStepQ D fun c w k s s' p => ∀ (u : s.CC c) φ, IsQ w k u → ∀ v ∈ s.KF,
  IsQFun c w (k + 1) s' (p.up φ (PiLocalization₂.val u v))

def QOfVal (D : D7) : Prop := ForStageQ D fun c w j s =>
  (∀ (x : s.CC c) v, PiLocalization₂.val x v ≠ 0 → IsQFun c w j s (PiLocalization₂.val x v) → IsQ w j x) ∧ (j = 0 → ∀ x : s.CC c, IsQ w j x)

def UpVal (D : D7) : Prop := ForStepQ D fun c _ _ s s' p => ∀ ipD ip ipD' ip', IsMet c s ipD ip → IsMet c s' ipD' ip' → ∀ φ, ∀ v ∈ s.KF,
  ((∃ u : s.CC c, p.up φ (PiLocalization₂.val u v) ≠ 0) → ∃ w₀, w₀ ≠ 0 ∧ IsAdjVec p ipD ipD' φ v w₀) ∧
  ∀ w₀, IsAdjVec p ipD ipD' φ v w₀ → ∀ (u : s.CC c) (x : s'.CC c), (∀ y, ip' y x = ip (p.io y) u) → p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀

def QPeel (D : D7) : Prop := ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ a, IsMajOf c s a →
  ∀ (u₁ u₂ : s.CC c) φ, IsQ w k u₁ → ∀ v₁ ∈ s.KF, ∀ v₂ ∈ s.KF, ∀ z : ℝ, (D.R.t : ℝ) / 2 - 1 < z →
    IntegrableOn (flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z) (levSet s) s.ν →
    IntegrableOn (flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z) (intOff c s) s.ν ∧
    (z = (D.R.t : ℝ) / 2 → ∫ g in intOff c s, flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z g ∂s.ν =
      locQ c w k * ∫ g in levSet s, flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z g ∂s.ν)

def LevInt (D : D7) : Prop := ForStepQ D fun c _ _ s s' p => ∀ ipD ip, IsMet c s ipD ip → ∀ m X, IsCovolOne (ratL s'.V s.V) m X →
  ∀ mR, IsLevMeas s mR → ∀ φ v, RealConv p m X φ v mR → ∀ a, IsMajOf c s a → ∃ s₁ : ℝ, s₁ < (D.R.t : ℝ) / 2 ∧ ∀ u₁ u₂ : s.CC c,
    (∀ z : ℝ, s₁ ≤ z → IntegrableOn (flatInt p m X a φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) z)
      (levSet s) s.ν) ∧
    ∫ g in levSet s, flatInt p m X a φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v))
      (((D.R.t : ℝ) / 2 : ℝ) : ℂ) g ∂s.ν = (∫ g, zReal p m X φ v g ∂mR) * conj (ip u₁ u₂)

def StepExact (D : D7) : Prop := ForStepQ D fun c w k s s' p => ∀ ipD ip, IsMet c s ipD ip → ∀ m X, IsCovolOne (ratL s'.V s.V) m X →
  ∀ mR, IsLevMeas s mR → ∀ φ v, RealConv p m X φ v mR → ∀ (u₁ u₂ : s.CC c) B, IsPar u₁ B → IsQ w k u₁ →
    ∀ l, GlobalTheory.Cont.HolValueAt (fun z => GlobalTheory.LFun.LSD D c.S B (c.chT (k + 1)) (z + 1 / 2)) ((D.R.t : ℂ) / 2) l →
      s'.pet (p.up φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v))) (p.up φ (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v))) =
        conj ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℂ) * (l / dS (c.S : Set _) s s') * locQ c w k * ∫ g, zReal p m X φ v g ∂mR) * ip u₁ u₂

def LFull (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ B : GlobalTheory.LFun.Fam D.host.E,
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) → ∀ k < D.R.m,
    ∃ H, H ≠ 0 ∧ IsHval c (c.S : Set _) k H ∧
      GlobalTheory.LFun.Converges (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
        (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹) ((1 + (D.R.t : ℂ)) / 2) ∧
      GlobalTheory.LFun.LSD D c.S B (c.μ (k + 1)) ((1 + (D.R.t : ℂ)) / 2) ≠ 0 ∧
      GlobalTheory.Cont.HolValueAt (fun z => GlobalTheory.LFun.LSD D c.S (chainPar c B k) (c.chT (k + 1)) (z + 1 / 2)) ((D.R.t : ℂ) / 2)
        (GlobalTheory.LFun.LSD D c.S B (c.μ (k + 1)) ((1 + (D.R.t : ℂ)) / 2) * H)

def idxQ (PP : Pl D.host.E) (j : ℕ) : ℝ :=
  (Ideal.absNorm PP.asIdeal : ℝ) ^ (D.R.r * (j * D.R.t)) * zinv PP 0 (D.R.r + j * D.R.t) / (zinv PP 0 D.R.r * zinv PP 0 (j * D.R.t))

def volOne (PP : Pl D.host.E) (j : ℕ) : ℝ := zinv PP 0 D.R.r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (D.R.r * (j * D.R.t)))⁻¹

open Classical in

def Twist.S₀ (w : Twist D) : Set (HeightOneSpectrum (𝓞 D.host.F)) := (w.Pg.image fun PP => PP.under (𝓞 D.host.F) : Finset _)

def kapOf (w : Twist D) (k : ℕ) (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V)) (mR : Measure (GinfC s.V))
    (φ : PolF D s'.V.rank s.V.rank) (v : s.M.Vec) (H₀ : ℂ) : ℂ :=
  ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν / ∏ PP ∈ w.Q, idxQ PP (k + 1) : ℝ) : ℂ) * (H₀ / dS w.S₀ s s') *
    ((∫ g, zReal p m X φ v g ∂mR) / ((∏ PP ∈ w.Q, volOne PP (k + 1) : ℝ) : ℂ))

def Restore (D : D7) : Prop := ForStepQ D fun c w k s s' _ =>
  (∀ H H₀, IsHval c (c.S : Set _) k H → IsHval c w.S₀ k H₀ → H₀ = H * ∏ PP ∈ w.Q, blockL c k PP) ∧
  (∃ H₀, H₀ ≠ 0 ∧ IsHval c w.S₀ k H₀) ∧ dS w.S₀ s s' ≠ 0 ∧
  dS (c.S : Set _) s s' = dS w.S₀ s s' * ((∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t) : ℝ) : ℂ)

def RealZetaQ (D : D7) : Prop := ForStepQ D fun _ _ _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∃ φ v,
  ∀ mR : Measure (GinfC s.V), mR.IsHaarMeasure → (∫ g, zReal p m X φ v g ∂mR) ≠ 0 ∧ RealConv p m X φ v mR

def LPos (D : D7) : Prop := ForStageQ D fun c _ j s => j = 0 → ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) ∧
  ∀ k < D.R.m, ∃ l : ℝ, 0 < l ∧ GlobalTheory.LFun.LSD D c.S B (c.μ (k + 1)) ((1 + (D.R.t : ℂ)) / 2) = l

def StepLam (D : D7) : Prop := ForStepQ D fun c w k s s' p => ∀ ipD ip ipD' ip', IsMet c s ipD ip → IsMet c s' ipD' ip' →
  ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ mR, IsLevMeas s mR → ∀ φ v, RealConv p m X φ v mR → ∀ H₀, IsHval c w.S₀ k H₀ →
    kapOf w k p m X mR φ v H₀ ≠ 0 → ∀ B,
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) →
    ∀ u₁ : s.CC c, IsPar u₁ (chainPar c B k) → IsQ w k u₁ → ∃ w₀, w₀ ≠ 0 ∧ IsAdjVec p ipD ipD' φ (PiTensorProduct.tprod ℂ v) w₀ ∧
      ∀ x₁ : s'.CC c, (∀ y, ip' y x₁ = ip (p.io y) u₁) → IsPar x₁ (chainPar c B (k + 1)) ∧ IsQ w (k + 1) x₁ ∧
        ∀ (u₂ : s.CC c) (x₂ : s'.CC c), (∀ y, ip' y x₂ = ip (p.io y) u₂) → ip' x₁ x₂ * ipD' w₀ w₀ =
          conj (kapOf w k p m X mR φ v H₀ * GlobalTheory.LFun.LSD D c.S B (c.μ (k + 1)) ((1 + (D.R.t : ℂ)) / 2)) * ip u₁ u₂

example (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) : qPar c PP x 0 = 0 := rfl

example (c : Com D) (PP : Pl D.host.E) : blockL c 0 PP = 1 := by simp [blockL]

end GlobalTheory.ChainTw

end
