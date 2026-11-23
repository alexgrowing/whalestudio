import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.Chain (IsVacVec ptOf signed)
open GlobalTheory.ChainOnto (stepPar)

namespace GlobalTheory.EvenOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def UpPair (t : ℕ) (S S' : SPar) (aS aT : ℚ) : Prop :=
  ∃ al be ga de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧ (∀ e ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |e|) ∧
    S = dualPar (signed (al ++ be) (ga ++ de) aT) ∧ S' = dualPar (signed (al ++ block t ++ de) (ga ++ be) aS)

structure Com (D : D7) where
  θ : InfFam D
  ψ : AddChar (AF D.host.F) ℂ
  S : Finset (HeightOneSpectrum (𝓞 D.host.F))
  n : ℕ
  t : ℕ
  m : ℕ
  χ : ℕ → ((AE D)ˣ →* Circle)
  a : ℕ → D.what₂.Tau → ℚ

structure Com.Is (c : Com D) : Prop where
  inf : IsInfFam c.θ
  std : IsStdChar D c.ψ (-1)
  hecke : ∀ k < c.m, IsHeckeChar D (c.χ k) ∧ Formalism.L2.Theta.ResEta D (c.χ k) 0
  exp : ∀ k < c.m, ∀ τ, HasInfExp D (c.χ k) τ (c.a k τ)
  unr : ∀ k < c.m, GlobalTheory.LFun.UnrOff (c.χ k) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  ne : ∀ i k, i < k → k < c.m → ∀ τ, c.a i τ ≠ c.a k τ
  one_le : 1 ≤ c.n
  step : c.n + 2 ≤ c.t

structure PiLocalization₂ (D : D7) where
  V : HSp D
  par : D.what₂.Tau → SPar
  M : DSModel V par
  J : Subgroup (GA D V)
  ν : Measure (GA D V)
  fd : Set (GA D V)

abbrev PiLocalization₂.Λ (s : PiLocalization₂ D) : Submodule (𝓞 D.host.E) (Fin s.V.rank → D.host.E) := GlobalTheory.AdelicU.frameLat s.V

def intOff (c : Com D) (s : PiLocalization₂ D) : Set (GA D s.V) :=
  {g | ∀ v ∉ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v}

def PiLocalization₂.big (s : PiLocalization₂ D) : Set (GA D s.V) := {g | ∃ b : GinfC s.V, ∃ κ ∈ s.J, g = (b : GA D s.V) * κ}

structure PiLocalization₂.Is (c : Com D) (j : ℕ) (s : PiLocalization₂ D) : Prop where
  rank : s.V.rank = c.n + j * c.t
  sigOK : s.V.SigOK
  witt : GlobalTheory.Cusp.wittIndex s.V < c.t
  selfDual : IsSelfDualC s.V s.Λ
  fin : s.J ≤ GfC s.V
  isOpen : ∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧ ∀ k ∈ U, k ∈ GfC s.V → k ∈ s.J
  stab : ∀ k ∈ s.J, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v
  off : ∀ k ∈ GfC s.V, k ∈ intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) → k ∈ s.J
  sph : SphOff (s.J : Set (GA D s.V)) 1 c.S
  split : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ s.J,
    ∃ k₁ ∈ s.J, ∃ k₂ ∈ s.J, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂
  haar : s.ν.IsHaarMeasure
  fund : IsFundamentalDomain (GQ s.V) s.fd s.ν

abbrev PiLocalization₂.CC (c : Com D) (s : PiLocalization₂ D) : Submodule ℂ (SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := MultT c.θ s.M (s.J : Set (GA D s.V)) 1

abbrev PiLocalization₂.val {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : SmT s.M) : GA D s.V → ℂ :=
  (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v

def PiLocalization₂.KF (s : PiLocalization₂ D) : Submodule ℂ (SmT s.M) :=
  Submodule.span ℂ {w | ∃ v : s.M.Vec, (∀ τ, (v τ : s.M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin s.M τ) ∧ w = PiTensorProduct.tprod ℂ v}

abbrev PiLocalization₂.pet (s : PiLocalization₂ D) (f₁ f₂ : GA D s.V → ℂ) : ℂ := Lift.pet s.ν s.fd f₁ f₂

variable {c : Com D} {s s' : PiLocalization₂ D}

def coefW (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ)) (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V))
    (Φ : WO s.V s'.V → ℂ) (g : GA D s.V) : ℂ := ∫ w in X, ω (g, 1) Φ w * conj (Φ w) ∂m

structure PreStep (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ))
    (f : WO s.V s'.V → ℂ) : Prop where
  weil : IsWeilDatumO c.ψ s.V s'.V (c.χ k) (c.χ k) ω
  par : ∀ τ, UpPair c.t (s.par τ) (s'.par τ) (c.a k τ) (c.a k τ)
  vac : IsVacVec c.ψ c.θ s.M s'.M f
  sph : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S f
  law : ∀ φ, ∀ κ ∈ s.J, ∀ κ' ∈ s'.J, ω (κ, κ') (ptOf c.ψ c.θ s.M s'.M f φ) = ptOf c.ψ c.θ s.M s'.M f φ
  supp : ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ φ, ∀ g ∈ intOff c s, g ∉ s.big →
    coefW ω m X (ptOf c.ψ c.θ s.M s'.M f φ) g = 0

structure Step (c : Com D) (s s' : PiLocalization₂ D) where
  ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ)
  f : WO s.V s'.V → ℂ
  It : PolF D s'.V.rank s.V.rank →ₗ[ℂ] SmT s'.M →ₗ[ℂ] SmT s.M
  io : s'.CC c →ₗ[ℂ] s.CC c

def Step.pt (p : Step c s s') : PolF D s'.V.rank s.V.rank → (WO s.V s'.V → ℂ) := ptOf c.ψ c.θ s.M s'.M p.f

structure Step.Is (k : ℕ) (p : Step c s s') : Prop where
  pre : PreStep c k s s' p.ω p.f
  it : IsItW c.θ s.M s'.M p.ω p.pt p.It
  io : Lift.IsIo s'.ν s'.fd (thetaKO p.ω) p.pt p.It (s'.CC c) (s.CC c) p.io

inductive Reach (c : Com D) (s₀ : PiLocalization₂ D) : ℕ → ∀ s : PiLocalization₂ D, (s.CC c →ₗ[ℂ] s₀.CC c) → Prop
  | zero : Reach c s₀ 0 s₀ LinearMap.id
  | step {k : ℕ} {s : PiLocalization₂ D} {Θ : s.CC c →ₗ[ℂ] s₀.CC c} (h : Reach c s₀ k s Θ) {s' : PiLocalization₂ D} (hs' : s'.Is c (k + 1))
      (p : Step c s s') (hp : p.Is k) : Reach c s₀ (k + 1) s' (Θ ∘ₗ p.io)

def OntoAll (D : D7) : Prop :=
  ∀ c : Com D, c.Is → ∀ s₀ : PiLocalization₂ D, s₀.Is c 0 →
    ∀ k ≤ c.m, ∀ (s : PiLocalization₂ D) (Θ : s.CC c →ₗ[ℂ] s₀.CC c), Reach c s₀ k s Θ → Function.Surjective Θ

structure IsMet (c : Com D) (s : PiLocalization₂ D) (ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ) (ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ) : Prop where
  pure : ∀ v v' : s.M.Vec, ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') = ∏ τ, ⟪(v' τ : s.M.H τ), (v τ : s.M.H τ)⟫_ℂ
  hermD : ∀ w w', ipD w w' = conj (ipD w' w)
  posD : ∀ w, w ≠ 0 → 0 < (ipD w w).re
  herm : ∀ x y, ip x y = conj (ip y x)
  pos : ∀ x, x ≠ 0 → 0 < (ip x x).re
  integ : ∀ (x y : s.CC c) w w', IntegrableOn (fun g => PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g)) s.fd s.ν
  schur : Lift.IsSchur s.ν s.fd ipD (s.CC c) ip

def ParFun (c : Com D) (s : PiLocalization₂ D) (f : GA D s.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E) : Prop :=
  GlobalTheory.LFun.IsParamFun D.sp.cm.sig s.V.gram s.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) (fun g => conj (f g)) B

def IsPar (u : s.CC c) (B : GlobalTheory.LFun.Fam D.host.E) : Prop := u ≠ 0 ∧ ∀ v, PiLocalization₂.val u v ≠ 0 → ParFun c s (PiLocalization₂.val u v) B

def chainPar (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) : GlobalTheory.LFun.Fam D.host.E :=
  Nat.rec B (fun i B' => stepPar (c.χ i) (c.χ i) c.t B') k

def LNe (c : Com D) (χ : (AE D)ˣ →* Circle) (B : GlobalTheory.LFun.Fam D.host.E) : Prop :=
  ∃ l : ℂ, l ≠ 0 ∧ GlobalTheory.Cont.HolValueAt (fun z => GlobalTheory.LFun.LSD D c.S B χ (z + 1 / 2)) ((c.t : ℂ) / 2) l

def Step.up (p : Step c s s') (φ : PolF D s'.V.rank s.V.rank) (F : GA D s.V → ℂ) : GA D s'.V → ℂ :=
  fun h => ∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * F g ∂s.ν

def hgtS (c : Com D) (s : PiLocalization₂ D) (a : GL (Fin s.V.rank) (AE D)) (g : GA D s.V) : ℝ :=
  (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w g)) *
    ∏ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g)

def Step.zint (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (F : GA D s.V → ℂ) (g : GA D s.V) : ℂ := coefW p.ω m X (p.pt φ) g * conj (s.pet (rTr s.V g F) F)

def ForStage (D : D7) (Φ : ∀ (_ : Com D) (_ : ℕ) (_ : PiLocalization₂ D), Prop) : Prop :=
  ∀ c : Com D, c.Is → ∀ j ≤ c.m, ∀ s : PiLocalization₂ D, s.Is c j → Φ c j s

def FinDim (D : D7) : Prop := ForStage D fun c _ s => FiniteDimensional ℂ (s.CC c)

def MetEx (D : D7) : Prop := ForStage D fun c _ s => ∃ ipD ip, IsMet c s ipD ip

def EigSpan (D : D7) : Prop := ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ B, IsPar u B} = ⊤

def ParBound (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B s.V.rank (((s.V.rank : ℝ) - 1) / 2)

def ParOfVal (D : D7) : Prop := ForStage D fun c _ s => ∀ (x : s.CC c) w B, PiLocalization₂.val x w ≠ 0 → ParFun c s (PiLocalization₂.val x w) B → IsPar x B

def ParIndep (D : D7) : Prop := ForStage D fun c _ s => ∀ (ι : Type) (x : ι → s.CC c) (B : ι → GlobalTheory.LFun.Fam D.host.E),
  (∀ i, IsPar (x i) (B i)) →
  (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) → LinearIndependent ℂ x

def ForStep (D : D7) (Φ : ∀ (c : Com D) (_ : ℕ) (s s' : PiLocalization₂ D) (_ : Step c s s'), Prop) : Prop :=
  ∀ c : Com D, c.Is → ∀ k < c.m, ∀ s s' : PiLocalization₂ D, s.Is c k → s'.Is c (k + 1) → ∀ p : Step c s s', p.Is k → Φ c k s s' p

def StepEx (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ k < c.m, ∀ s s' : PiLocalization₂ D, s.Is c k → s'.Is c (k + 1) →
  ∀ ω f, PreStep c k s s' ω f → ∃ p : Step c s s', p.ω = ω ∧ p.f = f ∧ p.Is k

def UpSpan (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ (u : s.CC c) φ, ∀ v ∈ s.KF,
  p.up φ (PiLocalization₂.val u v) ∈ Submodule.span ℂ {F | ∃ (y : s'.CC c), ∃ w ∈ s'.KF, F = PiLocalization₂.val y w}

def UpAdj (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ (u : s.CC c) (y : s'.CC c) φ, ∀ v ∈ s.KF, ∀ w ∈ s'.KF,
  s'.pet (PiLocalization₂.val y w) (p.up φ (PiLocalization₂.val u v)) = s.pet (PiLocalization₂.val (p.io y) (p.It φ w)) (PiLocalization₂.val u v)

def UpPar (D : D7) : Prop := ForStep D fun c k s s' p => ∀ (u : s.CC c) B φ, IsPar u B → ∀ v ∈ s.KF,
  p.up φ (PiLocalization₂.val u v) ≠ 0 → ParFun c s' (p.up φ (PiLocalization₂.val u v)) (stepPar (c.χ k) (c.χ k) c.t B)

def ZetaNe (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∃ φ, ∃ v ∈ s.KF,
  ∀ u : s.CC c, u ≠ 0 → (∫ g in intOff c s, p.zint m X φ (PiLocalization₂.val u v) g ∂s.ν) ≠ 0 ∧
    ∀ a : GL (Fin s.V.rank) (AE D), GlobalTheory.Doubling.IsMaj s.V a →
      (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) →
      ∃ s₁ : ℝ, s₁ < (c.t : ℝ) / 2 ∧
        IntegrableOn (fun g => p.zint m X φ (PiLocalization₂.val u v) g * (hgtS c s a g : ℂ) ^ ((s₁ : ℂ) - (c.t : ℂ) / 2)) (intOff c s) s.ν

def RealZeta (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∃ φ, ∃ v : s.M.Vec,
  (∀ τ, (v τ : s.M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin s.M τ) ∧ ∀ mR : Measure (GinfC s.V), mR.IsHaarMeasure →
    let z : GinfC s.V → ℂ := fun g => coefW p.ω m X (p.pt φ) g *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)
    (∫ g, z g ∂mR) ≠ 0 ∧
    ∀ a : GL (Fin s.V.rank) (AE D), GlobalTheory.Doubling.IsMaj s.V a →
      (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) →
      ∃ s₁ : ℝ, s₁ < (c.t : ℝ) / 2 ∧ Integrable (fun g : GinfC s.V => z g *
        ((∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (g : GA D s.V)) : ℝ) : ℂ) ^
          ((s₁ : ℂ) - (c.t : ℂ) / 2)) mR

def UpNe (D : D7) : Prop := ForStep D fun c k s _ p => ∀ (u : s.CC c) B, IsPar u B → LNe c (c.χ k) B →
  ∃ φ, ∃ v ∈ s.KF, p.up φ (PiLocalization₂.val u v) ≠ 0

def StepUp (D : D7) : Prop := ForStep D fun c k s s' p => ∀ ipD ip ipD' ip', IsMet c s ipD ip → IsMet c s' ipD' ip' →
  ∀ (u : s.CC c) B, IsPar u B → LNe c (c.χ k) B →
    ∃ x : s'.CC c, (∀ y, ip' y x = ip (p.io y) u) ∧ IsPar x (stepPar (c.χ k) (c.χ k) c.t B)

def ChainL (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ B : GlobalTheory.LFun.Fam D.host.E,
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B c.n (((c.n : ℝ) - 1) / 2) →
  ∀ k < c.m, LNe c (c.χ k) (chainPar c B k)

def ChainUp (D : D7) : Prop :=
  ∀ c : Com D, c.Is → ∀ s₀ : PiLocalization₂ D, s₀.Is c 0 →
    ∀ k ≤ c.m, ∀ (s : PiLocalization₂ D) (Θ : s.CC c →ₗ[ℂ] s₀.CC c), Reach c s₀ k s Θ → s.Is c k ∧
      ∀ ipD₀ ip₀ ipD ip, IsMet c s₀ ipD₀ ip₀ → IsMet c s ipD ip → ∀ (u : s₀.CC c) B, IsPar u B →
        ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k)

example (c : Com D) (s₀ : PiLocalization₂ D) : Reach c s₀ 0 s₀ LinearMap.id ∧ Function.Surjective (LinearMap.id : s₀.CC c →ₗ[ℂ] s₀.CC c) :=
  ⟨Reach.zero, Function.surjective_id⟩

theorem chainPar_succ (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B (k + 1) = stepPar (c.χ k) (c.χ k) c.t (chainPar c B k) := rfl

end GlobalTheory.EvenOnto

end
