import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.DstarEq
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ProjRows
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Real

variable {n r : ℕ}

def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)

def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})

def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r

def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r

def nxt {V : Type} (e : Fin r → V) (z : V) (a : Fin r) : V :=
  if h : a.1 + 1 < r then e ⟨a.1 + 1, h⟩ else z

def rootCoord (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (a : Fin r) : ℂ :=
  hJ ε (f a) (g *ᵥ nxt e z a)

def psiR (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    ((∑ a, (rootCoord ε e f z g a + star (rootCoord ε e f z g a))) / (gg : ℂ)))

end Real

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

variable {r : ℕ}

def Sinf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InS (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}

def Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}

def psiInf (g : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) (s : I.Ginf) : ℂ :=
  ∏ v, psiR (I.ε v) g (fun a => rv I v (e a)) (fun a => rv I v (f a)) (rv I v z) (uMat (s v))

def psiEinf (x : I.E) : ℂ :=
  ∏ v, Complex.exp (2 * Real.pi * Complex.I * (I.φ v x + star (I.φ v x)))

end Inst

section Fin

variable (I : Formalism.MainNotions.S.AutInst)

abbrev VA : Type := Fin I.n → I.E ⊗[I.F] Af I.F

def incl (x : Fin I.n → I.E) : VA I := fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)

def hA (x y : VA I) : I.E ⊗[I.F] Af I.F :=
  Formalism.UG.hform (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) x y

abbrev sigA : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

def mL (m : ℕ) : Submodule (IntAf I.F I.E) (VA I) :=
  Submodule.span (IntAf I.F I.E) {y | ∃ x ∈ I.Lf, y = (m : I.E ⊗[I.F] Af I.F) • x}

def InMod (m : ℕ) (S : Set (VA I)) (x : VA I) : Prop :=
  x ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I m

def ZMod' (m : ℕ) (c : I.E ⊗[I.F] Af I.F) : Prop :=
  ∃ t ∈ IntAf I.F I.E, c = (m : I.E ⊗[I.F] Af I.F) * t

def InAt (g m : ℕ) (x : VA I) : Prop :=
  ∃ c : ℕ, Nat.Coprime c g ∧ (c : I.E ⊗[I.F] Af I.F) • x ∈ mL I m

def OneOff (g : ℕ) (x : I.Gf) : Prop :=
  ∀ m : ℕ, Nat.Coprime m g → ∀ y ∈ I.Lf, InAt I m m ((I.fmat x - 1) *ᵥ y)

def divN (g : ℕ) (c : I.E ⊗[I.F] Af I.F) : I.E ⊗[I.F] Af I.F :=
  algebraMap I.F (I.E ⊗[I.F] Af I.F) ((g : I.F)⁻¹) * c

variable {r k : ℕ}

def Nfin (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Gf :=
  {x | (∀ a : Fin r, (I.fmat x - 1) *ᵥ incl I (e a) ∈
        Submodule.span (I.E ⊗[I.F] Af I.F) ((fun b => incl I (e b)) '' {b | b.1 < a.1})) ∧
    (I.fmat x - 1) *ᵥ incl I z ∈ Submodule.span (I.E ⊗[I.F] Af I.F) (Set.range fun b => incl I (e b)) ∧
    ∀ y : VA I, (∀ a, hA I (incl I (e a)) y = 0) →
      (I.fmat x - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Af I.F) (Set.range fun b => incl I (e b))}

def psiFin (psiEf : I.E ⊗[I.F] Af I.F → ℂ) (g : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (x : I.Gf) : ℂ :=
  psiEf (divN I g (∑ a, hA I (incl I (f a)) (I.fmat x *ᵥ incl I (nxt e z a))))

def K2cong (g : ℕ) (e0 : Fin r → VA I) (z0 : VA I) (β : Fin k → VA I) (x : I.Gf) : Prop :=
  (∀ a : Fin r, InMod I g (e0 '' {b | b.1 < a.1}) ((I.fmat x - 1) *ᵥ e0 a)) ∧
    InMod I g (Set.range e0) ((I.fmat x - 1) *ᵥ z0) ∧
    ∀ i : Fin k, InMod I g (Set.range e0 ∪ β '' {j | j.1 < i.1}) ((I.fmat x - 1) *ᵥ β i)

def K2set (g : ℕ) (e0 : Fin r → VA I) (z0 : VA I) (β : Fin k → VA I) : Set I.Gf :=
  {x | x ∈ I.Kset ∧ K2cong I g e0 z0 β x}

def chi2f (psiEf : I.E ⊗[I.F] Af I.F → ℂ) (g : ℕ) (e0 f0 : Fin r → VA I) (z0 : VA I)
    (β βd : Fin k → VA I) (x : I.Gf) : ℂ :=
  psiEf (divN I g ((∑ a, hA I (f0 a) (I.fmat x *ᵥ nxt e0 z0 a)) +
    ∑ i : Fin k, if h : i.1 + 1 < k then hA I (βd i) (I.fmat x *ᵥ β ⟨i.1 + 1, h⟩) else 0))

end Fin

section Wu

variable (I : Formalism.MainNotions.S.AutInst) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def IsRepS (S N : Set I.Ginf) (rho : I.Ginf → (V →L[ℂ] V)) : Prop :=
  rho 1 = 1 ∧ (∀ s ∈ S, ∀ t ∈ S, rho (s * t) = rho s * rho t) ∧
    (∀ s ∈ S, ∀ x y : V, ⟪rho s x, rho s y⟫_ℂ = ⟪x, y⟫_ℂ) ∧ (∀ s ∈ N, rho s = 1) ∧
    ∀ x : V, ContinuousOn (fun s => rho s x) S

def IsSFund (S : Set I.Ginf) (Fd : Set I.Ginf) : Prop :=
  MeasurableSet Fd ∧ (∀ x, ∃ s ∈ S, s * x ∈ Fd) ∧ ∀ x ∈ Fd, ∀ s ∈ S, s * x ∈ Fd → s = 1

def IsHaarOnSet (S : Set I.Ginf) (μ : Measure I.Ginf) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ

def IsQuotMeasS (μS ν : Measure I.Ginf) : Prop :=
  ∀ f : I.Ginf → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x ∂(Formalism.L2.SG.ProjRows.muInf I) = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν

def IsWu (ph : I.Ginf → ℂ) (S : Set I.Ginf) (psi : I.Ginf → ℂ) (rho : I.Ginf → (V →L[ℂ] V))
    (ν : Measure I.Ginf) (W : I.Ginf → V) : Prop :=
  (∀ s ∈ S, ∀ x, W (s * x) = psi s • rho s (W x)) ∧
    (∀ x, Integrable (fun y => ph y • W (x * y)) (Formalism.L2.SG.ProjRows.muInf I) ∧
      ∫ y, ph y • W (x * y) ∂(Formalism.L2.SG.ProjRows.muInf I) = W x) ∧
    Continuous W ∧ ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤ ∧ ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν = 1

def Hset (S : Set (Fin I.n → I.E)) : Set I.Ginf :=
  {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}

def matW {k : ℕ} (wf : Fin k → Fin I.n → ℂ) (v : InfinitePlace I.F) (s : I.Ginf) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun a b => hJ (I.ε v) (wf a) (uMat (s v) *ᵥ wf b)

end Wu

def latSpanS {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] {r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (v : Fin r → V) : Submodule (𝓞 E) V :=
  Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ aa a ∧ y = x • v a}

def aaD (D : D7) (a : Fin D.R.rS) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

def crdOf {D : D7} (I : Formalism.MainNotions.S.AutInst) (ιE : I.E ≃+* D.host.E)
    (bas : Module.Basis (Fin I.n) D.host.E (VS D).V) (y : (VS D).V) : Fin I.n → I.E :=
  fun i => ιE.symm (bas.repr y i)

structure HidaSetting (D : D7) where

  B : RowsAut

  ιE : B.I.E ≃+* D.host.E
  ιE_conj : ∀ x : B.I.E, ιE (star x) = D.host.conj (ιE x)
  ιE_F : ∀ y : D.host.E, y ∈ D.host.F ↔ ∃ a : B.I.F, ιE (algebraMap B.I.F B.I.E a) = y

  bas : Module.Basis (Fin B.I.n) D.host.E (VS D).V

  J_eq : ∀ i j, ιE (B.I.J i j) = (VS D).hT (bas i) (bas j)

  L_eq : ∀ x : Fin B.I.n → B.I.E, x ∈ B.I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0

  pl : InfinitePlace B.I.F ≃ D.what₂.Tau
  φ_eq : ∀ v (x : B.I.E), B.I.φ v x = embS D (pl v) (ιE x)
  n_eq : B.I.n = D.R.r
  eps_eq : ∀ v (i : Fin B.I.n), B.I.ε v i = epsS D.R (Fin.cast n_eq i)
  lam_eq : ∀ v (i : Fin B.I.n), B.lam v i = lamS D.R (D.hc (pl v)) (Fin.cast n_eq i)
  ds : ∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v)
  low : ∀ v, IsLowUnit (B.I.ε v) (B.lam v) (B.σ v) (B.w v)
  g_eq : B.g = D.host.g 0 * D.host.g 1
  g0_eq : B.g₀ = D.host.g 0

  Rph : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund
  Rph_spec : Formalism.L2.SG.ProjRows.IsOpInt (Formalism.L2.SG.ProjRows.muInf B.I) (fun y => B.R (y, 1))
    (Formalism.L2.SG.ProjRows.phInf B.I B.σ B.w fun v => fdegOf (Formalism.REAL.muG (B.I.ε v)) (B.σ v) (B.w v)) Rph

  eX : Fin D.R.rS → (VS D).V
  fY : Fin D.R.rS → (VS D).V
  ee : ∀ a b, (VS D).hT (eX a) (eX b) = 0
  ff : ∀ a b, (VS D).hT (fY a) (fY b) = 0
  ef : ∀ a b, (VS D).hT (eX a) (fY b) = if a = b then 1 else 0

  Lb : Submodule (𝓞 D.host.E) (VS D).V
  Lb_perp : ∀ x ∈ Lb, ∀ a, (VS D).hT (eX a) x = 0 ∧ (VS D).hT (fY a) x = 0
  Lam_split : (VS D).L0 = latSpanS (fun a => aaD D a) eX ⊔ Lb ⊔ latSpanS (fun a => (aaD D a)⁻¹) fY

  zu : D.what₂.Word → (VS D).V
  zu_norm : ∀ u, (VS D).hT (zu u) (zu u) = -(((D.mem u).A.T : ℕ) : D.host.E)
  zu_orth : ∀ u a, (VS D).hT (eX a) (zu u) = 0 ∧ (VS D).hT (fY a) (zu u) = 0
  zu_Lb : ∀ u, zu u ∈ Lb

  Fu : ∀ u, FlagS D u
  Fu_e : ∀ u, (Fu u).e = eX
  flagZVector : ∀ u, (Fu u).z = zu u
  Fu_fixed : ∀ u, Formalism.MainNotions.S.Lat.FixedHyp D (VS D).L0
    (⟨Fu u, zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (VS D) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))

  psiEf : B.I.E ⊗[B.I.F] Af B.I.F → ℂ
  psiEf_add : ∀ x y, psiEf (x + y) = psiEf x * psiEf y
  psiEf_int : ∀ x ∈ IntAf B.I.F B.I.E, psiEf x = 1
  psiEf_rat : ∀ x : B.I.E, psiEf (Formalism.UG.inclE (F := B.I.F) (Af B.I.F) x) * psiEinf B.I x = 1

  e0 : Fin D.R.rS → VA B.I
  f0 : Fin D.R.rS → VA B.I
  z0 : VA B.I
  bw : Fin D.R.k → VA B.I
  bwd : Fin D.R.k → VA B.I
  ew : B.I.E ⊗[B.I.F] Af B.I.F
  vectorsInLattice : (∀ a, e0 a ∈ B.I.Lf ∧ f0 a ∈ B.I.Lf) ∧ z0 ∈ B.I.Lf ∧ ∀ i, bw i ∈ B.I.Lf ∧ bwd i ∈ B.I.Lf

  basisApprox : ∀ a, InAt B.I B.g B.g (e0 a - incl B.I (crdOf B.I ιE bas (eX a))) ∧
    InAt B.I B.g B.g (f0 a - incl B.I (crdOf B.I ιE bas (fY a)))

  gramIntegral : ∀ a b, ZMod' B.I B.g (hA B.I (e0 a) (e0 b)) ∧ ZMod' B.I B.g (hA B.I (f0 a) (f0 b)) ∧
    ZMod' B.I B.g (hA B.I (e0 a) (f0 b) - if a = b then 1 else 0)
  formsAtZero : ZMod' B.I B.g (hA B.I z0 z0 + 1) ∧
    ∀ a, ZMod' B.I B.g (hA B.I (e0 a) z0) ∧ ZMod' B.I B.g (hA B.I (f0 a) z0)
  weightVectorsIntegral : ∀ i, ZMod' B.I B.g (hA B.I z0 (bw i)) ∧ ZMod' B.I B.g (hA B.I z0 (bwd i)) ∧
    ∀ a, ZMod' B.I B.g (hA B.I (e0 a) (bw i)) ∧ ZMod' B.I B.g (hA B.I (f0 a) (bw i)) ∧
      ZMod' B.I B.g (hA B.I (e0 a) (bwd i)) ∧ ZMod' B.I B.g (hA B.I (f0 a) (bwd i))

  ew_idem : ew * ew = ew
  ew_orth : ew * sigA B.I ew = 0
  ew_int : ew ∈ IntAf B.I.F B.I.E
  ew_full : ∀ y ∈ B.I.Lf, (1 - ew - sigA B.I ew) • y ∈ mL B.I B.g
  bw_w : ∀ i, bw i = ew • bw i
  bwd_w : ∀ i, bwd i = sigA B.I ew • bwd i

  bw_dual : ∀ i j, ZMod' B.I B.g (hA B.I (bwd i) (bw j) - if i = j then ew else 0)

  latticeSpan : ∀ y ∈ B.I.Lf,
    InMod B.I B.g (Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd) y

  e_eq : ∀ x, B.e x = if x ∈ K2set B.I B.g e0 z0 bw then
    star (chi2f B.I psiEf B.g e0 f0 z0 bw bwd x) / ((B.μf (K2set B.I B.g e0 z0 bw)).toReal : ℂ) else 0

  xu : D.what₂.Word → B.I.Gf
  xu_fix : ∀ u a, B.I.fmat (xu u) *ᵥ incl B.I (crdOf B.I ιE bas (eX a)) = incl B.I (crdOf B.I ιE bas (eX a)) ∧
    B.I.fmat (xu u) *ᵥ incl B.I (crdOf B.I ιE bas (fY a)) = incl B.I (crdOf B.I ιE bas (fY a))
  xu_z : ∀ u, InAt B.I B.g B.g (B.I.fmat (xu u)⁻¹ *ᵥ incl B.I (crdOf B.I ιE bas (zu u)) - z0)
  xu_one : ∀ u, OneOff B.I B.g (xu u)

  xu_K : ∀ u, xu u ∈ B.I.Kset

  Vpi : D.what₂.Word → Type
  [vN : ∀ u, NormedAddCommGroup (Vpi u)]
  [vI : ∀ u, InnerProductSpace ℂ (Vpi u)]
  [vF : ∀ u, FiniteDimensional ℂ (Vpi u)]
  piU : ∀ u, B.I.Ginf → (Vpi u →L[ℂ] Vpi u)
  piU_rep : ∀ u, IsRepS B.I
    (Sinf B.I (fun a => crdOf B.I ιE bas (eX a)) (crdOf B.I ιE bas (zu u)))
    (Ninf B.I (fun a => crdOf B.I ιE bas (eX a)) (crdOf B.I ιE bas (zu u))) (piU u)

  Vloc : D.what₂.Word → InfinitePlace B.I.F → Type
  [lN : ∀ u v, NormedAddCommGroup (Vloc u v)]
  [lI : ∀ u v, InnerProductSpace ℂ (Vloc u v)]
  [lF : ∀ u v, FiniteDimensional ℂ (Vloc u v)]
  piLoc : ∀ u v, Matrix (Fin D.R.k) (Fin D.R.k) ℂ → (Vloc u v →L[ℂ] Vloc u v)
  piLoc_type : ∀ u v, IsHCTypeU D.R.k (fun i => ((D.hcW u (pl v)).u i : ℝ)) (piLoc u v)
  wfr : D.what₂.Word → InfinitePlace B.I.F → Fin D.R.k → Fin B.I.n → ℂ
  wfr_on : ∀ u v a b, hJ (B.I.ε v) (wfr u v a) (wfr u v b) = if a = b then 1 else 0
  wfr_perp : ∀ u v a, (∀ c, hJ (B.I.ε v) (rv B.I v (crdOf B.I ιE bas (eX c))) (wfr u v a) = 0 ∧
      hJ (B.I.ε v) (rv B.I v (crdOf B.I ιE bas (fY c))) (wfr u v a) = 0) ∧
    hJ (B.I.ε v) (rv B.I v (crdOf B.I ιE bas (zu u))) (wfr u v a) = 0
  tensU : ∀ u, (∀ v, Vloc u v) → Vpi u
  tensU_inner : ∀ u x y, ⟪tensU u x, tensU u y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ
  tensU_span : ∀ u, Submodule.span ℂ (Set.range (tensU u)) = ⊤
  tensU_equiv : ∀ u, ∀ s ∈ Hset B.I (Set.range (fun a => crdOf B.I ιE bas (eX a)) ∪
      Set.range (fun a => crdOf B.I ιE bas (fY a)) ∪ {crdOf B.I ιE bas (zu u)}), ∀ x,
    piU u s (tensU u x) = tensU u (fun v => piLoc u v (matW B.I (wfr u v) v s) (x v))

  muN : D.what₂.Word → Measure B.I.Ginf
  muH : D.what₂.Word → Measure B.I.Ginf
  muN_haar : ∀ u, IsHaarOnSet B.I
    (Ninf B.I (fun a => crdOf B.I ιE bas (eX a)) (crdOf B.I ιE bas (zu u))) (muN u)
  muH_haar : ∀ u, IsHaarOnSet B.I (Hset B.I (Set.range (fun a => crdOf B.I ιE bas (eX a)) ∪
      Set.range (fun a => crdOf B.I ιE bas (fY a)) ∪ {crdOf B.I ιE bas (zu u)})) (muH u)
  nuQ : D.what₂.Word → Measure B.I.Ginf
  nuQ_weil : ∀ u, IsQuotMeasS B.I (((muN u).prod (muH u)).map (fun p => p.1 * p.2)) (nuQ u)

  Wu : ∀ u, B.I.Ginf → Vpi u
  Wu_spec : ∀ u, IsWu B.I
    (Formalism.L2.SG.ProjRows.phInf B.I B.σ B.w fun v => fdegOf (Formalism.REAL.muG (B.I.ε v)) (B.σ v) (B.w v))
    (Sinf B.I (fun a => crdOf B.I ιE bas (eX a)) (crdOf B.I ιE bas (zu u)))
    (psiInf B.I B.g (fun a => crdOf B.I ιE bas (eX a)) (fun a => crdOf B.I ιE bas (fY a))
      (crdOf B.I ιE bas (zu u)))
    (piU u) (nuQ u) (Wu u)

  Wloc : ∀ u v, Formalism.REAL.UJ (B.I.ε v) → Vloc u v
  Wloc_cont : ∀ u v, Continuous (Wloc u v)
  Wu_tens : ∀ u x, Wu u x = tensU u (fun v => Wloc u v (x v))

  measG : Formalism.L2.SG.Measures.MeasG B.I.cm.sig B.I.J D.R.rS
  measG_norm : measG.IsTextNorm
  measW : ∀ u, Formalism.L2.SG.Measures.MeasW B.I.cm.sig B.I.J
    (⟨fun a => crdOf B.I ιE bas (eX a), fun a => crdOf B.I ιE bas (fY a), crdOf B.I ιE bas (zu u)⟩ :
      Formalism.L2.SG.Sub.Frame B.I.E B.I.n D.R.rS)
  measW_norm : ∀ u, (measW u).IsTextNorm

attribute [instance] HidaSetting.vN HidaSetting.vI HidaSetting.vF HidaSetting.lN HidaSetting.lI HidaSetting.lF

namespace HidaSetting

variable {D : D7} (X : HidaSetting D)

def crd (y : (VS D).V) : Fin X.B.I.n → X.B.I.E := crdOf X.B.I X.ιE X.bas y

def eR : Fin D.R.rS → Fin X.B.I.n → X.B.I.E := fun a => X.crd (X.eX a)
def fR : Fin D.R.rS → Fin X.B.I.n → X.B.I.E := fun a => X.crd (X.fY a)
def zR (u : D.what₂.Word) : Fin X.B.I.n → X.B.I.E := X.crd (X.zu u)

def SinfU (u : D.what₂.Word) : Set X.B.I.Ginf := Sinf X.B.I X.eR (X.zR u)
def NinfU (u : D.what₂.Word) : Set X.B.I.Ginf := Ninf X.B.I X.eR (X.zR u)
def NfinU (u : D.what₂.Word) : Set X.B.I.Gf := Nfin X.B.I X.eR (X.zR u)

def psiInfU (u : D.what₂.Word) : X.B.I.Ginf → ℂ := psiInf X.B.I X.B.g X.eR X.fR (X.zR u)
def psiFinU (u : D.what₂.Word) : X.B.I.Gf → ℂ := psiFin X.B.I X.psiEf X.B.g X.eR X.fR (X.zR u)

def K2 : Set X.B.I.Gf := K2set X.B.I X.B.g X.e0 X.z0 X.bw
def chi2 : X.B.I.Gf → ℂ := chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd

def volK2 : ℝ := (X.B.μf X.K2).toReal

def dv (v : InfinitePlace X.B.I.F) : ℝ := fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)
def ph : X.B.I.Ginf → ℂ := Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w X.dv

def LevelSubgroupCharacter : Prop :=
  1 ∈ X.K2 ∧ (∀ x ∈ X.K2, ∀ y ∈ X.K2, x * y ∈ X.K2) ∧ (∀ x ∈ X.K2, x⁻¹ ∈ X.K2) ∧
    (∀ x ∈ X.K2, ∀ y ∈ X.K2, X.chi2 (x * y) = X.chi2 x * X.chi2 y) ∧ ∀ x ∈ X.K2, ‖X.chi2 x‖ = 1

def LevelSubgroupNormalized : Prop :=
  (∀ x ∈ X.B.I.Kg X.B.g, x ∈ X.K2 ∧ X.chi2 x = 1) ∧ (∀ x ∈ X.K2, x ∈ X.B.I.Kset) ∧
    0 < X.B.μf X.K2 ∧ X.B.μf X.K2 < ⊤

def toInf (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (s : X.B.I.Ginf) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  (Formalism.L2.SG.Measures.splitA X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.AdBridge.toHA X.B.I hb (s, 1))).1
def toFin (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (x : X.B.I.Gf) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  (Formalism.L2.SG.Measures.splitA X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x))).2

def MeasTie (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) : Prop :=
  X.measG.μG = (X.B.I.muA X.B.μf).map (Formalism.L2.SG.AdBridge.toHA X.B.I hb) ∧
    X.measG.μGinf = (Formalism.L2.SG.ProjRows.muInf X.B.I).map (toInf X hb) ∧
    X.measG.μGf = X.B.μf.map (toFin X hb) ∧
    ∀ u, Formalism.L2.SG.Measures.amb (X.measW u).μNinf = (X.muN u).map (toInf X hb) ∧
      Formalism.L2.SG.Measures.amb (X.measW u).μHinf = (X.muH u).map (toInf X hb)

end HidaSetting

end Formalism.L2.SG.HidaSetting
