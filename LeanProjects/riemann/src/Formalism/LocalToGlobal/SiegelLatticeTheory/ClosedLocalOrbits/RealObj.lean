import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.HermitianCurvature.StatementC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.HermitianCurvature.StatementD

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal Classical
open Matrix

namespace Formalism.L2.SG.RealObj

section Lin

variable {n r : ℕ}

def fam (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Fin (r + 1) → Fin n → ℂ :=
  Fin.snoc (α := fun _ => Fin n → ℂ) e z

def famSc (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Fin (r + 1) → Fin n → ℂ :=
  fun a => (((sc : ℂ) ^ (r - a.1))⁻¹) • fam e z a

def Zhat (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun a b => Formalism.L2.SG.HidaSetting.hJ ε (f a) (g *ᵥ f' b)

def Dl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : ℕ) : ℂ :=
  if h : l ≤ r + 1 then (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def cl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : ℕ) : ℂ := Dl Z l / Dl Z (l - 1)

def Gv (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ℝ :=
  ‖Dl Z (r + 1)‖ ^ 2 - T * T' * ‖Dl Z r‖ ^ 2

def BigCell (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Prop :=
  ∀ l, 1 ≤ l → l ≤ r + 1 → Dl Z l ≠ 0

def IsReg (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Prop :=
  (∀ l, 1 ≤ l → l ≤ r → Dl Z l ≠ 0) ∧ Gv T T' Z ≠ 0

def modC (x : ℂ) : ℝ := ‖x‖ ^ 2

def JacV (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ℝ :=
  ∏ l ∈ Finset.Icc 1 r, modC (Dl Z l) ^ 2

end Lin

section Loc

variable {n : ℕ} {ε : Fin n → Bool}

def StSet (N N' : Set (Formalism.REAL.UJ ε)) (γ : Formalism.REAL.UJ ε) : Set (Formalism.REAL.UJ ε) :=
  {y | y ∈ N ∧ γ⁻¹ * y * γ ∈ N'}

def IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) (μ : Measure (Formalism.REAL.UJ ε)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ

def IsQuotLoc (μR ν : Measure (Formalism.REAL.UJ ε)) : Prop :=
  ∀ f : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x ∂(Formalism.REAL.muG ε) = ∫⁻ x, (∫⁻ s, f (s * x) ∂μR) ∂ν

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

def Jv (ν : Measure (Formalism.REAL.UJ ε)) (W : Formalism.REAL.UJ ε → V) (W' : Formalism.REAL.UJ ε → V')
    (γ : Formalism.REAL.UJ ε) : V' →L[ℂ] V :=
  Formalism.L2.SG.TermOp.OO ν Set.univ W W' γ

end Loc

section HS

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def hs2 (A : V' →L[ℂ] V) : ℝ :=
  ∑ i, ‖A (stdOrthonormalBasis ℂ V' i)‖ ^ 2

end HS

section Glob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def rdOf : ℝ := D.host.rdE

def Tw (u : D.what₂.Word) : ℝ := (((D.mem u).A.T : ℕ) : ℝ)

def frm (u : D.what₂.Word) (sc : ℝ) (v : InfinitePlace X.B.I.F) : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ :=
  famSc sc (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u))

def ZX (u u' : D.what₂.Word) (sc : ℝ) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
  Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat (γ v))

def ZhatO {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun a b => (-1 : ℂ) ^ (r - b.1) * Z a b

def GX (u u' : D.what₂.Word) (sc : ℝ) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) : ℝ :=
  Gv (Tw u) (Tw u') (ZX X u u' sc γ v)

def RegX (u u' : D.what₂.Word) (γ : X.B.I.Ginf) : Prop :=
  ∀ v, IsReg (Tw u) (Tw u') (ZX X u u' 1 γ v)

def OOinf (u u' : D.what₂.Word) (γ : X.B.I.Ginf) : X.Vpi u' →L[ℂ] X.Vpi u :=
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  TermOp.OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

abbrev Cinf : Type := InfinitePlace X.B.I.F → Fin (D.R.rS + 1) → ℂ

def dcInf : Measure (Cinf X) :=
  Measure.pi fun _ => Measure.pi fun _ => (2 : ℝ≥0∞) • (volume : Measure ℂ)

def HasDiag (u u' : D.what₂.Word) (sc : ℝ) (c : Cinf X) (γ : X.B.I.Ginf) : Prop :=
  ∀ v, ZX X u u' sc γ v = Matrix.diagonal (c v)

def hOf (u u' : D.what₂.Word) (sc : ℝ) (c : Cinf X) : X.B.I.Ginf :=
  if h : ∃ γ, HasDiag X u u' sc c γ then h.choose else 1

def Good (u u' : D.what₂.Word) : Set (Cinf X) :=
  {c | ∀ v, (∀ l, c v l ≠ 0) ∧ 0 < Gv (Tw u) (Tw u') (Matrix.diagonal (c v))}

def wt (u u' : D.what₂.Word) (c : Cinf X) : ℝ :=
  ∏ v, Gv (Tw u) (Tw u') (Matrix.diagonal (c v)) ^ (D.R.k - 1) * JacV (Matrix.diagonal (c v))

def muS (u : D.what₂.Word) : Measure X.B.I.Ginf :=
  ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)

def Disint (u u' : D.what₂.Word) (sc C : ℝ) : Prop :=
  ∀ φ : X.B.I.Ginf → ℝ≥0∞, Measurable φ →
    ∫⁻ x, φ x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∫⁻ c in Good X u u', ENNReal.ofReal (C * wt X u u' c) *
        ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' sc c * s'⁻¹) ∂(muS X u') ∂(muS X u) ∂(dcInf X)

def DisintegrationConstantPositive (u u' : D.what₂.Word) (sc : ℝ) : Prop := ∃ C, 0 < C ∧ Disint X u u' sc C

def DisintegrationConstant (u u' : D.what₂.Word) (sc : ℝ) : ℝ :=
  if h : ∃ C, 0 < C ∧ Disint X u u' sc C then h.choose else 0

def nuM (u u' : D.what₂.Word) (sc : ℝ) : Measure (Cinf X) :=
  ((dcInf X).restrict (Good X u u')).withDensity
    (fun c => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c))

def hilbertSchmidtSqGram (u u' : D.what₂.Word) (sc : ℝ) (c : Cinf X) : ℝ :=
  hs2 (OOinf X u u' (hOf X u u' sc c))

def intOOe (u u' : D.what₂.Word) (sc : ℝ) : ℝ≥0∞ :=
  ∫⁻ c, ENNReal.ofReal (hilbertSchmidtSqGram X u u' sc c) ∂(nuM X u u' sc)

def intCe (u u' : D.what₂.Word) (sc : ℝ) : ℝ≥0∞ :=
  ∫⁻ c in Good X u u', ENNReal.ofReal (wt X u u' c * hilbertSchmidtSqGram X u u' sc c) ∂(dcInf X)

def IntOO (u u' : D.what₂.Word) (sc : ℝ) : ℝ := (intOOe X u u' sc).toReal

def IntC (u u' : D.what₂.Word) (sc : ℝ) : ℝ := (intCe X u u' sc).toReal

def degX : ℝ := ∏ v, X.dv v

def CoordOK (u u' : D.what₂.Word) (sc : ℝ) : Prop :=
  (∀ c ∈ Good X u u', ∃ γ, HasDiag X u u' sc c γ) ∧
    ∀ c ∈ Good X u u', TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') (hOf X u u' sc c)

def InInfinityX (u u' : D.what₂.Word) (sc : ℝ) : Prop :=
  DisintegrationConstantPositive X u u' sc ∧ CoordOK X u u' sc ∧ intOOe X u u' sc ≤ ENNReal.ofReal (1 / degX X)

def InNuX (u u' : D.what₂.Word) (sc : ℝ) : Prop :=
  intOOe X u u' sc = ENNReal.ofReal (DisintegrationConstant X u u' sc) * intCe X u u' sc

def OOIndep (u u' : D.what₂.Word) (sc : ℝ) : Prop :=
  ∀ c ∈ Good X u u', ∀ γ γ', HasDiag X u u' sc c γ → HasDiag X u u' sc c γ' →
    hs2 (OOinf X u u' γ) = hs2 (OOinf X u u' γ')

def OOEquivar (u u' : D.what₂.Word) : Prop :=
  ∀ (γ : X.B.I.Ginf), ∀ s ∈ X.SinfU u, ∀ s' ∈ X.SinfU u',
    OOinf X u u' (s * γ * s'⁻¹) = (X.psiInfU u s * conj (X.psiInfU u' s')) •
      ((X.piU u s).comp ((OOinf X u u' γ).comp (X.piU u' s'⁻¹)))

def OOFactor (u u' : D.what₂.Word) : Prop :=
  ∀ (γ : X.B.I.Ginf) (y : ∀ v, X.Vloc u' v),
    OOinf X u u' γ (X.tensU u' y) =
      X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Jv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) (γ v)) (y v))

end Glob

section Frame

variable {n r k : ℕ}

def eN (x : Fin k → ℂ) : ℝ := Real.sqrt (∑ i, ‖x i‖ ^ 2)

def wCoord (ε : Fin n → Bool) (wb : Fin k → Fin n → ℂ) (y : Fin n → ℂ) : Fin k → ℂ :=
  fun i => Formalism.L2.SG.HidaSetting.hJ ε (wb i) y

def xPr (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (f' : Fin (r + 1) → Fin n → ℂ) : Fin n → ℂ :=
  ∑ b, Matrix.adjugate Z b (Fin.last r) • (g *ᵥ f' b)

def xUn (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (f : Fin (r + 1) → Fin n → ℂ) : Fin n → ℂ :=
  ∑ a, star (Matrix.adjugate Z (Fin.last r) a) • f a

def IsDFrame (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (g gi : Matrix (Fin n) (Fin n) ℂ)
    (wb wb' : Fin k → Fin n → ℂ) (i0 i0' : Fin k) (h h' : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  h ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ h' ∈ Matrix.unitaryGroup (Fin k) ℂ ∧
    h *ᵥ Pi.single i0 1 = ((eN ((Dl (Zhat ε f f' g) (r + 1))⁻¹ • wCoord ε wb (xPr (Zhat ε f f' g) g f')))⁻¹ : ℂ) •
      ((Dl (Zhat ε f f' g) (r + 1))⁻¹ • wCoord ε wb (xPr (Zhat ε f f' g) g f')) ∧
    h' *ᵥ Pi.single i0' 1 =
      ((eN ((star (Dl (Zhat ε f f' g) (r + 1)))⁻¹ • wCoord ε wb' (gi *ᵥ xUn (Zhat ε f f' g) f)))⁻¹ : ℂ) •
      ((star (Dl (Zhat ε f f' g) (r + 1)))⁻¹ • wCoord ε wb' (gi *ᵥ xUn (Zhat ε f f' g) f)) ∧
    ∀ y : Fin n → ℂ, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) y = 0) →
      (∀ b, Formalism.L2.SG.HidaSetting.hJ ε (g *ᵥ f' b) y = 0) →
      h *ᵥ (star h' *ᵥ wCoord ε wb' (gi *ᵥ y)) = wCoord ε wb y

end Frame

section GlobV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def HsetU (u : D.what₂.Word) : Set X.B.I.Ginf :=
  Formalism.L2.SG.HidaSetting.Hset X.B.I (Set.range X.eR ∪ Set.range X.fR ∪ {X.zR u})

def StInf (u u' : D.what₂.Word) (γ : X.B.I.Ginf) : Set X.B.I.Ginf :=
  {y | y ∈ X.NinfU u ∧ γ⁻¹ * y * γ ∈ X.NinfU u'}

def IsDFrameX (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (γ h h' : X.B.I.Ginf) : Prop :=
  h ∈ HsetU X u ∧ h' ∈ HsetU X u' ∧ ∀ v,
    IsDFrame (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat (γ v)) (uMat ((γ v)⁻¹)) (X.wfr u v) (X.wfr u' v)
      (i0 v) (i0' v) (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v h) (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v h')

def NuQOK (u u' : D.what₂.Word) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ γ, (RegX X u u' γ → νq γ = Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
    ∃ μR, Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' γ) μR ∧ Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR (νq γ)

def unscaledFrameConjugatedOperator (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (ν : Measure X.B.I.Ginf) (γ : X.B.I.Ginf) : X.Vpi u' →L[ℂ] X.Vpi u :=
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  if h : ∃ p : X.B.I.Ginf × X.B.I.Ginf, IsDFrameX X u u' sc i0 i0' γ p.1 p.2 then
    (X.piU u h.choose.1⁻¹).comp ((TermOp.OO ν Set.univ (X.Wu u) (X.Wu u') γ).comp (X.piU u' h.choose.2))
  else 0

def VG (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (ν : Measure X.B.I.Ginf) (γ : X.B.I.Ginf) : X.Vpi u' →L[ℂ] X.Vpi u :=
  ((TermOp.scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) • unscaledFrameConjugatedOperator X u u' sc i0 i0' ν γ

def ptC (v : InfinitePlace X.B.I.F) (w : Point D.host.E (D.R.rS + 1)) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
  (ptMat w).map (fun t => X.B.I.φ v (X.ιE.symm t))

def IsPtRep (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) : Prop :=
  ∀ v, ZhatO (ZX X u u' 1 γ v) = ptC X v w

def gamW (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) : X.B.I.Ginf :=
  if h : ∃ γ, IsPtRep X u u' w γ then h.choose else 1

def VPt (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1)) :
    X.Vpi u' →L[ℂ] X.Vpi u :=
  if ∃ γ, IsPtRep X u u' w γ then VG X u u' sc i0 i0' FdN FdN' (νq (gamW X u u' w)) (gamW X u u' w) else 0

def unscaledOperatorAtPointRepresentative (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1)) : X.Vpi u' →L[ℂ] X.Vpi u :=
  if ∃ γ, IsPtRep X u u' w γ then unscaledFrameConjugatedOperator X u u' sc i0 i0' (νq (gamW X u u' w)) (gamW X u u' w) else 0

def NGPt (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) : ℝ :=
  ∏ v, GX X u u' D.host.rdE (gamW X u u' w) v

def ptOfL (i : ℕ) (x : Formalism.FourierDecayAlt.TB.Pt D.host.E) : Option (Point D.host.E i) :=
  Formalism.L2.SG.DataInst.ptOfList (D := D) i x

def nHead (v : InfinitePlace X.B.I.F) : ℕ → List (D.host.E × ℕ) → ℝ
  | _, [] => 1
  | b, (t, s) :: rest =>
      ((D.host.rdE ^ (2 * (D.R.rS + 1) - b - (b + s - 1)))⁻¹ * ‖X.B.I.φ v (X.ιE.symm t)‖) ^
        (2 * s * (2 * (D.R.rS + 1 - (b + s - 1)) + s - 1)) * nHead v (b + s) rest

def nW (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) : ℝ :=
  ∏ v, GX X u u' D.host.rdE (gamW X u u' w) v ^ (D.R.k - 1) * nHead X v 1 w.1

def VtPt (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (_FdN _FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) :
    Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) :=
  match ptOfL (D.R.rS + 1) p with
  | some w => ((Real.sqrt (nW X u u' w) : ℝ) : ℂ) •
      Formalism.L2.SG.PackageTie.hsEmb (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq w)
  | none => 0

def PtRepExists (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1),
    (∀ v, 0 < Gv (Tw u) (Tw u') (ZhatO (ptC X v w))) →
      ∃ γ, IsPtRep X u u' w γ ∧ ∃ h h', IsDFrameX X u u' sc i0 i0' γ h h'

def VIndep (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  NuQOK X u u' νq →
  ∀ γ h₁ h₁' h₂ h₂', IsDFrameX X u u' sc i0 i0' γ h₁ h₁' → IsDFrameX X u u' sc i0 i0' γ h₂ h₂' →
    (X.piU u h₁⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        TermOp.OO (νq γ) Set.univ (X.Wu u) (X.Wu u') γ).comp (X.piU u' h₁')) =
      (X.piU u h₂⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        TermOp.OO (νq γ) Set.univ (X.Wu u) (X.Wu u') γ).comp (X.piU u' h₂'))

def VEquivar (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) : Prop :=
  ∀ γ, RegX X u u' γ → ∀ n ∈ X.NinfU u, ∀ n' ∈ X.NinfU u', ∀ h ∈ HsetU X u, ∀ h' ∈ HsetU X u',
    VG X u u' sc i0 i0' FdN FdN' (Formalism.L2.SG.ProjRows.muInf X.B.I) (n * h * γ * h'⁻¹ * n') =
      (X.psiInfU u n * X.psiInfU u' n') • VG X u u' sc i0 i0' FdN FdN' (Formalism.L2.SG.ProjRows.muInf X.B.I) γ

def VNorm (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ γ, (∃ h h', IsDFrameX X u u' sc i0 i0' γ h h') →
    hs2 (VG X u u' sc i0 i0' FdN FdN' (νq γ) γ) =
      (TermOp.scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2) ^ 2 *
        hs2 (haveI := FiniteDimensional.complete ℂ (X.Vpi u); TermOp.OO (νq γ) Set.univ (X.Wu u) (X.Wu u') γ)

def OOtReg (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)) :
    Prop :=
  TermOp.FrameTie X u u' F0 F0' →
  ∀ t : TermOp.GTerm X u u' F0 F0' what₂ rows', RegX X u u' t.pt.1 → TermOp.OOt t = OOinf X u u' t.pt.1

def FormReg (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)) :
    Prop :=
  TermOp.FrameTie X u u' F0 F0' →
  ∀ (t : TermOp.GTerm X u u' F0 F0' what₂ rows') (w : Point D.host.E (D.R.rS + 1))
    (L U : Formalism.L2.SG.PairVal.MatR D),
    RegX X u u' t.pt.1 → IsLoUni L → IsUpUni U →
    (∀ v, ZhatO (ZX X u u' 1 t.pt.1 v) = (L * ptMat w * U).map (fun x => X.B.I.φ v (X.ιE.symm x))) →
    ∃ γw, IsPtRep X u u' w γw ∧ ∃ h ∈ HsetU X u, ∃ h' ∈ HsetU X u', ∃ n ∈ X.NinfU u, ∃ n' ∈ X.NinfU u',
      t.pt.1 = n * h * γw * h'⁻¹ * n' ∧
      TermOp.OOt t = Formalism.L2.SG.PairVal.phasePair (gS D) L U •
        ((X.piU u h).comp ((OOinf X u u' γw).comp (X.piU u' h'⁻¹)))

end GlobV

section Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def blkOf {K : Type*} : List (K × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (_, s) :: bs, i => if i < s then 0 else blkOf bs (i - s) + 1

def FreeE (w : Point D.host.E (D.R.rS + 1)) : Type :=
  {p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) // p.1 < p.2 ∧ blkOf w.1 p.1.1 = blkOf w.1 p.2.1}

instance (w : Point D.host.E (D.R.rS + 1)) : Fintype (FreeE w) := by unfold FreeE; infer_instance

def stCoord (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ y : X.B.I.Ginf) :
    InfinitePlace X.B.I.F → FreeE w → ℂ :=
  fun v p => ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1)) *
    Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v)
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR ⟨p.1.1.1, by have := p.2.1; omega⟩))
      (uMat ((γ⁻¹ * y * γ) v) *ᵥ frm X u' D.host.rdE v p.1.2)

def muStab (w : Point D.host.E (D.R.rS + 1)) : Measure (InfinitePlace X.B.I.F → FreeE w → ℂ) :=
  Measure.pi fun _ => Measure.pi fun _ =>
    ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) • (volume : Measure ℂ)

def NuQPin (u u' : D.what₂.Word) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  (∀ γ, RegX X u u' γ → νq γ = Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    ∃ μR, Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR ∧
      Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR (νq (gamW X u u' w)) ∧
      μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w

variable {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def TopTie (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (τ : Fin S.f ≃ InfinitePlace X.B.I.F) : Prop :=
  Formalism.FourierDecayAlt.C.PropGram S (VtPt X u u' sc i0 i0' FdN FdN' νq) ∧
  (∀ j x, S.emb j (X.ιE x) = X.B.I.φ (τ j) x) ∧
  ∀ j (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
      (Formalism.FourierDecayAlt.D.ptLast (Formalism.FourierDecayAlt.C.loc (S.emb j) p)).1 = 1 →
      (S.pd j).G (Formalism.FourierDecayAlt.C.loc (S.emb j) p) =
        GX X u u' D.host.rdE (gamW X u u' w) (τ j) /
          ‖Dl (ZX X u u' D.host.rdE (gamW X u u' w) (τ j)) D.R.rS‖ ^ 2

end Comparison₂

section Built

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def cTor (g : ℝ) (r a : ℕ) : ℂ := (-(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ))) ^ (r - a)

def IsTransp (v : InfinitePlace X.B.I.F) (g : ℝ) (k r : ℕ) (Q : Matrix (Fin X.B.I.n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin X.B.I.n) ℂ) : Prop :=
  Qi * Q = 1 ∧ Q * Qi = 1 ∧ Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q = Formalism.QuantumDeterminants.Hpk k r ∧
  ∀ (a : Fin r) (b : Fin D.R.rS), (a : ℕ) = b →
    Q *ᵥ Pi.single (Formalism.QuantumDeterminants.eI k r a) 1 = cTor g r a • Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR b) ∧
    Q *ᵥ Pi.single (Formalism.QuantumDeterminants.esI k r a) 1 = (star (cTor g r a))⁻¹ • Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR b)

def matQ {n k : ℕ} (ε : Fin n → Bool) (wf : Fin k → Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun a b => Formalism.L2.SG.HidaSetting.hJ ε (wf a) (g *ᵥ wf b)

def trG {n m : ℕ} {ε : Fin n → Bool} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (γ : Formalism.REAL.UJ ε) : Matrix (Fin m) (Fin m) ℂ :=
  Qi * uMat γ * Q

variable {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def BuiltFromX (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (_f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ)
    (Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v) : Prop :=
  ∀ v, IsTransp X v (S.g : ℝ) S.G.k S.G.r (Q v) (Qi v) ∧
    (T (τ.symm v)).base.z = Qi v *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u) ∧
    (T (τ.symm v)).base.z' = Qi v *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u') ∧
    (∀ m, (T (τ.symm v)).base.π m = ((eP v).symm.toContinuousLinearEquiv : X.Vloc u v →L[ℂ] _).comp
      ((X.piLoc u v (matQ (X.B.I.ε v) (X.wfr u v) (Q v * m * Qi v))).comp
        ((eP v).toContinuousLinearEquiv : _ →L[ℂ] X.Vloc u v))) ∧
    (∀ m, (T (τ.symm v)).base.π' m = ((eQ v).symm.toContinuousLinearEquiv : X.Vloc u' v →L[ℂ] _).comp
      ((X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (Q v * m * Qi v))).comp
        ((eQ v).toContinuousLinearEquiv : _ →L[ℂ] X.Vloc u' v))) ∧
    (T (τ.symm v)).base.μG = (Formalism.REAL.muG (X.B.I.ε v)).map (fun γ => Matrix.of.symm (trG (Q v) (Qi v) γ)) ∧
    (∃ μS : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      IsHaarLoc {γ | trG (Q v) (Qi v) γ ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T (τ.symm v)).base.z} μS ∧
      μS.map (fun γ => Matrix.of.symm (trG (Q v) (Qi v) γ)) =
        ((T (τ.symm v)).base.μN.prod (T (τ.symm v)).base.μW).map
          (fun p => Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2)))

def BaseFromX (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ)
    (Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r) : Prop :=
  ∀ v, i0 v = i0' v ∧ ν' (τ.symm v) = Qi v *ᵥ X.wfr u' v (i0' v) ∧
    ∀ i, (Q v * m₀ (τ.symm v) * Qi v) *ᵥ X.wfr u' v i = X.wfr u v i

def VJoint [∀ x, FiniteDimensional ℂ (Wq x)] (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ x : ∀ v, X.Vloc u' v,
      unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq w (X.tensU u' x) =
        X.tensU u (fun v => eP v
          (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
              (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
            Formalism.FourierDecayAlt.D.vecV (T (τ.symm v)).base (ν' (τ.symm v)) (m₀ (τ.symm v)) (f (τ.symm v))
              (Formalism.FourierDecayAlt.D.toStd S.G.r S.g 1 (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p)))
            ((eQ v).symm (x v))))

end Built

section Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def CarrierInput (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (C₄ jn : ℝ)
    (CA : ℝ) (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ) : Prop :=
  ∃ (Wp Wq : InfinitePlace D.host.E → Type) (_ : ∀ x, NormedAddCommGroup (Wp x)) (_ : ∀ x, InnerProductSpace ℂ (Wp x))
    (_ : ∀ x, NormedAddCommGroup (Wq x)) (_ : ∀ x, InnerProductSpace ℂ (Wq x)) (_ : ∀ x, FiniteDimensional ℂ (Wq x))
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (top : ∀ j : Fin S.f, (Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) → List Formalism.FourierDecayAlt.C.Letter →
      Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ)
    (Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v),
    S.CA = CA ∧ S.G = G0 ∧ S.de = de ∧ S.de' = de' ∧ S.l = l ∧
    Formalism.L2.SG.DataInst.Compat S u u' ∧ Formalism.FourierDecayAlt.D.IsBuilt S T f χ ν' m₀ top A₀ ∧
    BuiltFromX X S u u' T f τ Q Qi eP eQ ∧ BaseFromX X S u u' i0 i0' τ Q Qi ν' m₀ ∧
    TopTie X S u u' sc i0 i0' FdN FdN' νq τ ∧ VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ ∧
    Formalism.FourierDecayAlt.PB.RealInputs (Formalism.L2.SG.DataInst.dOf S δ M u u') C₄ jn (VtPt X u u' sc i0 i0' FdN FdN' νq)

def CarrierInput0 (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (C₄ jn : ℝ)
    (CA : ℝ) (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ) : Prop :=
  ∃ (Wp Wq : InfinitePlace D.host.E → Type) (_ : ∀ x, NormedAddCommGroup (Wp x)) (_ : ∀ x, InnerProductSpace ℂ (Wp x))
    (_ : ∀ x, NormedAddCommGroup (Wq x)) (_ : ∀ x, InnerProductSpace ℂ (Wq x)) (_ : ∀ x, FiniteDimensional ℂ (Wq x))
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (top : ∀ j : Fin S.f, (Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) → List Formalism.FourierDecayAlt.C.Letter →
      Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ)
    (Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v),
    S.CA = CA ∧ S.G = G0 ∧ S.de = de ∧ S.de' = de' ∧ S.l = l ∧
    Formalism.L2.SG.DataInst.Compat S u u' ∧ BaseFromX X S u u' i0 i0' τ Q Qi ν' m₀ ∧
    TopTie X S u u' sc i0 i0' FdN FdN' νq τ ∧ VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ ∧
    Formalism.FourierDecayAlt.PB.RealInputs (Formalism.L2.SG.DataInst.dOf S δ M u u') C₄ jn (VtPt X u u' sc i0 i0' FdN FdN' νq)

def RowsSumX (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (κ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℕ) (nc : ℝ) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  PtRepExists X u u' sc i0 i0' ∧ NuQPin X u u' νq ∧
    Formalism.L2.SG.DataInst.RowsSum (Formalism.L2.SG.PairVal.vRdef D u u' F0 what₂ δ M) κ nc
      (VtPt X u u' sc i0 i0' FdN FdN' νq)

end Carrier

section Proofs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hilbert_schmidt_nonneg_alt {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) : 0 ≤ hs2 A := by
  unfold hs2
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem cooOf_nonneg (u u' : D.what₂.Word) (sc : ℝ) : 0 ≤ DisintegrationConstant X u u' sc := by
  unfold DisintegrationConstant
  split_ifs with h
  · exact h.choose_spec.1.le
  · exact le_rfl

theorem inNuX_of_meas (u u' : D.what₂.Word) (sc : ℝ) (hm : Measurable (wt X u u')) : InNuX X u u' sc := by
  have hC := cooOf_nonneg X u u' sc
  have hf : Measurable (fun c => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hm)
  have key : ∀ c, ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c) * ENNReal.ofReal (hilbertSchmidtSqGram X u u' sc c) =
      ENNReal.ofReal (DisintegrationConstant X u u' sc) * ENNReal.ofReal (wt X u u' c * hilbertSchmidtSqGram X u u' sc c) := by
    intro c
    have ho : 0 ≤ hilbertSchmidtSqGram X u u' sc c := hilbert_schmidt_nonneg_alt _
    rcases le_total 0 (wt X u u' c) with hw | hw
    · rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_mul hw, mul_assoc]
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hC hw),
        ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hw ho), zero_mul, mul_zero]
  unfold InNuX intOOe intCe nuM
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hf
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext c
  exact key c

end Proofs

end Formalism.L2.SG.RealObj
