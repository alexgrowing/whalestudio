import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVtCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.HermitianCurvature.StatementJCT

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate Classical

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

open Formalism.L2.SG.RealObj

section HSForms

variable {Wq Wp : Type*} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem inner_hsEmb {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (A A' : Wq →L[ℂ] Wp) :
    ⟪Formalism.L2.SG.PackageTie.hsEmb A, Formalism.L2.SG.PackageTie.hsEmb A'⟫_ℂ =
      ∑ j, ⟪A (stdOrthonormalBasis ℂ Wq j), A' (stdOrthonormalBasis ℂ Wq j)⟫_ℂ := by
  simp [Formalism.L2.SG.PackageTie.hsEmb, PiLp.inner_apply]

theorem inner_hsVec {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (A A' : Wq →L[ℂ] Wp) :
    ⟪Formalism.FourierDecayAlt.B.hsVec A, Formalism.FourierDecayAlt.B.hsVec A'⟫_ℂ =
      ∑ j, ⟪A (stdOrthonormalBasis ℂ Wq j), A' (stdOrthonormalBasis ℂ Wq j)⟫_ℂ := by
  simp [Formalism.FourierDecayAlt.B.hsVec, PiLp.inner_apply]

private theorem sum_inner_basis_eq_trace_adjoint_comp {U Y : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [FiniteDimensional ℂ U] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ U) (N N' : U →L[ℂ] Y) :
    ∑ j, ⟪N (b j), N' (b j)⟫_ℂ =
      LinearMap.trace ℂ U ((ContinuousLinearMap.adjoint N ∘L N' : U →L[ℂ] U) : U →ₗ[ℂ] U) := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [ContinuousLinearMap.adjoint_inner_right]

theorem hsSum_conj {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] [FiniteDimensional ℂ Wp]
    (e : Wp ≃ₗᵢ[ℂ] V) (e' : Wq ≃ₗᵢ[ℂ] V') (M M' : Wq →L[ℂ] Wp) :
    ∑ j, ⟪((e.toContinuousLinearEquiv : Wp →L[ℂ] V).comp (M.comp (e'.symm.toContinuousLinearEquiv : V' →L[ℂ] Wq)))
        (stdOrthonormalBasis ℂ V' j),
      ((e.toContinuousLinearEquiv : Wp →L[ℂ] V).comp (M'.comp (e'.symm.toContinuousLinearEquiv : V' →L[ℂ] Wq)))
        (stdOrthonormalBasis ℂ V' j)⟫_ℂ =
    ∑ j, ⟪M (stdOrthonormalBasis ℂ Wq j), M' (stdOrthonormalBasis ℂ Wq j)⟫_ℂ := by
  have key := sum_inner_basis_eq_trace_adjoint_comp ((stdOrthonormalBasis ℂ V').map e'.symm) M M'
  simp only [OrthonormalBasis.map_apply] at key
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.inner_map_map]
  rw [key, sum_inner_basis_eq_trace_adjoint_comp]

end HSForms

section Joint

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
variable {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def locOp (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (v : InfinitePlace X.B.I.F) : X.Vloc u' v →L[ℂ] X.Vloc u v :=
  ((eP v).toContinuousLinearEquiv : Wp (S.pl (τ.symm v)) →L[ℂ] X.Vloc u v).comp
    (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
          (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
        Formalism.FourierDecayAlt.D.vecV (T (τ.symm v)).base (ν' (τ.symm v)) (m₀ (τ.symm v)) (f (τ.symm v))
          (Formalism.FourierDecayAlt.D.toStd S.G.r S.g 1 (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p))).comp
      ((eQ v).symm.toContinuousLinearEquiv : X.Vloc u' v →L[ℂ] Wq (S.pl (τ.symm v))))

theorem hsVec_smul {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    Formalism.FourierDecayAlt.B.hsVec (c • A) = c • Formalism.FourierDecayAlt.B.hsVec A := by
  unfold Formalism.FourierDecayAlt.B.hsVec
  ext i
  simp

theorem inner_V0Pt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (hVJ : VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ)
    (p q : Formalism.FourierDecayAlt.TB.Pt D.host.E) (wp wq : Point D.host.E (D.R.rS + 1))
    (hp : ptOfL (D := D) (D.R.rS + 1) p = some wp) (hq : ptOfL (D := D) (D.R.rS + 1) q = some wq)
    (hrp : ∃ γ, IsPtRep X u u' wp γ) (hrq : ∃ γ, IsPtRep X u u' wq γ)
    (hGp : ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' wp) v)
    (hGq : ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' wq) v) :
    ⟪Formalism.L2.SG.PackageTie.hsEmb (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wq),
              Formalism.L2.SG.PackageTie.hsEmb (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wp)⟫_ℂ =
      ∏ j : Fin S.f, ⟪Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ j (Formalism.FourierDecayAlt.C.loc (S.σ j) q),
        Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ j (Formalism.FourierDecayAlt.C.loc (S.σ j) p)⟫_ℂ := by
  rw [inner_hsEmb]
  rw [hsSum_tensor (X.tensU u') (X.tensU_inner u') (X.tensU_span u') (X.tensU u) (X.tensU_inner u)
    (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wq) (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wp)
    (locOp X S u u' T f ν' m₀ τ eP eQ q) (locOp X S u u' T f ν' m₀ τ eP eQ p)
    (fun x => by rw [hVJ q wq hq hrq hGq x]; rfl) (fun x => by rw [hVJ p wp hp hrp hGp x]; rfl)]
  rw [← Fintype.prod_equiv τ.symm (fun v => ⟪Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ (τ.symm v)
      (Formalism.FourierDecayAlt.C.loc (S.σ (τ.symm v)) q), Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ (τ.symm v)
      (Formalism.FourierDecayAlt.C.loc (S.σ (τ.symm v)) p)⟫_ℂ) _ (fun v => rfl)]
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold Formalism.FourierDecayAlt.JC.vecPlace
  rw [← hsVec_smul, ← hsVec_smul, inner_hsVec]
  unfold locOp
  have : FiniteDimensional ℂ (Wp (S.pl (τ.symm v))) := LinearEquiv.finiteDimensional (eP v).symm.toLinearEquiv
  exact hsSum_conj (eP v) (eQ v) _ _

end Joint

section Assembly

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
variable {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def GoodPt (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  (∃ γ, IsPtRep X u u' w γ) ∧ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v

def PtSome (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) : Prop :=
  ∀ p : Formalism.FourierDecayAlt.TB.Pt D.host.E, Formalism.FourierDecayAlt.TB.IsPt p (S.G.r + 1) → ∃ w, ptOfL (D := D) (D.R.rS + 1) p = some w

def WtTie (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)), ptOfL (D := D) (D.R.rS + 1) p = some w →
    GoodPt X u u' w →
    Real.sqrt (nW X u u' w) =
      ∏ j, Real.sqrt (Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd j).G (Formalism.FourierDecayAlt.C.loc (S.σ j) p))

def LZero (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)), ptOfL (D := D) (D.R.rS + 1) p = some w →
    ¬ GoodPt X u u' w → VtPt X u u' sc i0 i0' FdN FdN' νq p = 0

def RZero (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)), ptOfL (D := D) (D.R.rS + 1) p = some w →
    ¬ GoodPt X u u' w → ∃ j,
      Real.sqrt (Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd j).G (Formalism.FourierDecayAlt.C.loc (S.σ j) p)) = 0 ∨
      Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ j (Formalism.FourierDecayAlt.C.loc (S.σ j) p) = 0

theorem alg_prod {ι : Type*} [Fintype ι] (a b : ι → ℝ) (c : ι → ℂ) :
    (starRingEnd ℂ) ((∏ j, b j : ℝ) : ℂ) * (((∏ j, a j : ℝ) : ℂ) * ∏ j, c j) = ∏ j, ((a j * b j : ℝ) : ℂ) * c j := by
  rw [Complex.conj_ofReal]
  simp only [Complex.ofReal_prod, Complex.ofReal_mul, Finset.prod_mul_distrib]
  ring

theorem inner_zero_of {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : H) (h : y = 0) :
    inner ℂ x y = 0 := by
  subst h
  simp

theorem inner_zero_of' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : H) (h : x = 0) :
    inner ℂ x y = 0 := by
  subst h
  simp

theorem rhs_zero (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (p q : Formalism.FourierDecayAlt.TB.Pt D.host.E)
    (h : (∃ j, Real.sqrt (Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd j).G (Formalism.FourierDecayAlt.C.loc (S.σ j) p)) = 0 ∨
      Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ j (Formalism.FourierDecayAlt.C.loc (S.σ j) p) = 0) ∨
      (∃ j, Real.sqrt (Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd j).G (Formalism.FourierDecayAlt.C.loc (S.σ j) q)) = 0 ∨
      Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ j (Formalism.FourierDecayAlt.C.loc (S.σ j) q) = 0)) :
    ∏ v, ((√(Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd v).G (Formalism.FourierDecayAlt.C.loc (S.σ v) p)) *
          √(Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd v).G (Formalism.FourierDecayAlt.C.loc (S.σ v) q)) : ℝ) : ℂ) *
        inner ℂ (Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v (Formalism.FourierDecayAlt.C.loc (S.σ v) q))
          (Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v (Formalism.FourierDecayAlt.C.loc (S.σ v) p)) = 0 := by
  rcases h with ⟨j, hj | hj⟩ | ⟨j, hj | hj⟩ <;>
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

theorem vt_good (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (hVJ : VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ) (hW : WtTie X S u u')
    (p q : Formalism.FourierDecayAlt.TB.Pt D.host.E) (wp wq : Point D.host.E (D.R.rS + 1))
    (hp : ptOfL (D := D) (D.R.rS + 1) p = some wp) (hq : ptOfL (D := D) (D.R.rS + 1) q = some wq)
    (gp : GoodPt X u u' wp) (gq : GoodPt X u u' wq) :
    inner ℂ (VtPt X u u' sc i0 i0' FdN FdN' νq q) (VtPt X u u' sc i0 i0' FdN FdN' νq p) = ∏ v,
      ((√(Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd v).G (Formalism.FourierDecayAlt.C.loc (S.σ v) p)) *
          √(Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd v).G (Formalism.FourierDecayAlt.C.loc (S.σ v) q)) : ℝ) : ℂ) *
        inner ℂ (Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v (Formalism.FourierDecayAlt.C.loc (S.σ v) q))
          (Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v (Formalism.FourierDecayAlt.C.loc (S.σ v) p)) := by
  have ep : VtPt X u u' sc i0 i0' FdN FdN' νq p = ((Real.sqrt (nW X u u' wp) : ℝ) : ℂ) •
      Formalism.L2.SG.PackageTie.hsEmb (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wp) := by
    unfold VtPt; rw [hp]
  have eq' : VtPt X u u' sc i0 i0' FdN FdN' νq q = ((Real.sqrt (nW X u u' wq) : ℝ) : ℂ) •
      Formalism.L2.SG.PackageTie.hsEmb (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wq) := by
    unfold VtPt; rw [hq]
  rw [ep, eq', inner_smul_left, inner_smul_right,
    inner_V0Pt X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ hVJ p q wp wq hp hq gp.1 gq.1 gp.2 gq.2,
    hW p wp hp gp, hW q wq hq gq]
  exact alg_prod _ _ _

theorem vtTensor_of_steps (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (hVJ : VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ) (hPt : PtSome S) (hW : WtTie X S u u')
    (hL : LZero X u u' sc i0 i0' FdN FdN' νq) (hR : RZero X S u u' T f ν' m₀) :
    Formalism.FourierDecayAlt.JCT.VtTensor S T f ν' m₀ (VtPt X u u' sc i0 i0' FdN FdN' νq) := by
  intro p q hpP hqP
  obtain ⟨wp, hp⟩ := hPt p hpP
  obtain ⟨wq, hq⟩ := hPt q hqP
  by_cases gp : GoodPt X u u' wp
  · by_cases gq : GoodPt X u u' wq
    · exact vt_good X S u u' sc i0 i0' FdN FdN' νq T f ν' m₀ τ eP eQ hVJ hW p q wp wq hp hq gp gq
    · rw [rhs_zero S T f ν' m₀ p q (Or.inr (hR q wq hq gq))]
      exact inner_zero_of' _ _ (hL q wq hq gq)
  · rw [rhs_zero S T f ν' m₀ p q (Or.inl (hR p wp hp gp))]
    exact inner_zero_of _ _ (hL p wp hp gp)

end Assembly

end Formalism.L2.SG.Pf.Carrier.CarPinVt
