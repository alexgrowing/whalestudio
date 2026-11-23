import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume

section Pure

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

abbrev Sg (j j' : ℕ) : Type := Fin j ⊕ Fin j'

def sgI (j j' : ℕ) : Matrix (Sg j j') (Sg j j') ℂ := fromBlocks 1 0 0 (-1)

def IsSgU (u : Matrix (Sg j j') (Sg j j') ℂ) : Prop := uᴴ * sgI j j' * u = sgI j j'

def moebW (u : Matrix (Sg j j') (Sg j j') ℂ) (W : Matrix (Fin j') (Fin j) ℂ) : Matrix (Fin j') (Fin j) ℂ :=
  (u.toBlocks₂₁ + u.toBlocks₂₂ * W) * (u.toBlocks₁₁ + u.toBlocks₁₂ * W)⁻¹

def ballPt (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ) : Fin n → ℂ :=
  fun k => W (q.symm k).1 (q.symm k).2.2 (q.symm k).2.1

def moebBall (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ) (t : Fin n → ℂ) : Fin n → ℂ :=
  ballPt q fun τ => moebW (u τ) (ballMat q t τ)ᵀ

end Pure

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

omit [IsCMField E] in

theorem intEmb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def embOf (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (intEmb_injective s)

structure LatEmb (F : UnivFam E Ψ j j' n g Λ) where

  h : HermitianForm (maximalRealSubfield E) E (Fin (j + j') → E)

  e : Λ →+ (Fin (j + j') → E)
  e_inj : Function.Injective e
  e_smul : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x

  Dn : ℕ
  integral : IsDIntegral h Dn e.range
  orth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0

  xi : E

  c : ℝ
  c_pos : 0 < c

  eps : Ψ → ℝ
  eps_sq : ∀ τ, eps τ ^ 2 = 1
  xi_eq : ∀ τ, embOf (F.σ τ) xi = Complex.I * ((c * eps τ : ℝ) : ℂ)
  form_eq : ∀ x y, ((F.form x y : ℤ) : ℚ) = Algebra.trace ℚ E (xi * h.toSesq (e y) (e x))

  lam : Module.Basis (Fin (2 * g)) ℤ Λ

  bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin (j + j') → ℂ)
  bas_eq : ∀ k τ i, bas k τ i = embOf (F.σ τ) (e (lam k) i)

def plc (F : UnivFam E Ψ j j' n g Λ) (τ : Ψ) : InfinitePlace E := InfinitePlace.mk (embOf (F.σ τ))

open Classical in

def tauMat (F : UnivFam E Ψ j j' n g Λ) (a : InfinitePlace E → GL (Fin (j + j')) ℂ) (τ : Ψ) :
    Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  if (plc F τ).embedding = embOf (F.σ τ) then (a (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)
  else (a (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ).map (starRingEnd ℂ)

namespace LatEmb

variable {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

def vec (x : Λ) : Ψ → Fin (j + j') → ℂ := fun τ i => embOf (F.σ τ) (C.e x i)

def gr (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  (gram C.h.toSesq (Pi.basisFun E (Fin (j + j')))).map (embOf (F.σ τ))

def sgr (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ := ((C.eps τ : ℝ) : ℂ) • C.gr τ

def Fm (y y' : Ψ → Fin (j + j') → ℂ) : ℝ :=
  ∑ τ, 2 * (embOf (F.σ τ) C.xi * (star (y' τ) ⬝ᵥ (C.gr τ *ᵥ y τ))).re

def cinv (A : Matrix (Fin (j + j')) (Sg j j') ℂ) (τ : Ψ) : Matrix (Sg j j') (Fin (j + j')) ℂ :=
  sgI j j' * Aᴴ * C.sgr τ

def perExt (R : RiemLat E g Λ) : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
  C.bas.constr ℝ fun k => R.P (C.lam k)

open Classical in

def pPart (R : RiemLat E g Λ) (τ : Ψ) (y : Fin (j + j') → ℂ) : Fin g → ℂ :=
  (1 / 2 : ℂ) • (C.perExt R (Pi.single τ y) - Complex.I • C.perExt R (Pi.single τ (Complex.I • y)))

open Classical in

def pBar (R : RiemLat E g Λ) (τ : Ψ) (y : Fin (j + j') → ℂ) : Fin g → ℂ :=
  (1 / 2 : ℂ) • (C.perExt R (Pi.single τ y) + Complex.I • C.perExt R (Pi.single τ (Complex.I • y)))

structure IsAdapted (R : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) : Prop where
  unit : ∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j'
  ker : ∀ τ (v : Fin j → ℂ), C.pPart R τ (A τ *ᵥ Sum.elim v 0) = 0
  kerBar : ∀ τ (v : Fin j' → ℂ), C.pBar R τ (A τ *ᵥ Sum.elim 0 v) = 0

abbrev Arch : Subgroup (InfinitePlace E → GL (Fin (j + j')) ℂ) := archUnitary C.h (Pi.basisFun E (Fin (j + j')))

def tm (a : C.Arch) (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  tauMat F (a : InfinitePlace E → GL (Fin (j + j')) ℂ) τ

end LatEmb

end Arch

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
