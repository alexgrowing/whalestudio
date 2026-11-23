import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts

variable {D : D7}

variable (D) in

def Sizes : Prop :=
  1800 < D.R.r ∧ ∀ (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m),
    2 * (bigN D : ℚ) ^ 3 < (D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩

section Arrow

variable (θ : InfFam D)

def IsCuspOfType (N : Node D) (φ : GA D N.V → ℂ) : Prop :=
  IsAutFunSm θ N.V φ ∧ IsCuspFun N.V φ ∧ ∀ τ, IsTypeAt θ N.V τ (N.S τ) φ

variable {A B : Node D} {P : Type} (m : A.MeasDat)

def LiftsMult (K : P → GA D B.V → GA D A.V → ℂ) (It : P → SmT A.M → SmT B.M) : Prop :=
  ∀ F ∈ A.Cusp θ, ∃ F' ∈ B.Cusp θ, ∀ (p : P) (v : SmT A.M) (h : GA D B.V),
    IntegrableOn (fun g => K p h g * F v g) m.fd m.ν ∧ ∫ g in m.fd, K p h g * F v g ∂m.ν = F' (It p v) h

def LiftsSmooth (K : GA D B.V → GA D A.V → ℂ) : Prop :=
  ∀ φ, IsCuspOfType θ A φ → (∀ h, IntegrableOn (fun g => K h g * φ g) m.fd m.ν) ∧
    IsCuspOfType θ B fun h => ∫ g in m.fd, K h g * φ g ∂m.ν

end Arrow

section Grid

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

structure RowBase : Prop where

  lev : R.toLevCh.Is A.μ0

  inf : IsInfFam R.θ

  measY : R.models_νY

  measY' : R.models_νY'

  measX : R.models_νX

variable {R}

variable (G : GridPre R)

structure CuspAlong : Prop where

  X : ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f →
    LiftsMult R.θ (A := G.V i j) (B := G.V (i + 1) j) (G.meas t i j)
      (fun p h g => thetaKO (G.X i j).ω h g (fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f p)) fun p v => (G.X i j).It p v

  th : ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) f →
    LiftsMult R.θ (A := G.V i (j + 1)) (B := G.V i j) (G.meas t i (j + 1))
      (fun p h g => thetaKO (G.th t i j).ω h g (fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) f p)) fun p v => (G.th t i j).It p v

  up : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    LiftsMult R.θ (A := G.P i) (B := G.P (i + 1)) (G.mP i)
      (fun p h g => starRingEnd ℂ (thetaKO (G.dn i).ω h g (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f p))) fun p v => G.ItU i p v

  dn : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    LiftsMult R.θ (A := G.P (i + 1)) (B := G.P i) (G.mP (i + 1))
      (fun p h g => thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f p)) fun p v => (G.dn i).It p v

  col : ∀ t j, j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) f →
    LiftsMult R.θ (A := G.Xp j) (B := G.Xp (j + 1)) (G.measX j)
      (fun p h g => thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) f p)) fun p v => (G.col t j).It p v

structure CuspAlongSmooth : Prop where

  X : ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.V (i + 1) j).V) (G.V i j).V Φ →
    LiftsSmooth R.θ (A := G.V i j) (B := G.V (i + 1) j) (G.meas t i j) fun h g => thetaKO (G.X i j).ω h g Φ

  th : ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ →
    LiftsSmooth R.θ (A := G.V i (j + 1)) (B := G.V i j) (G.meas t i (j + 1)) fun h g => thetaKO (G.th t i j).ω h g Φ

  up : ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V Φ →
    LiftsSmooth R.θ (A := G.P i) (B := G.P (i + 1)) (G.mP i) fun h g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)

  dn : ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V Φ →
    LiftsSmooth R.θ (A := G.P (i + 1)) (B := G.P i) (G.mP (i + 1)) fun h g => thetaKO (G.dn i).ω g h Φ

  col : ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    LiftsSmooth R.θ (A := G.Xp j) (B := G.Xp (j + 1)) (G.measX j) fun h g => thetaKO (G.col t j).ω g h Φ

end Grid

def LiftsCuspidalAt (D : D7) : Prop :=
  Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GridPre R),
    RowBase R → G.Is → CuspAlong G

def LiftsCuspidal : Prop := ∀ D : D7, LiftsCuspidalAt D

def LiftsCuspidalSmoothAt (D : D7) : Prop :=
  Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GridPre R),
    RowBase R → G.Is → CuspAlongSmooth G

theorem LiftsMult.exists_linear {θ : InfFam D} {A B : Node D} {P : Type} {m : A.MeasDat} {K : P → GA D B.V → GA D A.V → ℂ}
    {It : P → SmT A.M → SmT B.M} (H : LiftsMult θ m K It) :
    ∃ io : A.Cusp θ →ₗ[ℂ] B.Cusp θ, ∀ (F : A.Cusp θ) p v h,
      IntegrableOn (fun g => K p h g * F.1 v g) m.fd m.ν ∧ ∫ g in m.fd, K p h g * F.1 v g ∂m.ν = (io F).1 (It p v) h := by
  classical
  let b := Module.Free.chooseBasis ℂ (A.Cusp θ)
  choose F' hF'mem hF' using fun i => H (b i).1 (b i).2
  let io := b.constr ℂ (fun i => (⟨F' i, hF'mem i⟩ : B.Cusp θ))
  refine ⟨io, fun F => ?_⟩
  have hF : F ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    intro p v h
    simp only [io, b.constr_basis]
    exact hF' i p v h
  | zero =>
    intro p v h
    simp
  | add x y _ _ hx hy =>
    intro p v h
    obtain ⟨hx1, hx2⟩ := hx p v h
    obtain ⟨hy1, hy2⟩ := hy p v h
    have e : (fun g => K p h g * (x + y).1 v g) = fun g => K p h g * x.1 v g + K p h g * y.1 v g := by
      funext g
      simp [mul_add]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hx1.add hy1
    · rw [e, integral_add hx1 hy1, hx2, hy2, map_add]
      simp
  | smul c x _ hx =>
    intro p v h
    obtain ⟨hx1, hx2⟩ := hx p v h
    have e : (fun g => K p h g * (c • x).1 v g) = fun g => c * (K p h g * x.1 v g) := by
      funext g
      simp [mul_left_comm]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hx1.const_mul c
    · have h3 : (io (c • x)).1 (It p v) h = c * (io x).1 (It p v) h := by
        simp only [map_smul, Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      rw [h3, e, integral_const_mul, hx2]

section

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem cuspAlong_iff_hasLifts (G : GridPre R) : CuspAlong G ↔ G.HasLifts := by
  constructor
  · intro hc
    refine { X := ?_, th := ?_, col := ?_, dn := ?_, up := ?_ }
    · intro t i j hi hj f hf
      obtain ⟨io, hio⟩ := (hc.X t i j hi hj f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro t i j hi hj f hf
      obtain ⟨io, hio⟩ := (hc.th t i j hi hj f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro t j hj f hf
      obtain ⟨io, hio⟩ := (hc.col t j hj f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro i hi f hf
      obtain ⟨io, hio⟩ := (hc.dn i hi f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro i hi f hf
      obtain ⟨io, hio⟩ := (hc.up i hi f hf).exists_linear
      exact ⟨io, Lift.IsIoUp.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
  · intro hl
    refine { X := ?_, th := ?_, up := ?_, dn := ?_, col := ?_ }
    · intro t i j hi hj f hf F hF
      obtain ⟨io, hio⟩ := hl.X t i j hi hj f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro t i j hi hj f hf F hF
      obtain ⟨io, hio⟩ := hl.th t i j hi hj f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro i hi f hf F hF
      obtain ⟨io, hio⟩ := hl.up i hi f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIoUp.integ hio ⟨F, hF⟩ p v h, Lift.IsIoUp.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro i hi f hf F hF
      obtain ⟨io, hio⟩ := hl.dn i hi f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro t j hj f hf F hF
      obtain ⟨io, hio⟩ := hl.col t j hj f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩

example (G : GridDat R) (h : G.Is) : CuspAlong G.toGridPre := (cuspAlong_iff_hasLifts _).2 h.lifts.hasLifts

end

end GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts

end
