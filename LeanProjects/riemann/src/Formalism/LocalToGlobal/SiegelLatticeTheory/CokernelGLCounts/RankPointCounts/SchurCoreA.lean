import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KappaOffDiagonal

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SchurCoreA : Prop :=
  ∀ (k : ℕ) (ι : Type) [Fintype ι] (V V' : ι → Type)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    [∀ i, NormedAddCommGroup (V' i)] [∀ i, InnerProductSpace ℂ (V' i)] [∀ i, FiniteDimensional ℂ (V' i)]
    (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W']
    (tens : (∀ i, V i) → W) (tens' : (∀ i, V' i) → W'),
    (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ →
    (∀ x y, ⟪tens' x, tens' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) → Submodule.span ℂ (Set.range tens') = ⊤ →
    ∀ (π : ∀ i, Matrix (Fin k) (Fin k) ℂ → (V i →L[ℂ] V i)) (π' : ∀ i, Matrix (Fin k) (Fin k) ℂ → (V' i →L[ℂ] V' i))
      (lam lam' : ι → Fin k → ℝ),
    (∀ i, IsHCTypeU k (lam i) (π i)) → (∀ i, IsHCTypeU k (lam' i) (π' i)) →
    ∀ i₀ : ι, lam i₀ ≠ lam' i₀ →
    ∀ (C : ι → Matrix (Fin k) (Fin k) ℂ), (∀ i, C i ∈ UJset (allPos k)) →
    ∀ P : W' →L[ℂ] W,
      (∀ M : ι → Matrix (Fin k) (Fin k) ℂ, (∀ i, M i ∈ UJset (allPos k)) →
        ∃ (A : W →L[ℂ] W) (B : W' →L[ℂ] W'),
          (∀ x, A (tens x) = tens (fun i => π i (M i) (x i))) ∧
          (∀ x, B (tens' x) = tens' (fun i => π' i (C i * M i * (C i)ᴴ) (x i))) ∧
          A.comp P = P.comp B) →
      P = 0

def LeviTens : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∀ h ∈ X.SinfU u, ∀ x : ∀ v, X.Vloc u v,
    X.piU u h (X.tensU u x) = X.tensU u (fun v => X.piLoc u v (matW X.B.I (X.wfr u v) v h) (x v))

def WfrSpan : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → ℂ),
    (∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) y = 0 ∧ hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) y = 0) →
    hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) y = 0 →
    y = ∑ b, hJ (X.B.I.ε v) (X.wfr u v b) y • X.wfr u v b

def CplxKer : Prop :=
  ∀ (E : Type) [Field E] (φ : E →+* ℂ) (m N : ℕ) (A : Matrix (Fin m) (Fin N) E) (c : Fin N → ℂ),
    A.map φ *ᵥ c = 0 → c ∈ Submodule.span ℂ ((fun s : Fin N → E => fun i => φ (s i)) '' {s | A *ᵥ s = 0})

variable {D : D7} in

def spanAt (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (U : Submodule D.host.E (VS D).V) :
    Submodule ℂ (Fin X.B.I.n → ℂ) :=
  Submodule.span ℂ ((fun p => rv X.B.I v (X.crd p)) '' (U : Set (VS D).V))

def CplxNF : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
    ∀ v : InfinitePlace X.B.I.F,
      (∀ y : Fin X.B.I.n → ℂ, (∀ p ∈ (lf D (X.Fu u)).fl.Xplus, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) y = 0) →
        ∃ x ∈ spanAt X v (lf D (X.Fu u)).fl.X,
          ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (y - x) = 0) ∧
      (∀ y : Fin X.B.I.n → ℂ, (∀ p ∈ (frq X q).fl.Xplus, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) y = 0) →
        ∃ x ∈ spanAt X v (frq X q).fl.X,
          ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (y - x) = 0) ∧
      (∀ y ∈ spanAt X v (lf D (X.Fu u)).fl.X, (∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) y = 0) →
        y ∈ spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl))

def GeomB : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
    ∃ C : InfinitePlace X.B.I.F → Matrix (Fin D.R.k) (Fin D.R.k) ℂ, (∀ v, C v ∈ UJset (allPos D.R.k)) ∧
      ∀ M : InfinitePlace X.B.I.F → Matrix (Fin D.R.k) (Fin D.R.k) ℂ, (∀ v, M v ∈ UJset (allPos D.R.k)) →
        ∃ h ∈ pointwiseStabilizerInfinite X q,
          (∀ x, X.piU u h (X.tensU u x) = X.tensU u (fun v => X.piLoc u v (M v) (x v))) ∧
          (∀ x, X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1) (X.tensU u' x) =
            X.tensU u' (fun v => X.piLoc u' v (C v * M v * (C v)ᴴ) (x v)))

end PI.SchurPlaces
