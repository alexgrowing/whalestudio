import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws

noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsBlockVec {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (χ : kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W) : Prop :=
  ∀ h ∈ KO k (Fin (r + t)),
    (∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1) →
    (∀ i j : Fin r, valuation k (h.val (Fin.castAdd t i) (Fin.castAdd t j) - if i = j then 1 else 0) < 1) →
    ∀ u : kˣ, (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det → π h v = (χ u : ℂ) • v

variable (k) in

def BlockSplit : Prop := ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), IsSmoothChar χ → IsTame χ →
  v ≠ 0 → IsBlockVec χ π.π v →
  (∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSpherical π₂.π ∧
    Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin t) χ))))) ∨
  ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) ∧
    t < Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))}

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def RecSupp (rc : ∀ n, Irr k n → WD h) : Prop :=
  ∀ (n s : ℕ) (π : Irr k n) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) →
    ∀ g : Weil h, (rc n π).charPol g = ∏ a, (rc (d a) (σ a)).charPol g

def RecUnit (rc : ∀ n, Irr k n → WD h) : Prop :=
  ∀ (χ : kˣ →* ℂˣ) (c : Irr k 1), IsUnitaryChar χ → Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    ∀ g : Weil h, ∀ α ∈ (rc 1 c).eig g, ‖α‖ = 1

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  {T : WDTie N A} (S : Reading T)

def SuppLaws : Prop := ∀ i w hw, RecSupp (S i w hw).rc

def TypeBlock (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w) : Prop :=
  IsTame (S i w hw).mu ∧ ∀ P, ∃ v, v ≠ 0 ∧ IsBlockVec (S i w hw).mu ((S i w hw).rep P).π v

def BlockSplitAll (E : Type) [Field E] [NumberField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), BlockSplit (w.adicCompletion E)

variable (N A)

def MuInt : Prop := ∀ (i : N.Loc) (τ : H.E →+* ℂ), ∀ z ∈ A.infG (A.muC i) τ, ∃ m : ℤ, z = (m : ℂ)

def ChiIne : Prop := ∀ (i : N.Loc) (w : PlE H), w ∉ placesOver H.E (N.l i) →
  ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))

def XiOverO : Prop := ∀ i : N.Loc, ∃ ξ : G H.E N.Om →* (N.O i)ˣ, Continuous (fun g => ((ξ g : (N.O i)ˣ) : N.O i)) ∧
  ∀ w : PlE H, w ∉ placesOver H.E (N.l i) → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), ξ σ = 1) ∧
    ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      A.frobEig (A.lpTw (A.locG A.etaTinv w) (-(R.t : ℝ) / 2)) = {iotaO N A i ((ξ σ : (N.O i)ˣ) : N.O i)}

def RowPoint : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
  ∃ i' : N.Loc, N.j i' = N.j i ∧ N.l i' = N.l i ∧ (∀ w, IsSplitPl H w → A.locW i' σ w = A.locW i σ w) ∧
    (∃ φ : N.O i' ≃+* N.O i, Continuous φ ∧ ∀ z, iotaO N A i (φ z) = iotaO N A i' z) ∧
    ∃ (P : A.AV i') (x : N.X i'), thetaOf N A i' σ P ∧ A.ptV i' P = some x

end GlobalTheory.SplitRead
