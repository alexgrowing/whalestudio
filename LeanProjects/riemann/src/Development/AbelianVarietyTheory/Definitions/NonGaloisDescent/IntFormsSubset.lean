import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverRead

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

variable {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ)

structure Cover : Type 1 where

  c' : Coeff T.Q.l
  hle : T.Q.c.F ≤ c'.F

  d : DeltaDat (T.Q.Xo j) c' 0

  σ₂ : d.c₂.F →+* ℂ
  U₂ : Unf d.Xo₂ d.c₂ σ₂ D.R.r
  dict₂ : GA D (T.V j σ) → Σ k, Frame (U₂.X k).Ψ D.R.r
  cc₂ : U₂.Comp → ℂ

variable {T j σ}

namespace Cover

variable (C : Cover T j σ)

def inc : T.Q.c.F →+* C.d.c₂.F := (C.d.eF : C.c'.F →+* C.d.c₂.F).comp (incF T.Q.c C.c' C.hle)

def rd (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f₂ : Rul C.d.Xo₂ C.d.c₂) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂) (rdU C.U₂ f₂)

def IsPull (f : T.R j) (f₂ : Rul C.d.Xo₂ C.d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [Algebra T.Q.c.F k] [Algebra C.c'.F k] [Algebra C.d.c₂.F k] (h : AlgOver T.Q.c C.c' C.hle k),
    (∀ x : C.c'.F, algebraMap C.d.c₂.F k (C.d.eF x) = algebraMap C.c'.F k x) →
    ∀ (y₂ : FrPt C.d.Xo₂ C.d.c₂ k) (y : FrPt (T.Q.Xo j) C.c' k), FrOver C.d y₂ y →
      evR C.d.Xo₂ C.d.c₂ f₂ y₂ = evR (T.Q.Xo j) T.Q.c f (y.res C.hle h)

def IsUnif : Prop :=
  C.d.IsLev ∧ C.d.l₂.A = 1 ∧ C.σ₂.comp C.inc = σ ∧ IsUnf C.U₂ ∧
    (∀ h, (C.dict₂ h).2 ∈ (C.U₂.X (C.dict₂ h).1).dom) ∧
    ∃ (hr : (T.V j σ).rank = D.R.r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
      (F : FamilyUnif C.d.Xo₂ (C.σ₂.comp (IntermediateField.inclusion C.d.c₂.le).toRingHom)
        (fun i => relab C.d.c₂ C.σ₂ (e i).1))
      (ik : C.U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (C.U₂.X k).Λ)
      (th : ∀ k, (C.U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k, ModelW (T.V j σ) hr (C.U₂.X k)) ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
        DictLat C.U₂ (T.V j σ) hr C.dict₂ (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) e F ik φ th
          (T.x₀ j σ)

def IsPinned (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  CUnit C.cc₂ ∧ ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → C.rd a f₂ = T.phiJ j σ a f

def cuspSec (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul C.d.Xo₂ C.d.c₂) :=
  {f₂ | f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n ∧ rdU C.U₂ f₂ ∈ holSub0 C.U₂.X (laU C.U₂ a n)}

def ratForms (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (GA D (T.V j σ) → ℂ) := C.rd a '' C.cuspSec a n

def intForms (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) :
    Set (GA D (T.V j σ) → ℂ) :=
  C.rd a '' {f₂ | f₂ ∈ C.cuspSec a n ∧ ∀ la ∈ S, ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v f₂}

theorem intForms_subset (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) :
    C.intForms a n S ⊆ C.ratForms a n := Set.image_mono fun _ h => h.1

end Cover

variable (T j σ)

def baseForms (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (GA D (T.V j σ) → ℂ) :=
  T.phiJ j σ a '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}

def baseInt (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) :
    Set (GA D (T.V j σ) → ℂ) :=
  T.phiJ j σ a '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n) ∧
    ∀ la ∈ S, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, 0 ≤ v f}

end GlobalTheory.CoverRead
