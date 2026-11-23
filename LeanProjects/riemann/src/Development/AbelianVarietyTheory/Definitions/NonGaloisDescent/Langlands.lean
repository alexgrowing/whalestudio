import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def segSum (rc : IrrGL (w.adicCompletion E) → WD h) (l : List (Segment (w.adicCompletion E))) : WD h :=
  sumList (l.map fun Δ => ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len))

structure LawsMin (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h) : Prop where

  bij : Function.Bijective rc

  dim : ∀ x, (rc x).lpDim = x.1

  one : ∀ χ hχ, rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)

  eps : ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
    ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) (w.adicCompletion E))) (τ : IrrRep (GL (Fin m) (w.adicCompletion E))),
      IsCuspidal π.ρ → HasPairEps ψ π.ρ τ.ρ (e ψ ((rc (cls π)).lpChar (rc (cls τ))))

  cusp : ∀ x, x.IsCusp ↔ IsIrrWD (rc x)

  langlands : ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep → rc x = segSum rc l

structure LawsLit (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h) : Prop
    extends LawsMin a ha e rc where

  twist : ∀ x χ hχ, rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))

  central : ∀ (x : IrrGL (w.adicCompletion E)) ω, HasCentralChar x.rep ω →
    ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ)

  dual : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Nonempty (π'.ρ.Equiv (contra π.ρ)) →
    rc (cls π') = (rc (cls π)).lpDual

variable (h) in

def IsRecLit (rc : IrrGL (w.adicCompletion E) → WD h) : Prop :=
  ∃ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A),
    IsDeligneEps ε ∧ LawsLit a ha (ε E w h) rc

theorem Laws.toLit {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
    {rc : IrrGL (w.adicCompletion E) → WD h} (H : Laws a ha ε rc) : LawsLit a ha (ε E w h) rc :=
  { bij := H.bij, dim := H.dim, one := H.one, eps := H.eps, cusp := H.cusp, langlands := H.langlands,
    twist := H.twist, central := H.central, dual := H.dual }

theorem IsRec.toLit {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) : IsRecLit h rc :=
  let ⟨a, ha, ε, hε, H⟩ := H; ⟨a, ha, ε, hε, H.toLit⟩

section Transport

def RepRel {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k')
    (x : IrrGL k) (x' : IrrGL k') : Prop :=
  ∃ (n : ℕ) (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k')) (e : π.V ≃ₗ[ℂ] π'.V),
    x = cls π ∧ x' = cls π' ∧ ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)

variable {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

def WeilRel (φ : Ω ≃+* Ω') (σ : Weil h) (σ' : Weil h') : Prop :=
  ∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)

def WDRel (φ : Ω ≃+* Ω') (y : WD h) (y' : WD h') : Prop :=
  ∃ (n : ℕ) (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = y ∧ WD.mk b' = y' ∧
    b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), WeilRel φ σ σ' → b.ρ σ = b'.ρ σ'

variable (A A' w w') in

structure PlaceIso (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E') : Prop where

  mem : ∀ z, φ z ∈ A' ↔ z ∈ A

  ext : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)

  cont : Continuous i

  loc : ∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)

end Transport

theorem PlaceIso.refl : PlaceIso A w A w (RingEquiv.refl Ω) (RingHom.id E) (RingEquiv.refl _) :=
  ⟨fun _ => Iff.rfl, fun _ => rfl, continuous_id, fun _ => rfl⟩

end GlobalTheory.LocLanglands

end
