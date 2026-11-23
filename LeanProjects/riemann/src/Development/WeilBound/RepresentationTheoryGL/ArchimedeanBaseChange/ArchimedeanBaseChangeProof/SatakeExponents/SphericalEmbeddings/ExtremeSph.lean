import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.BaseChangeIsobaricOf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
open GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.N3

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

abbrev iP (ξ : Fin n → ℂˣ) := prinSeries (k := k) (n := Fin n) fun i => unrChar k (ξ i)

def IsExpN {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ξ : Fin n → ℂˣ) : Prop :=
  ∃ ℓ : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
    ∀ t v, ℓ (jacB π t v) = (torusChar (fun i => unrChar k (ξ i)) t : ℂ) * ℓ v

def Mono (ξ : Fin n → ℂˣ) : Prop := ∀ i j : Fin n, i ≤ j → ‖(ξ j : ℂ)‖ ≤ ‖(ξ i : ℂ)‖

variable (k)

def ExpEmb : Prop := ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
  (ξ : Fin n → ℂˣ), IsSmooth π → IsExpN π ξ →
  ∃ f : π.IntertwiningMap (iP (k := k) ξ), f ≠ 0

def SphEmb : Prop := ∀ (n : ℕ) (ξ : Fin n → ℂˣ), Mono ξ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → IsSpherical π →
  IsSubquotient π (iP (k := k) ξ) → ∃ f : π.IntertwiningMap (iP (k := k) ξ), Function.Injective f

def UniqSub : Prop := CharZero k → ∀ (n : ℕ) (ξ : Fin n → ℂˣ), Mono ξ → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) V) (σ : Representation ℂ (GL (Fin n) k) W),
  π.IsIrreducible → σ.IsIrreducible → ∀ (f : π.IntertwiningMap (iP (k := k) ξ)) (g : σ.IntertwiningMap (iP (k := k) ξ)),
    f ≠ 0 → g ≠ 0 → Nonempty (π.Equiv σ)

def SphConst : Prop := ∀ (n : ℕ) (ξ : Fin n → ℂˣ), ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
  (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π ∧ π.IsIrreducible ∧ IsSpherical π ∧ IsSubquotient π (iP (k := k) ξ)

def ExtremeSph : Prop := CharZero k → ∀ (n : ℕ) (ξ : Fin n → ℂˣ), Mono ξ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
  (∃ f : π.IntertwiningMap (iP (k := k) ξ), f ≠ 0) → IsSpherical π

end Local

section Global

variable {E : Type} [Field E] [NumberField E] {c n : ℕ} {N : Fin c → ℕ}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def N3 : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c n : ℕ) (N : Fin c → ℕ)
  (h : ∑ i, N i = n) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (P : SmIrr (GL (Fin n) (w.adicCompletion E)))
  (ξ : Fin n → ℂˣ), IsSubquotient P.ρ (locProd h w σ) → IsExpN P.ρ ξ → Mono ξ →
  (∀ i, GlobalTheory.LGrp.IsSpherical (σ i).ρ (GlobalTheory.LFun.KGL w (N i))) ∧
    ∃ b : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (σ i).ρ (b i)) ∧ ∑ i, b i = Finset.univ.val.map ξ

def SatLink : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c n : ℕ) (N : Fin c → ℕ)
  (h : ∑ i, N i = n) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (P : SmIrr (GL (Fin n) (w.adicCompletion E)))
  (ξ : Fin n → ℂˣ), IsSubquotient P.ρ (locProd h w σ) → IsSpherical P.ρ →
  (∃ f : P.ρ.IntertwiningMap (iP (k := w.adicCompletion E) ξ), f ≠ 0) →
  (∀ i, GlobalTheory.LGrp.IsSpherical (σ i).ρ (GlobalTheory.LFun.KGL w (N i))) ∧
    ∃ b : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (σ i).ρ (b i)) ∧ ∑ i, b i = Finset.univ.val.map ξ

end Global

end PositivityTheory.Rg.BcB.N3

end
