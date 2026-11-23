import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSelfDualFor
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RSGam

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n m : ℕ}

open Classical in

def zc {j : ℕ} (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (hn : m + (j + 1) = n) (π : Representation ℂ (GL (Fin n) k) V)
    (τ : Representation ℂ (GL (Fin m) k) V') (l : Module.Dual ℂ V) (l' : Module.Dual ℂ V') (v : V) (v' : V') (t : ℤ) : ℂ :=
  I (fun g => if ord k (GeneralLinearGroup.det g) = t then
    l (π (emb₂ k (stdSum hn) (g, 1)) v) * l' (τ g v') * (absPow k (-(j : ℂ) / 2) (GeneralLinearGroup.det g) : ℂ) else 0)

open Classical in

def zd [MeasurableSpace k] (μ : Measure k) {j : ℕ} (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (hn : m + (j + 1) = n)
    (π : Representation ℂ (GL (Fin n) k) V) (τ : Representation ℂ (GL (Fin m) k) V') (l : Module.Dual ℂ V)
    (l' : Module.Dual ℂ V') (v : V) (v' : V') (t : ℤ) : ℂ :=
  I (fun g => if ord k (GeneralLinearGroup.det g) = t then
    (∫ x : Fin j → Fin m → k, l (π (tilde (emb₂ k (stdSum hn) (g, 1) * lowUnip hn (padRow x) *
        emb₂ k (stdSum hn) (1, longElt (j + 1) k))) v) ∂(Measure.pi fun _ => Measure.pi fun _ => μ)) *
      l' (τ (tilde g) v') * (absPow k (-(j : ℂ) / 2) (GeneralLinearGroup.det g) : ℂ) else 0)

def HasGammaX (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin n) k) V) (τ : Representation ℂ (GL (Fin m) k) V')
    (γ : RatFunc ℂ) : Prop :=
  ∀ (j : ℕ) (hn : m + (j + 1) = n) [MeasurableSpace k] [BorelSpace k] (μ : Measure k), IsSelfDualFor ψ μ →
    ∀ ω : kˣ →* ℂˣ, HasCentralChar τ ω →
    ∀ (l : Module.Dual ℂ V) (l' : Module.Dual ℂ V'), IsFunctional ψ π l → IsFunctional ψ⁻¹ τ l' →
      ∀ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I → ∀ (v : V) (v' : V'),
        ∃ R R' : RatFunc ℂ, (∀ t, (R : LaurentSeries ℂ).coeff t = zc I hn π τ l l' v v' t) ∧
          (∀ t, (R' : LaurentSeries ℂ).coeff t = zd μ I hn π τ l l' v v' t) ∧
          ∀ᶠ x in Filter.cofinite, R'.eval (RingHom.id ℂ) x⁻¹ =
            (ω (-1) : ℂ) ^ (n - 1) * γ.eval (RingHom.id ℂ) x * R.eval (RingHom.id ℂ) x

def GamIs (ψ : AddChar k Circle) (x y : IrrGL k) (f : ℂ → ℂ) : Prop :=
  ∃ γ : RatFunc ℂ, HasGammaX ψ x.rep y.rep γ ∧ ∀ᶠ z in Filter.cofinite, γ.eval (RingHom.id ℂ) z = f z

end Local

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def NoInv (y : WD h) : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = y ∧
    ∀ v, (∀ σ : Ine (F := E) A, a.ρ (ineIncl h σ) v = v) → v = 0

open Classical in

def lroots (y : WD h) : Multiset ℂ :=
  if hy : ∃ (c : Multiset ℂ) (y' : WD h), (0 : ℂ) ∉ c ∧ y = (WD.lpUnr h c).lpSum y' ∧ NoInv y' then hy.choose else 0

def gamGal (e : WD h → ℂˣ) (y : WD h) (x : ℂ) : ℂ :=
  (e (y.lpTwist (unrChar h (WD.unitOf x)⁻¹) (isSmooth_unrChar h _)) : ℂ) *
    ((lroots y).map fun c => 1 - c⁻¹ * x * ((normV w : ℕ) : ℂ) ^ (-(1 / 2 : ℂ))).prod /
    ((lroots y).map fun c => 1 - c * x⁻¹ * ((normV w : ℕ) : ℂ) ^ (-(1 / 2 : ℂ))).prod

end Galois

end GlobalTheory.RSGam

end
