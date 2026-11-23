import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

def trSp (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (e : AE D) (M : ℕ) (O : Subring ℂ) :
    Submodule O (WO V W → ℂ) :=
  Submodule.span O {f | ∃ y : WO V W, IsHalf e y ∧ M • y ∈ latO V W ΛV ΛW (fun _ => True) ∧ f = heisO ψ V W y f₀}

abbrev stdF (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D)
    (sW BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) :
    MvPolynomial (FVar D W.rank V.rank) ℂ →ₗ[ℂ] (WO V W → ℂ) :=
  pureTensorO ψ θ V W (fun _ => 1) sW (fun _ => 1) BW f

def OneAt (V : HSp D) (l : ℕ) (h : GA D V) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
    ∀ a b, algebraMap (AF D.host.F) (AE D) ε * (Formalism.L2.Theta.mt V h - 1) a b = 0

def ChiData (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) : Prop :=
  ChrEq χW χ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((b : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q) ∧
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1

def ValRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ) : Prop :=
  ∀ x : k, la.valuation k x ≤ 1 → σ x ∈ O

def locRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) : Subring ℂ :=
  (la.valuation k).integer.map σ

theorem valRing_locRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) :
    ValRing σ la (locRing σ la) := fun x hx => ⟨x, hx, rfl⟩

theorem valRing_range {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) :
    ValRing σ la σ.range := fun x _ => ⟨x, rfl⟩

def ConjIn (D : D7) {k : Type} [Field k] (σ : k →+* ℂ) : Prop := ∀ (τ : D.host.E →+* ℂ) (a : D.host.E), ∃ x, σ x = τ a

def DenomAt {E : Type} [Field E] {n : ℕ} (l c : ℕ) (γ : GL (Fin n) E) : Prop :=
  ∃ m : ℕ, Nat.Coprime m l ∧ ∀ a b, IsIntegral ℤ (((m * l ^ c : ℕ) : E) * γ.val a b) ∧
    IsIntegral ℤ (((m * l ^ c : ℕ) : E) * γ⁻¹.val a b)

theorem oneAt_one (V : HSp D) (l : ℕ) : OneAt V l 1 := fun _ _ _ _ a b => by
  have h1 : Formalism.L2.Theta.mt V 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  rw [h1, sub_self]
  simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)
  (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i)

def BaseCc (ph : ℂ) : Prop :=
  CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) T.σ₀) (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀))
    (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i)
    fun k => ph * T.cE ((i : ℕ) + 1) T.σ₀ k

def CovCc (ph : ℂ) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂)
    (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i)
    fun k => ph * C.cc₂ k

end GlobalTheory.LevelSeries

end
