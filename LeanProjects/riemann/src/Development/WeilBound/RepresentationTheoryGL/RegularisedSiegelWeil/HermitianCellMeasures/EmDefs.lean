import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.Em

structure Rich {X : Type} [TopologicalSpace X] (A : Submodule ℂ (X → ℂ)) : Prop where
  cc : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f
  mul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A
  star : ∀ f ∈ A, star f ∈ A
  sep : ∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y
  bump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1

def Dens : Prop := ∀ (X N : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace N] (σ : Measure X) (lam : Measure N) [SFinite lam]
  (k : N → X → ℂ) (A : Submodule ℂ (X → ℂ)) (Z Y : Set X) (g : ℕ → N → ℂ) (G : ℕ → X → ℝ),
  IsFiniteMeasureOnCompacts σ → Measurable (Function.uncurry k) → (∀ x z, ‖k x z‖ ≤ 1) → Rich A → IsClosed Z → IsClosed Y →
  σ Yᶜ = 0 → (∀ j, Integrable (g j) lam ∧ (∀ x, ‖g j x‖ ≤ 1) ∧ ∀ z ∈ Y, 0 ≤ G j z ∧ ∫ x, g j x * k x z ∂lam = G j z) →
  (∀ x, Tendsto (g · x) atTop (𝓝 1)) →
  (∀ C : Set X, IsCompact C → C ⊆ Y → Disjoint C Z → ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ z ∈ C, G j z ≤ ε) →
  (∀ f ∈ A, Integrable (fun x => ∫ z, f z * k x z ∂σ) lam) →
  ∃ ν : Measure X, IsFiniteMeasureOnCompacts ν ∧ ν (Y ∩ Z)ᶜ = 0 ∧
    (∀ f f₀ : X → ℂ, Continuous f → Continuous f₀ → (∀ z, 0 ≤ (f₀ z).re ∧ (f₀ z).im = 0) → Integrable f σ → Integrable f₀ σ →
      Integrable (fun x => ∫ z, f z * k x z ∂σ) lam → Integrable (fun x => ∫ z, f₀ z * k x z ∂σ) lam →
      (∀ ε : ℝ, 0 < ε → ∃ f₁ : X → ℂ, Continuous f₁ ∧ HasCompactSupport f₁ ∧ ∀ z, ‖f z - f₁ z‖ ≤ ε * (f₀ z).re) →
      ∫ x, ∫ z, f z * k x z ∂σ ∂lam = ∫ z, f z ∂ν) ∧
    ∀ (Θ : X ≃ₜ X) (κ : ℝ≥0), (∀ f ∈ A, f ∘ Θ ∈ A ∧
      ∫ x, ∫ z, f (Θ z) * k x z ∂σ ∂lam = κ * ∫ x, ∫ z, f z * k x z ∂σ ∂lam) → ν.map Θ = κ • ν

variable {D : D7} {a r t n : ℕ}

abbrev XS (D : D7) (a r t : ℕ) (e : AE D) : Type := {z : Mx D a r × Mx D a t // e • z.1 = z.1 ∧ e • z.2 = z.2}

def toX {e : AE D} (he : e * e = e) (z : Mx D a r × Mx D a t) : XS D a r t e :=
  ⟨(e • z.1, e • z.2), by simp [smul_smul, he], by simp [smul_smul, he]⟩

def sig (S : Finset (Pl D)) {e : AE D} (he : e * e = e) (μ : Measure (Mx D a r × Mx D a t)) : Measure (XS D a r t e) :=
  (μ.restrict {z | IntOff S z.1 ∧ IntOff S z.2}).map (toX he)

def algA (θ : InfFam D) (hn : r + t = n) (S : Finset (Pl D)) (e : AE D) : Submodule ℂ (XS D a r t e → ℂ) :=
  Submodule.span ℂ {f | ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ f = fun z => Φ (jn hn z.1.1 z.1.2)}

def TopX : Prop := ∀ (D : D7) (a r t : ℕ) (e : AE D), T2Space (XS D a r t e) ∧ LocallyCompactSpace (XS D a r t e) ∧
  SecondCountableTopology (XS D a r t e) ∧ BorelSpace (XS D a r t e) ∧ BorelSpace (Mx D a r × Mx D a t) ∧
  MeasurableEmbedding (Subtype.val : XS D a r t e → _) ∧ BorelSpace (hermS D t e) ∧ SecondCountableTopology (hermS D t e) ∧
  LocallyCompactSpace (hermS D t e)

def AlgRich : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (a r t n : ℕ) (hn : r + t = n) (S : Finset (Pl D)) e, IsIdem S e →
  Rich (algA (a := a) θ hn S e) ∧ ∀ f ∈ algA (a := a) θ hn S e,
    ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ f = fun z => Φ (jn hn z.1.1 z.1.2)

def AlgStab : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (a n : ℕ) (S : Finset (Pl D)) e, IsIdem S e →
  ∀ (h : GL (Fin a) (AE D)) (g : GL (Fin n) (AE D)), e • (h.1 - 1) = h.1 - 1 → e • (g.1 - 1) = g.1 - 1 →
  ∀ Φ ∈ schwartzA θ a n, Good S e Φ → HasCompactSupport Φ →
    (fun X => Φ (mm (mm h.1 X) g.1)) ∈ schwartzA θ a n ∧ Good S e (fun X => Φ (mm (mm h.1 X) g.1)) ∧
      HasCompactSupport fun X : Mx D a n => Φ (mm (mm h.1 X) g.1)

def SigLaw : Prop := ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r) (S : Finset (Pl D)) (e : AE D), IsIdem S e →
  ∀ (he : e * e = e) (fib : Measure (Mx D V.rank r)) (μt : Measure (Mx D V.rank t)), IsFiniteMeasureOnCompacts fib →
  fib {x | ip V x x ≠ rat b₀.1} = 0 → (∀ h : GA D V, fib.map (fun x => mm (mt V h) x) = fib) → μt.IsAddHaarMeasure →
  IsFiniteMeasureOnCompacts (sig S he (fib.prod μt)) ∧
  sig S he (fib.prod μt) {z | ip V z.1.1 z.1.1 = e • rat b₀.1}ᶜ = 0 ∧
  (∀ Ξ : Mx D V.rank r × Mx D V.rank t → ℂ, Continuous Ξ →
    (∀ z, (IntOff S z.1 ∧ IntOff S z.2 → Ξ z = Ξ (e • z.1, e • z.2)) ∧ (¬ (IntOff S z.1 ∧ IntOff S z.2) → Ξ z = 0)) →
    (Integrable Ξ (fib.prod μt) → Integrable (fun z : XS D V.rank r t e => Ξ z.1) (sig S he (fib.prod μt))) ∧
    ∫ z, Ξ z ∂(fib.prod μt) = ∫ z, Ξ z.1 ∂(sig S he (fib.prod μt))) ∧
  (∀ (h : GA D V), e • (mt V h - 1) = mt V h - 1 → ∀ Θ : XS D V.rank r t e ≃ₜ XS D V.rank r t e,
    (∀ z, (Θ z).1 = (mm (mt V h) z.1.1, mm (mt V h) z.1.2)) → (sig S he (fib.prod μt)).map Θ = sig S he (fib.prod μt)) ∧
  (∀ y : Mx D r t, e • y = y → ∀ Θ : XS D V.rank r t e ≃ₜ XS D V.rank r t e,
    (∀ z, (Θ z).1 = (z.1.1, z.1.2 + mm z.1.1 y)) → (sig S he (fib.prod μt)).map Θ = sig S he (fib.prod μt)) ∧
  ∀ g : GL (Fin t) (AE D), e • (g.1 - 1) = g.1 - 1 → ∀ Θ : XS D V.rank r t e ≃ₜ XS D V.rank r t e,
    (∀ z, (Θ z).1 = (z.1.1, mm z.1.2 g.1)) → (sig S he (fib.prod μt)).map Θ =
      ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ V.rank : ℝ≥0) • sig S he (fib.prod μt)

def HermScale : Prop := ∀ (D : D7) (t : ℕ) (S : Finset (Pl D)) (e : AE D), IsIdem S e →
  ∀ lam : Measure (hermS D t e), lam.IsAddHaarMeasure → ∀ g : GL (Fin t) (AE D), e • (g.1 - 1) = g.1 - 1 →
  ∃ c : hermS D t e ≃ₜ+ hermS D t e, (∀ x, (c x).1.1 = mm (mm g.1 x.1.1) (adj g.1)) ∧
    lam.map c = ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ t : ℝ≥0) • lam

def OrbEx : Prop := ∀ (D : D7) (n r t : ℕ) (hn : r + t = n) (V : HSp D), V.rank = r + 2 * t → ∀ ψ, IsCharAF D.host.F ψ →
  ∀ θ : InfFam D, IsInfFam θ → ∀ (b₀ : HermE D r), b₀.1.det ≠ 0 → ∀ (S : Finset (Pl D)) (e : AE D), IsIdem S e →
  ∀ (he : e * e = e) (fib : Measure (Mx D V.rank r)) (μt : Measure (Mx D V.rank t)), IsFiniteMeasureOnCompacts fib →
  fib {x | ip V x x ≠ rat b₀.1} = 0 → (∀ h : GA D V, fib.map (fun x => mm (mt V h) x) = fib) → μt.IsAddHaarMeasure →
  ∀ lam : Measure (hermS D t e), lam.IsAddHaarMeasure →
  (∀ f ∈ algA (a := V.rank) θ hn S e,
    Integrable (fun x : hermS D t e => ∫ z, f z * pch ψ x.1.1 (qv V b₀ z.1) ∂(sig S he (fib.prod μt))) lam) →
  ∃ ν : Measure (XS D V.rank r t e), IsOrb V b₀ e (ν.map Subtype.val) ∧
    ∀ f f₀ : XS D V.rank r t e → ℂ, Continuous f → Continuous f₀ → (∀ z, 0 ≤ (f₀ z).re ∧ (f₀ z).im = 0) →
      Integrable f (sig S he (fib.prod μt)) → Integrable f₀ (sig S he (fib.prod μt)) →
      Integrable (fun x : hermS D t e => ∫ z, f z * pch ψ x.1.1 (qv V b₀ z.1) ∂(sig S he (fib.prod μt))) lam →
      Integrable (fun x : hermS D t e => ∫ z, f₀ z * pch ψ x.1.1 (qv V b₀ z.1) ∂(sig S he (fib.prod μt))) lam →
      (∀ ε : ℝ, 0 < ε → ∃ f₁, Continuous f₁ ∧ HasCompactSupport f₁ ∧ ∀ z, ‖f z - f₁ z‖ ≤ ε * (f₀ z).re) →
      ∫ x : hermS D t e, ∫ z, f z * pch ψ x.1.1 (qv V b₀ z.1) ∂(sig S he (fib.prod μt)) ∂lam = ∫ z, f z ∂ν

end PositivityTheory.Rg.Rsw.Em

end
