import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapAbsOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.Rs

def Dict : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ),
  (∀ r t, aT E N r t = An.aR E N r t) ∧ (∀ t, splitCentre E N t = An.tor E fun _ => t) ∧ latticeGL E N = An.lat E N ∧
  ∀ (φ : Sm E N), IsAutForm φ → ∀ r, 0 < r → r < N → IsCT r φ.1 (An.ctn r φ.1) ∧
    ∀ F, IsCT r φ.1 F → ∃ c : ℂ, c ≠ 0 ∧ F = fun g => c * An.ctn r φ.1 g

def NiceAut : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (φ : Sm E N), IsAutForm φ →
  (∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g) → An.Nice φ.1

def InitBnd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (φ : Sm E N), IsAutForm φ →
  (∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g) → ∃ M : ℝ, An.Bnd φ.1 fun _ => M

def FinTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (φ : Sm E N), IsAutForm φ →
  ∀ r, 0 < r → r < N → ∀ F, IsCT r φ.1 F →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t : ℝ => fun g => F (aT E N r t * g)))

def KillPoly : Prop := ∀ (G : Type) [Group G] (a : ℝ → G) (F₀ : G → ℂ), (∀ s t, a (s + t) = a s * a t) →
  (∀ g, Continuous fun t => F₀ (a t * g)) →
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t : ℝ => fun g => F₀ (a t * g))) →
  ∃ p : ℂ[X], p.Monic ∧ (∀ g, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F₀ (a j * g) = 0) ∧
    ∀ z, p.IsRoot z → ∃ c : ℂ, z = Complex.exp c ∧
      ∃ F ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => F₀ (a t * g)), F ≠ 0 ∧
        ∀ (t : ℝ) g, F (a t * g) = Complex.exp (c * t) * F g

def LatOf : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
  (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (n + 1)) (w.adicCompletion E)) V)
  (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (x : V) (S : Multiset ℂˣ), (∀ x y, B y x = starRingEnd ℂ (B x y)) →
  (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ g x y, B (ρ g x) (ρ g y) = B x y) → GlobalTheory.LFun.IsSatVecGL w ρ x S →
  ∃ (k : Type) (_ : Field k) (_ : Fintype k) (Γ : Type) (_ : Group Γ) (red : Γ →* GL (Fin (n + 1)) k)
    (ρ' : Γ →* Module.End ℂ V) (t : Module.End ℂ V) (v : Submodule k (Fin (n + 1) → k) → V),
    Fintype.card k = Ideal.absNorm w.asIdeal ∧ LatData k n B red ρ' t v ∧ LatEig k n v (S.map fun b : ℂˣ => (b : ℂ))

def SqIntGlue : Prop := Dict → NiceAut → InitBnd → FinTr → KillPoly → An.Boot → An.SlabInt → SqIntCrit
def ExpNegGlue : Prop := Dict → An.L2ConstantTermDecay → ExpNeg
def GapGlue : Prop := LatOf → GapAbs → Gap

end PositivityTheory.Rg.Rs

end
