import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.SgMemUnipB

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Automorphic (GLnLocal.integralGL)
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.V.Published UpperTheory.CBC
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G
open scoped Classical

namespace UpperTheory.Gal.Join

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def Dom (t : Fin n → kˣ) : Prop := ∀ i j, i < j → valuation k (t i : k) ≤ valuation k (t j : k)

structure IwLev (K : Subgroup (GL (Fin n) k)) : Prop where
  co : CO K
  fact : ∀ g ∈ K, ∃ u ∈ K ⊓ unipB k (Fin n), ∃ d, diagT k (Fin n) d ∈ K ∧ ∃ c ∈ K ⊓ unipBLower k (Fin n),
    g = u * diagT k (Fin n) d * c
  up : ∀ t, Dom t → ∀ u ∈ K ⊓ unipB k (Fin n), diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ ∈ K
  low : ∀ t, Dom t → ∀ c ∈ K ⊓ unipBLower k (Fin n), (diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t ∈ K

def dcos (K : Subgroup (GL (Fin n) k)) (t : Fin n → kˣ) : Set (GL (Fin n) k) :=
  {g | ∃ a ∈ K, ∃ b ∈ K, g = a * diagT k (Fin n) t * b}

def el (K : Subgroup (GL (Fin n) k)) (t : Fin n → kˣ) : GL (Fin n) k → ℂ := (dcos K t).indicator fun _ => 1

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def imK (π : Representation ℂ (GL (Fin n) k) V) (K : Subgroup (GL (Fin n) k)) : Submodule ℂ (Jacquet π (unipB k (Fin n))) :=
  (fixed π K).map (twKer π (unipB k (Fin n)) 1).mkQ

def IsExp (π : Representation ℂ (GL (Fin n) k) V) (μ : (Fin n → kˣ) →* ℂˣ) : Prop :=
  ∃ y : Jacquet π (unipB k (Fin n)), y ≠ 0 ∧ ∀ t, jacB π t y = (μ t : ℂ) • y

end Local

def trIn {X : Type} [AddCommGroup X] [Module ℂ X] (P : Submodule ℂ X) (T : X →ₗ[ℂ] X) : ℂ :=
  if h : ∀ y ∈ P, T y ∈ P then LinearMap.trace ℂ P (T.restrict h) else 0

structure IsNorm {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (ι : k →+* k') (σ : k' ≃+* k') (l : ℕ)
    (N : k'ˣ →* kˣ) : Prop where
  cyc : Cyc σ l
  prod : ∀ x, ι (N x : k) = ∏ i ∈ Finset.range l, σ^[i] (x : k')
  cont : Continuous N
  abs : ∀ x, GlobalTheory.SplitWeil.nabs k (N x) = GlobalTheory.SplitWeil.nabs k' x

def nT {A B : Type} [CommGroup A] [CommGroup B] (n : ℕ) (N : A →* B) : (Fin n → A) →* (Fin n → B) := N.compLeft (Fin n)

def ForInert (p : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (_ : E ≃ₐ[F] E) (_ : ℕ) (v : Pl F) (w : PlacesOver E v) (_ : w.1.adicCompletion E ≃+* w.1.adicCompletion E)
    (_ : (w.1.adicCompletion E)ˣ →* (v.adicCompletion F)ˣ), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (v : Pl F) (w : PlacesOver E v), ¬ GM.Split E v → ∀ σw N, IsLocGal (n := n) σ w (Loc.sg σw) →
      IsNorm (completionMap v w.1) σw (Module.finrank F E) N → p F E σ n v w σw N

def LocGal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime →
    ∀ (v : Pl F) (w : PlacesOver E v), ¬ GM.Split E v → ∃ σw N, (∀ n, IsLocGal (n := n) σ w (Loc.sg σw)) ∧
      IsNorm (completionMap v w.1) σw (Module.finrank F E) N ∧
      ∀ x, (N x : v.adicCompletion F) = (letI := (completionMap v w.1).toAlgebra; Algebra.norm (v.adicCompletion F) (x : w.1.adicCompletion E))

def ElemPairJ : Prop := ForInert fun _ E _ _ _ _ _ _ _ σ n v w σw N =>
  ∀ (U' : Subgroup (Gw n w.1)) (U : Subgroup (Gw n v)), IsOpen (U' : Set (Gw n w.1)) → IsOpen (U : Set (Gw n v)) →
    ∃ K' ≤ U', ∃ K ≤ U, IwLev K' ∧ IwLev K ∧ (∀ g, Loc.sg σw g ∈ K' ↔ g ∈ K') ∧ ∃ (c : ℂ) (t₀ : Fin n → (w.1.adicCompletion E)ˣ),
      c ≠ 0 ∧ Strict t₀ ∧ ∀ t, Dom t → GM.MatchAt σ v c (fun g => el K' (t₀ * t) (GM.cmp w g)) (el K (nT n N (t₀ * t))) ∧
        dcos K (nT n N (t₀ * t)) ⊆ normSet E n v

def ForLift (p : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F)
    (w : PlacesOver E v) (_ : w.1.adicCompletion E ≃+* w.1.adicCompletion E)
    (_ : (w.1.adicCompletion E)ˣ →* (v.adicCompletion F)ˣ) (_ : SmIrr (Gw n v)) (_ : SmIrr (Gw n w.1)), Prop) : Prop :=
  ForInert fun F E _ _ _ _ _ _ _ _ n v w σw N =>
    ∀ (π : CuspSub F n) (P : CuspSub E n), (∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv) →
      WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ τ τ', (Cusp.cx π).locComp v τ → (Cusp.cx P).locComp w.1 τ' → p F E n v w σw N τ τ'

def CoreId : Prop := ForLift fun _ E _ _ _ _ _ n v w σw N τ τ' =>
  ∃ (A : τ'.V →ₗ[ℂ] τ'.V) (hA : Semi σw τ'.ρ A), A ≠ 0 ∧
    ∀ (U' : Subgroup (Gw n w.1)) (U : Subgroup (Gw n v)), IsOpen (U' : Set (Gw n w.1)) → IsOpen (U : Set (Gw n v)) →
      ∃ K' ≤ U', ∃ K ≤ U, IwLev K' ∧ IwLev K ∧ (∀ g, Loc.sg σw g ∈ K' ↔ g ∈ K') ∧ ∃ (c : ℂ) (t₀ : Fin n → (w.1.adicCompletion E)ˣ),
        c ≠ 0 ∧ ∀ t, Dom t → trIn (imK τ'.ρ K') (jacB τ'.ρ (t₀ * t) ∘ₗ jacA hA) = c * trIn (imK τ.ρ K) (jacB τ.ρ (nT n N (t₀ * t)))

def LiftExp : Prop := ForLift fun _ _ _ _ _ _ _ n _ _ _ N τ τ' => ∀ μ, IsExp τ.ρ μ → IsExp τ'.ρ (μ.comp (nT n N))

def DescExp : Prop := ForLift fun _ E _ _ _ _ _ n _ w σw N τ τ' =>
  ∀ ω' : Fin n → (w.1.adicCompletion E)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω' i)) → (∀ i, Inv σw (ω' i)) →
    IsSubquotient τ'.ρ (prinSeries ω') → ∀ μ', IsExp τ'.ρ μ' → ∃ μ, IsExp τ.ρ μ ∧ μ.comp (nT n N) = μ'

def LiftGood : Prop := ForLift fun F _ _ _ _ _ _ n v _ _ N τ τ' =>
  ∀ ω : Fin n → (v.adicCompletion F)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) → IsSubquotient τ.ρ (prinSeries ω) →
    IsSubquotient τ'.ρ (prinSeries fun i => (ω i).comp N)

def DescGood : Prop := ForLift fun F E _ _ _ _ _ n v w σw N τ τ' =>
  ∀ ω' : Fin n → (w.1.adicCompletion E)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω' i)) → (∀ i, Inv σw (ω' i)) →
    IsSubquotient τ'.ρ (prinSeries ω') → ∃ ω : Fin n → (v.adicCompletion F)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧
      (∀ i, (ω i).comp N = ω' i) ∧ IsSubquotient τ.ρ (prinSeries ω)

end UpperTheory.Gal.Join
