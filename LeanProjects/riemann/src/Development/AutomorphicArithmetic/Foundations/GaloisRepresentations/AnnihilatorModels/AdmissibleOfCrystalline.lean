import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section

open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct Module Matrix
open scoped Formalism.Per

namespace UpperTheory.Gal.crystallineComparison

def AffFinProj : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f → AffFin Y

def HeckeRoots : Prop :=
  ∀ (K : Type) [CommRing K] (q n : ℕ) (t u : K) (β : Multiset K) (θ : ℕ → K), t ^ 2 = q → β.card = n →
    (∀ j ≤ n, θ j = u * t ^ (j * (n - j)) * β.esymm j) → heckePol q n θ = Polynomial.C u * rootPol (β.map fun b => t ^ (n - 1) * b)

theorem heckePol_map {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (q n : ℕ) (θ : ℕ → K) :
    (heckePol q n θ).map f = heckePol q n fun j => f (θ j) := by
  simp [heckePol, Polynomial.map_sum]

def AnnMat {F G C : Type} [Field F] [CommRing C] (c : F →+* C) (s : G → C → C) (φ : C → C) (q n : ℕ) {a : ℕ}
    (M : G → Matrix (Fin a) (Fin a) F) (T : ℕ → Matrix (Fin a) (Fin a) F) : Prop :=
  ∀ x : Fin a → C, (∀ g, (M g).map c *ᵥ (fun i => s g (x i)) = x) →
    ∑ j ∈ Finset.range (n + 1), ((-1) ^ j * (q : ℤ) ^ (j.choose 2)) • ((T j).map c *ᵥ fun i => φ^[n - j] (x i)) = 0

def AnnOfMat : Prop :=
  ∀ (F G B C : Type) [Field F] [Group G] [CommRing B] [Algebra F B] [CommRing C] (σ : G → End F B) (ψ : End F B)
    (c : F →+* C) (s : G → C → C) (φ : C → C) (e : B ≃+* C), (∀ z, e (algebraMap F B z) = c z) → (∀ g b, e (σ g b) = s g (e b)) →
    (∀ b, e (ψ b) = φ (e b)) → ∀ (V : Type) [AddCommGroup V] [Module F V] (a : ℕ) (b : Basis (Fin a) F V) (ρ : Representation F G V)
    (q n : ℕ) (T : ℕ → End F V), AnnMat c s φ q n (fun g => LinearMap.toMatrix b b (ρ g)) (fun j => LinearMap.toMatrix b b (T j)) →
      AnnD σ ψ q n ρ T

def AdmOfCrys : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → admitted (σCr P K) (finrank ℚ_[l] ↥(K0 K)) ρ

def AnnTied : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (K : FinExt l)
    (c : ℚ_[l] →+* Formalism.Per.Bcris l), (∀ z : ℤ_[l], c (z : ℚ_[l]) = Formalism.Per.zB l z) →
    ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (a : ℕ) (b : Basis (Fin a) ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V)
      (f q n : ℕ) (T : ℕ → End ℚ_[l] V),
      AnnMat c (fun (g : ↥(GK K)) x => Formalism.Per.σB (g : GQ l) x) (⇑(Formalism.Per.φB l))^[f] q n (fun g => LinearMap.toMatrix b b (ρ g))
        (fun j => LinearMap.toMatrix b b (T j)) → AnnD (σCr P K) (ψCr P f) q n ρ T

def JoinSt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (K LL : FinExt l)
    (c : ℚ_[l] →+* Formalism.Per.Bcris l), (∀ z : ℤ_[l], c (z : ℚ_[l]) = Formalism.Per.zB l z) →
    ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (a : ℕ) (b : Basis (Fin a) ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V)
      (f q n : ℕ) (T : ℕ → End ℚ_[l] V), IsCrys (P.PD K) ρ →
      AnnMat c (fun (g : ↥(GK K)) x => Formalism.Per.σB (g : GQ l) x) (⇑(Formalism.Per.φB l))^[f] q n (fun g => LinearMap.toMatrix b b (ρ g))
        (fun j => LinearMap.toMatrix b b (T j)) →
    ∀ (U : Type) [AddCommGroup U] [Module ↥LL.1 U] (ρU : Representation ↥LL.1 ↥(GK K) U) (i : U →ₗ[↥LL.1] ↥LL.1 ⊗[ℚ_[l]] V)
      (TU : ℕ → End ↥LL.1 U) (θ : ℕ → ↥LL.1),
      Inter ρU (extRep ↥LL.1 ρ) i → Function.Injective i → (∀ j u, i (TU j u) = (T j).baseChange ↥LL.1 (i u)) →
      (∀ j g, Commute (TU j) (ρU g)) → (∀ j j', Commute (TU j) (TU j')) → (∀ j ≤ n, IsNilpotent (TU j - θ j • (1 : End ↥LL.1 U))) →
    ∀ (W : Type) [AddCommGroup W] [Module ↥LL.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥LL.1 W] (ρW : Representation ↥LL.1 ↥(GK K) W)
      (I : Type) [Finite I] (C : I → Type) [∀ a, AddCommGroup (C a)] [∀ a, Module ↥LL.1 (C a)]
      (ρC : ∀ a, Representation ↥LL.1 ↥(GK K) (C a)) (e : ∀ a, W →ₗ[↥LL.1] C a),
      (∀ a, Subq ρU (ρC a)) → (∀ a, Inter ρW (ρC a) (e a)) → (∀ v, (∀ a, e a v = 0) → v = 0) →
      NilD (σSt P K) (ψSt P f) ρW (heckePol q n θ)

theorem admissible_of_crystalline : AdmOfCrys := by
  intro l _ P K V _ _ ρ h
  have e : Dinv (σCr P K) ρ = Dcris (P.PD K) ρ := by
    unfold Dinv Dcris actVB σCr
    refine iInf_congr fun g => ?_
    congr 3
    ext b
    simp [P.PD_actB]
  unfold admitted
  rw [e]
  exact h

theorem joinSt_of (h1 : JoinAbs) (h2 : BoundSt) (h3 : StOfCr) (h4 : AnnTied) : JoinSt := by
  intro l _ P AI hT K LL c hc V _ _ a b ρ f q n T hcr hann U _ _ ρU i TU θ a1 a2 a3 a4 a5 a6 W _ _ _ _ ρW I _ C _ _ ρC e b1 b2 b3
  haveI : Module.Finite ℚ_[l] V := Module.Finite.of_basis b
  obtain ⟨hB, hcm⟩ := h2 l P AI hT K LL
  obtain ⟨hA, hD⟩ := h3 l P AI hT K V ρ (admissible_of_crystalline l P K V ρ hcr)
  exact h1 ℚ_[l] _ _ (σSt P K) (ψSt P f) (hcm f) ↥LL.1 _ hB V ρ q n T hA (hD f q n T (h4 l P AI hT K c hc V a b ρ f q n T hann))
    U ρU i TU θ a1 a2 a3 a4 a5 a6 W ρW I C ρC e b1 b2 b3

end UpperTheory.Gal.crystallineComparison
