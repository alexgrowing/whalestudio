import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

def co {F L B : Type} [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] {a : ℕ} (x : (Fin a → L) ⊗[F] B) (i : Fin a) :
    L ⊗[F] B := AlgebraTensorModule.map (LinearMap.proj i : (Fin a → L) →ₗ[L] L) (LinearMap.id : B →ₗ[F] B) x

theorem co_tmul {F L B : Type} [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] {a : ℕ} (v : Fin a → L) (b : B) (i : Fin a) :
    co (v ⊗ₜ[F] b) i = v i ⊗ₜ[F] b := rfl

def onR {F B : Type} (L : Type) [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] (s : B →ₐ[F] B) : L ⊗[F] B →+* L ⊗[F] B :=
  (Algebra.TensorProduct.map (AlgHom.id F L) s).toRingHom

theorem onR_tmul {F B : Type} (L : Type) [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] (s : B →ₐ[F] B) (x : L) (b : B) :
    onR L s (x ⊗ₜ[F] b) = x ⊗ₜ[F] s b := rfl

def CoFacts : Prop :=
  ∀ (F L B : Type) [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] (a : ℕ),
    (∀ x y : (Fin a → L) ⊗[F] B, co (x + y) = co x + co y) ∧
    (∀ (c : L) (x : (Fin a → L) ⊗[F] B), co (c • x) = (c ⊗ₜ[F] (1 : B)) • co x) ∧
    (∀ (b : B) (x : (Fin a → L) ⊗[F] B), co (AlgebraTensorModule.map (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L))
      (LinearMap.mulLeft F b) x) = ((1 : L) ⊗ₜ[F] b) • co x) ∧
    (∀ (T : End L (Fin a → L)) (A : Matrix (Fin a) (Fin a) L), (∀ v, T v = A.mulVec v) → ∀ (s : B →ₐ[F] B) (x : (Fin a → L) ⊗[F] B),
      co (AlgebraTensorModule.map T s.toLinearMap x) = (A.map (algebraMap L (L ⊗[F] B))).mulVec fun i => onR L s (co x i)) ∧
    Function.Bijective fun x : (Fin 1 → L) ⊗[F] B => co x 0

def RingS : Prop :=
  ∀ (F L U B C : Type) [Field F] [Field L] [Field U] [CommRing B] [Field C] [Algebra F L] [Algebra F U] [Algebra F B] [Algebra U B]
    [IsScalarTower F U B] [Nontrivial B] (τL : L →+* C) (τU : U →+* C), (∀ z : F, τL (algebraMap F L z) = τU (algebraMap F U z)) →
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra C S) (π : L ⊗[F] B →+* S), Nontrivial S ∧
      (∀ x : L, π (x ⊗ₜ[F] (1 : B)) = algebraMap C S (τL x)) ∧ ∀ c : U, π ((1 : L) ⊗ₜ[F] algebraMap U B c) = algebraMap C S (τU c)

def UnitOfSpan : Prop :=
  ∀ (S : Type) [CommRing S] (a : ℕ) (v : Fin a → Fin a → S), Submodule.span S (Set.range v) = ⊤ →
    IsUnit (Matrix.det (Matrix.of fun i k => v k i))

def BasisIn : Prop :=
  ∀ (C W X : Type) [Field C] [AddCommGroup W] [Module C W] [Module.Finite C W] (a : ℕ) (mk : X → W),
    Submodule.span C (Set.range mk) = ⊤ → finrank C W = a → ∃ (x : Fin a → X) (b : Basis (Fin a) C W), ∀ k, b k = mk (x k)

def DetCore : Prop :=
  ∀ (C R S W W' X X' : Type) [Field C] [CommRing R] [CommRing S] [Algebra C S] [Nontrivial S] [AddCommGroup W] [Module C W]
    [Module.Finite C W] [AddCommGroup W'] [Module C W'] [Module.Finite C W'] (a : ℕ) (π : R →+* S) (mk : X → W) (mk' : X' → W')
    (c : X → Fin a → R) (c' : X' → R) (j : W →ₗ[C] (Fin a → S)) (j' : W' →ₗ[C] S) (M : End C W) (M' : End C W')
    (w : X → X) (w' : X' → X') (A : Matrix (Fin a) (Fin a) R) (s : R →+* R),
    finrank C W = a → finrank C W' = 1 → Submodule.span C (Set.range mk) = ⊤ →
    (∀ x i, j (mk x) i = π (c x i)) → (∀ x, j' (mk' x) = π (c' x)) →
    (∀ x, M (mk x) = mk (w x)) → (∀ x, M' (mk' x) = mk' (w' x)) →
    (∀ x, c (w x) = A.mulVec fun i => s (c x i)) → (∀ x, c' (w' x) = A.det * s (c' x)) →
    (∀ x : Fin a → X, ∃ x', c' x' = Matrix.det (Matrix.of fun i k => c (x k) i)) →
    Submodule.span S (Set.range fun x i => π (c x i)) = ⊤ → LinearMap.det M = LinearMap.det M'

def WdLift : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (N : Type) [AddCommGroup N] [Module ℂ N]
    (κ : ↥(Dpst P ρ) → N), (∀ x y, κ (x + y) = κ x + κ y) → (∀ (c : ↥LL.1) x, κ (c • x) = ι (c : Om l) • κ x) →
    (∀ (c : ↥(MaximalUnramifiedExtension l)) x, κ (mulD P ρ c x) = ι (c : Om l) • κ x) → ∃ j : WDSpace P ι ρ →ₗ[ℂ] N, ∀ x, j (wdMk P ι ρ x) = κ x

def DetMem : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (a : ℕ) (ρ : Representation ↥LL.1 ↥(GK K) (Fin a → ↥LL.1))
    (ρ' : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (A : ↥(GK K) → Matrix (Fin a) (Fin a) ↥LL.1)
    (A' : ↥(GK K) → Matrix (Fin 1) (Fin 1) ↥LL.1), (∀ g v, ρ g v = (A g).mulVec v) → (∀ g v, ρ' g v = (A' g).mulVec v) →
    (∀ g, (A' g).det = (A g).det) → ∀ x : Fin a → ↥(Dpst P ρ), ∃ x' : ↥(Dpst P ρ'),
      co (x' : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P) 0 =
        Matrix.det (Matrix.of fun i k => co (x k : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)

def WeilCo : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (LL : FinExt l)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] (g : ↥(Weil h)), deg g = -1 →
    ∀ x : ↥(Dpst P ρ), (weilD Bw h P ρ g x : V ⊗[ℚ_[l]] Bst P) = AlgebraTensorModule.map (ρ (weilToGK Bw h g))
      ((actSt P (weilToGK Bw h g : GQ l)).comp (phiSt P ^ resDeg l w)).toLinearMap (x : V ⊗[ℚ_[l]] Bst P)

def SpanS : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (K LL : FinExt l) (a : ℕ)
    (ρ : Representation ↥LL.1 ↥(GK K) (Fin a → ↥LL.1)), IsSst P ρ → ∀ (S : Type) [CommRing S] (π : ↥LL.1 ⊗[ℚ_[l]] Bst P →+* S),
    Submodule.span S (Set.range fun (x : ↥(Dpst P ρ)) i => π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)) = ⊤

def CoLift : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (K LL : FinExt l) (a : ℕ)
    (ρ : Representation ↥LL.1 ↥(GK K) (Fin a → ↥LL.1)) (S : Type) [CommRing S] [Algebra ℂ S] (π : ↥LL.1 ⊗[ℚ_[l]] Bst P →+* S),
    (∀ x : ↥LL.1, π (x ⊗ₜ[ℚ_[l]] (1 : Bst P)) = algebraMap ℂ S (ι (x : Om l))) →
    (∀ c : ↥(MaximalUnramifiedExtension l), π ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) = algebraMap ℂ S (ι (c : Om l))) →
    ∃ j : WDSpace P ι ρ →ₗ[ℂ] (Fin a → S), ∀ x i, j (wdMk P ι ρ x) i = π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)

def DetE : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (a : ℕ) (LL : FinExt l)
    (r : ↥(Dec (F := E) A) →* GL (Fin a) ↥LL.1) (c : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1),
    (∀ g, Matrix.GeneralLinearGroup.det (c g) = Matrix.GeneralLinearGroup.det (r g)) → IsSst P (Bw.repE LL r) →
    ∀ (hr : IsPst P (Bw.repE LL r)) (hc : IsPst P (Bw.repE LL c)) (g : ↥(Weil h)), deg g = -1 →
      haveI := hr.finite; haveI := hc.finite
      LinearMap.det (wdRho P ι Bw h hj (Bw.repE LL r) g) = LinearMap.det (wdRho P ι Bw h hj (Bw.repE LL c) g)

def CommonModel : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ)
    (r : ↥Gw →* GL (Fin a) (Om l)) (c : ↥Gw →* GL (Fin 1) (Om l)), IsCrysAt P Bw r → IsPstAt P Bw c →
    ∃ (LL : FinExt l) (r' : ↥Gw →* GL (Fin a) ↥LL.1) (c' : ↥Gw →* GL (Fin 1) ↥LL.1), IsModel Bw r LL r' ∧ IsModel Bw c LL c' ∧
      IsSst P (Bw.repE LL r') ∧ IsPst P (Bw.repE LL r') ∧ IsPst P (Bw.repE LL c')

end UpperTheory.Gal.crystallineComparison
