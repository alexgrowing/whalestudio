import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

section
variable {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B)
  {L : Type} [Field L] [Algebra F L] {V : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]

def Dinv (ρ : Representation L G V) : Submodule L (V ⊗[F] B) :=
  ⨅ g, LinearMap.ker (AlgebraTensorModule.map (ρ g) (σ g) - LinearMap.id)

theorem mem_Dinv {ρ : Representation L G V} {x : V ⊗[F] B} :
    x ∈ Dinv σ ρ ↔ ∀ g, AlgebraTensorModule.map (ρ g) (σ g) x = x := by
  simp [Dinv, Submodule.mem_iInf, sub_eq_zero]

variable (L V) in

def onPer : End L (V ⊗[F] B) := AlgebraTensorModule.map LinearMap.id ψ

def admitted (e : ℕ) (ρ : Representation L G V) : Prop := finrank L (Dinv σ ρ) = e * finrank L V

def AnnD (q n : ℕ) (ρ : Representation L G V) (T : ℕ → End L V) : Prop :=
  ∀ x ∈ Dinv σ ρ, ∑ j ∈ Finset.range (n + 1),
    ((-1) ^ j * (q : ℤ) ^ (j.choose 2)) • AlgebraTensorModule.map (T j) (ψ ^ (n - j)) x = 0

def NilD (ρ : Representation L G V) (Q : Polynomial L) : Prop :=
  ∃ N : ℕ, ∀ x ∈ Dinv σ ρ, (Polynomial.aeval (onPer ψ L V) Q ^ N) x = 0

variable (L) in

def Bound (e : ℕ) : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [Module.Finite L U] (ρ : Representation L G U),
    Module.Finite L (Dinv σ ρ) ∧ finrank L (Dinv σ ρ) ≤ e * finrank L U

end

def Inter {L G V W : Type} [Field L] [Group G] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ : Representation L G V) (ρ' : Representation L G W) (f : V →ₗ[L] W) : Prop := ∀ g v, f (ρ g v) = ρ' g (f v)

def Subq {L G V W : Type} [Field L] [Group G] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ : Representation L G V) (ρ' : Representation L G W) : Prop :=
  ∃ (U : Type) (_ : AddCommGroup U) (_ : Module L U) (ρU : Representation L G U) (i : U →ₗ[L] V) (p : U →ₗ[L] W),
    Inter ρU ρ i ∧ Function.Injective i ∧ Inter ρU ρ' p ∧ Function.Surjective p

theorem Subq.refl {L G V : Type} [Field L] [Group G] [AddCommGroup V] [Module L V] (ρ : Representation L G V) : Subq ρ ρ :=
  ⟨V, inferInstance, inferInstance, ρ, LinearMap.id, LinearMap.id, fun _ _ => rfl, Function.injective_id, fun _ _ => rfl,
    Function.surjective_id⟩

def extRep {F G V : Type} [Field F] [Group G] [AddCommGroup V] [Module F V] (L : Type) [Field L] [Algebra F L]
    (ρ : Representation F G V) : Representation L G (L ⊗[F] V) where
  toFun g := (ρ g).baseChange L
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one F V
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

def DinvExact : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (L : Type) [Field L] [Algebra F L]
    (U V W : Type) [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [AddCommGroup V] [Module L V] [Module F V]
    [IsScalarTower F L V] [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]
    (ρU : Representation L G U) (ρV : Representation L G V) (ρW : Representation L G W) (i : U →ₗ[L] V) (p : V →ₗ[L] W),
    Inter ρU ρV i → Inter ρV ρW p → Function.Injective i → Function.Exact i p → Module.Finite L (Dinv σ ρV) →
    (Dinv σ ρV).map (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) ≤ Dinv σ ρW ∧
    finrank L (Dinv σ ρV) = finrank L (Dinv σ ρU) +
      finrank L ((Dinv σ ρV).map (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)))

def AdmExact : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (L : Type) [Field L] [Algebra F L] (e : ℕ),
    Bound σ L e → ∀ (V W : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V]
    [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W] [Module.Finite L W]
    (ρ : Representation L G V) (ρ' : Representation L G W) (f : V →ₗ[L] W), Inter ρ ρ' f →
    (Function.Injective f → admitted σ e ρ' → admitted σ e ρ) ∧
    (Function.Surjective f → admitted σ e ρ → admitted σ e ρ' ∧
      (Dinv σ ρ).map (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B)) = Dinv σ ρ')

def NilEmb : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (V : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] (ρ : Representation L G V)
    (I : Type) [Finite I] (W : I → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module L (W i)] [∀ i, Module F (W i)]
    [∀ i, IsScalarTower F L (W i)] (ρ' : ∀ i, Representation L G (W i)) (f : ∀ i, V →ₗ[L] W i),
    (∀ i, Inter ρ (ρ' i) (f i)) → (∀ v, (∀ i, f i v = 0) → v = 0) →
    ∀ Q : Polynomial L, (∀ i, NilD σ ψ (ρ' i) Q) → NilD σ ψ ρ Q

def NilSubq : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (e : ℕ), Bound σ L e → ∀ (V W : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V]
    [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]
    (ρ : Representation L G V) (ρ' : Representation L G W), Subq ρ ρ' → admitted σ e ρ →
    admitted σ e ρ' ∧ ∀ Q : Polynomial L, NilD σ ψ ρ Q → NilD σ ψ ρ' Q

def NilOfAnn : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B), (∀ g, Commute (σ g) ψ) →
    ∀ (L : Type) [Field L] [Algebra F L] (V : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (ρ : Representation L G V) (q n : ℕ) (T : ℕ → End L V) (θ : ℕ → L), (∀ j g, Commute (T j) (ρ g)) → (∀ i j, Commute (T i) (T j)) →
    (∀ j ≤ n, IsNilpotent (T j - θ j • (1 : End L V))) → AnnD σ ψ q n ρ T → NilD σ ψ ρ (heckePol q n θ)

def AnnSub : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (U V : Type) [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [AddCommGroup V] [Module L V] [Module F V]
    [IsScalarTower F L V] (ρU : Representation L G U) (ρ : Representation L G V) (i : U →ₗ[L] V), Inter ρU ρ i → Function.Injective i →
    ∀ (q n : ℕ) (TU : ℕ → End L U) (T : ℕ → End L V), (∀ j u, i (TU j u) = T j (i u)) → AnnD σ ψ q n ρ T → AnnD σ ψ q n ρU TU

def DinvExt : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (L : Type) [Field L] [Algebra F L]
    (V : Type) [AddCommGroup V] [Module F V] (ρ : Representation F G V),
    (Dinv σ (extRep L ρ)).map (AlgebraTensorModule.assoc F F L L V B).toLinearMap = (Dinv σ ρ).baseChange L

def AnnExt : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (V : Type) [AddCommGroup V] [Module F V] (ρ : Representation F G V),
    (∀ e, admitted σ e ρ → admitted σ e (extRep L ρ)) ∧
    ∀ (q n : ℕ) (T : ℕ → End F V), AnnD σ ψ q n ρ T → AnnD σ ψ q n (extRep L ρ) fun j => (T j).baseChange L

def AnnPer : Prop :=
  ∀ (F G B B' : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] [AddCommGroup B'] [Module F B']
    (σ : G → End F B) (ψ : End F B) (σ' : G → End F B') (ψ' : End F B') (c : B →ₗ[F] B'), Function.Injective c →
    (∀ g b, c (σ g b) = σ' g (c b)) → (∀ b, c (ψ b) = ψ' (c b)) →
    ∀ (L : Type) [Field L] [Algebra F L] (e : ℕ), Bound σ' L e →
    ∀ (V : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V] (ρ : Representation L G V),
      admitted σ e ρ → admitted σ' e ρ ∧ ∀ (q n : ℕ) (T : ℕ → End L V), AnnD σ ψ q n ρ T → AnnD σ' ψ' q n ρ T

def JoinAbs : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B), (∀ g, Commute (σ g) ψ) →
    ∀ (L : Type) [Field L] [Algebra F L] (e : ℕ), Bound σ L e →
    ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] (ρ : Representation F G V) (q n : ℕ) (T : ℕ → End F V),
      admitted σ e ρ → AnnD σ ψ q n ρ T →
    ∀ (U : Type) [AddCommGroup U] [Module L U] (ρU : Representation L G U) (i : U →ₗ[L] L ⊗[F] V) (TU : ℕ → End L U) (θ : ℕ → L),
      Inter ρU (extRep L ρ) i → Function.Injective i → (∀ j u, i (TU j u) = (T j).baseChange L (i u)) →
      (∀ j g, Commute (TU j) (ρU g)) → (∀ j j', Commute (TU j) (TU j')) → (∀ j ≤ n, IsNilpotent (TU j - θ j • (1 : End L U))) →
    ∀ (W : Type) [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W] (ρW : Representation L G W)
      (I : Type) [Finite I] (C : I → Type) [∀ a, AddCommGroup (C a)] [∀ a, Module L (C a)] (ρC : ∀ a, Representation L G (C a))
      (f : ∀ a, W →ₗ[L] C a), (∀ a, Subq ρU (ρC a)) → (∀ a, Inter ρW (ρC a) (f a)) → (∀ v, (∀ a, f a v = 0) → v = 0) →
      NilD σ ψ ρW (heckePol q n θ)

def CharOfNil : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (W : Type) [AddCommGroup W] [Module K W] [Module.Finite K W] (M : End K W) (s : Multiset K)
    (u : K), u ≠ 0 → s.card = finrank K W → GenericMul s → IsNilpotent (Polynomial.aeval M (Polynomial.C u * rootPol s)) →
    LinearMap.det M = s.prod → M.charpoly = rootPol s

end UpperTheory.Gal.crystallineComparison
