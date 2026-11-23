import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus
open GlobalTheory.DeRham (spOver spOver_comp)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

variable {R : Type} [CommRing R]

section Tors

variable {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}

instance torsGroup (B : Type) [CommRing B] [Algebra R B] : CommGroup (Tors G N B) :=
  inferInstanceAs (CommGroup (powMonoidHom N : (SpAlg R B ⟶ G) →* (SpAlg R B ⟶ G)).ker)

@[simp] theorem tors_mul_val {B : Type} [CommRing B] [Algebra R B] (x y : Tors G N B) : (x * y).1 = x.1 * y.1 := rfl

@[simp] theorem tors_one_val {B : Type} [CommRing B] [Algebra R B] : (1 : Tors G N B).1 = 1 := rfl

def torsMap {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) (z : Tors G N B) :
    Tors G N C :=
  ⟨spOver φ ≫ z.1, by rw [← MonObj.comp_pow, z.2, MonObj.comp_one]⟩

@[simp] theorem torsMap_val {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C)
    (z : Tors G N B) : (torsMap φ z).1 = spOver φ ≫ z.1 := rfl

def torsIncl {N' : ℕ} (h : N ∣ N') {B : Type} [CommRing B] [Algebra R B] (z : Tors G N B) : Tors G N' B :=
  ⟨z.1, by obtain ⟨m, rfl⟩ := h; rw [pow_mul, z.2, one_pow]⟩

end Tors

example : True := trivial

section Ord

variable (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ)

def IsNatFn (σ : ∀ (B : Type) [CommRing B] [Algebra R B], Tors G N B → B) : Prop :=
  ∀ (B C : Type) [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) (z : Tors G N B),
    σ C (torsMap φ z) = φ (σ B z)

variable (K : Type) [Field K] [Algebra R K]

def ord : Subalgebra R (Tors G N K → K) where
  carrier := {f | ∀ s : Tors G N K, ∃ σ, IsNatFn G N σ ∧ ∀ x, σ K x = f (s * x)}
  mul_mem' {f g} hf hg s := by
    obtain ⟨σ, hσ, hσf⟩ := hf s
    obtain ⟨τ, hτ, hτg⟩ := hg s
    exact ⟨fun B _ _ z => σ B z * τ B z, fun B C _ _ _ _ φ z => by show σ C _ * τ C _ = _; rw [hσ, hτ, map_mul],
      fun x => (congrArg₂ _ (hσf x) (hτg x)).trans rfl⟩
  add_mem' {f g} hf hg s := by
    obtain ⟨σ, hσ, hσf⟩ := hf s
    obtain ⟨τ, hτ, hτg⟩ := hg s
    exact ⟨fun B _ _ z => σ B z + τ B z, fun B C _ _ _ _ φ z => by show σ C _ + τ C _ = _; rw [hσ, hτ, map_add],
      fun x => (congrArg₂ _ (hσf x) (hτg x)).trans rfl⟩
  algebraMap_mem' c s := ⟨fun B _ _ _ => algebraMap R B c, fun B C _ _ _ _ φ z => (φ.commutes c).symm,
    fun x => rfl⟩

end Ord

section Pts

variable (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ)

structure TorsPt (A : Type) [CommRing A] [HopfAlgebra R A] : Type 1 where

  pt : ∀ (B : Type) [CommRing B] [Algebra R B], Tors G N B → (A →ₐ[R] B)

  nat : ∀ (B C : Type) [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) (z : Tors G N B),
    pt C (torsMap φ z) = φ.comp (pt B z)

  mul : ∀ (B : Type) [CommRing B] [Algebra R B] (x y : Tors G N B),
    toConv (pt B (x * y)) = toConv (pt B x) * toConv (pt B y)

variable {G N} {A : Type} [CommRing A] [HopfAlgebra R A]

structure IsLevel (K : Type) [Field K] [Algebra R K] (θ : TorsPt G N A) : Prop where

  opn : ∃ V : (Sp A).Opens, ∀ (B : Type) [CommRing B] [Algebra R B],
    Set.BijOn (θ.pt B) Set.univ {φ | Set.range (spMap (φ : A →+* B)) ⊆ V}

  gen : Function.Bijective (θ.pt K)

end Pts

section Model

variable {p : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {GG : PDivGroup p R}

def _root_.GlobalTheory.GroupBplus.TorsionMap.level (θ : TorsionMap G GG) (n : ℕ) : TorsPt G (p ^ n) (GG.A n) where
  pt B _ _ z := θ.pt n B z
  nat B C _ _ _ _ φ z := θ.nat n B C φ z (torsMap φ z) rfl
  mul B _ _ x y := θ.mul n B x y (x * y) rfl

variable (K : Type) [Field K] [Algebra R K]

def IsModel (θ : TorsionMap G GG) : Prop := ∀ n, IsLevel K (θ.level n)

variable {K} [Algebra R K]

def GenCompat {G₀ : Over (Sp K)} [GrpObj G₀] (F : G₀.left ⟶ G.left) {GG₀ : PDivGroup p K} (θ : TorsionMap G GG)
    (θ₀ : TorsionMap G₀ GG₀) (e : GG₀ ≅ GG.baseChange K) : Prop :=
  ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower R K B] (z : Tors G (p ^ n) B)
    (z' : Tors G₀ (p ^ n) B), z.1.left = z'.1.left ≫ F → ∀ a, θ.pt n B z a = θ₀.pt n B z' (e.hom.app n (1 ⊗ₜ a))

end Model

section Chart

variable (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ)

structure PreChart (q : PrimeSpectrum R) : Type 1 where

  r : R
  hr : r ∉ q.asIdeal

  C : Type
  [ring : CommRing C]
  [alg : Algebra R C]
  [algLoc : Algebra (Localization.Away r) C]
  [tower : IsScalarTower R (Localization.Away r) C]
  [finite : Module.Finite (Localization.Away r) C]
  [free : Module.Free (Localization.Away r) C]

  j : Tors G N C

  W : G.left.Opens

  bij : ∀ (B : Type) [CommRing B] [Algebra R B],
    Set.BijOn (fun ψ : C →ₐ[R] B => torsMap ψ j) Set.univ {z | Set.range z.1.left ⊆ W}

  fibre : ∀ (k : Type) [Field k] [Algebra R k], RingHom.ker (algebraMap R k) = q.asIdeal →
    ∀ z : Tors G N k, Set.range z.1.left ⊆ W

attribute [instance] PreChart.ring PreChart.alg PreChart.algLoc PreChart.tower PreChart.finite PreChart.free

variable {G N}

def PreChart.IsGrp {q : PrimeSpectrum R} (c : PreChart G N q) : Prop :=
  (∃ ψ : c.C →ₐ[R] Localization.Away c.r, torsMap ψ c.j = 1) ∧
    ∀ (B : Type) [CommRing B] [Algebra R B] (ψ ψ' : c.C →ₐ[R] B),
      ∃ ψ'' : c.C →ₐ[R] B, torsMap ψ'' c.j = torsMap ψ c.j * torsMap ψ' c.j

end Chart

example (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra R K] (n : ℕ) :
    IsLevel K ((TorsionMap.ofTower (muTower p R)).level n) :=
  ⟨⟨⊤, fun B _ _ => by
    refine ⟨fun _ _ => ?_, (TorsionMap.ofTower_bijective (muTower p R) n B).1.injOn, fun φ _ => ?_⟩
    · intro x _; exact trivial
    · obtain ⟨z, hz⟩ := (TorsionMap.ofTower_bijective (muTower p R) n B).2 φ
      exact ⟨z, trivial, hz⟩⟩, TorsionMap.ofTower_bijective (muTower p R) n K⟩

end GlobalTheory.GroupBplus.Aff
