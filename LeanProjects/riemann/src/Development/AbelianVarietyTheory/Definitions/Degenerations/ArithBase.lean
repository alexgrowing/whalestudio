import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZH
open Classical

def eStd (g n : ℕ) (a b : Fin g ⊕ Fin g → ZMod n) : ZMod n := ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i))

structure ThetaSys (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] where
  g : ℕ
  N : ℕ
  r : ℕ
  N_ge : 2 ≤ N
  r_pos : 1 ≤ r
  ζ : o
  prim : IsPrimitiveRoot ζ ((r * N) ^ 2)
  unit : IsUnit ((r * N : ℕ) : o)
  J : Type
  [fin : Fintype J]
  [ne : Nonempty J]
  ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o
  ρ_one : ∀ a, r • a = 0 → ρ a = 1
  ρ_mul : ∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)
  ρ_add : ∀ a b, r • eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)
  th : (Fin g ⊕ Fin g → ZMod (r * N)) → Ω
  ev : (Fin g ⊕ Fin g → ZMod (r * N)) → J → Ω
  R : Subalgebra o Ω
  fg : R.FG
  frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b
  th_mem : ∀ x, th x ∈ R
  ev_mem : ∀ x i, ev x i ∈ R
  supp : AddSubgroup.closure {x | th x ≠ 0} = ⊤
  th_ne : ∃ x, th x ≠ 0
attribute [instance] ThetaSys.fin ThetaSys.ne
namespace ThetaSys
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

abbrev Gam : Type := Fin S.g ⊕ Fin S.g → ZMod (S.r * S.N)

def perp (H : AddSubgroup S.Gam) : AddSubgroup S.Gam where
  carrier := {a | ∀ h ∈ H, eStd S.g _ a h = 0}
  add_mem' := by
    intro a b ha hb h hh
    have h1 := ha h hh
    have h2 := hb h hh
    simp only [eStd, Pi.add_apply] at h1 h2 ⊢
    rw [← add_zero (0 : ZMod (S.r * S.N))]
    nth_rewrite 1 [← h1]
    rw [← h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  zero_mem' := by
    intro h _
    simp [eStd]
  neg_mem' := by
    intro a ha h hh
    have h1 := ha h hh
    simp only [eStd, Pi.neg_apply] at h1 ⊢
    rw [← neg_zero, ← h1, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

def IsoFree (T : AddSubgroup S.Gam) : Prop := T ≤ S.perp T ∧ ∃ d : ℕ, Nonempty (T ≃+ (Fin d → ZMod (S.r * S.N)))

def ζN : o := S.ζ ^ (S.r ^ 2 * S.N)

def proj (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) : Matrix S.J S.J o :=
  Ring.inverse (Nat.card T : o) • ∑ᶠ t : T, S.ζN ^ (-(c t)).val • S.ρ t

def FF (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) : Ω :=
  ∑ᶠ t : T, algebraMap o Ω (S.ζ ^ (k.2 t).val) * ∑ j, algebraMap o Ω (S.proj T c j k.1) * S.ev t j

structure Test (p : ℕ) [Fact p.Prime] (y : S.R →+* PadicAlgCl p) where
  X : Type
  [add : AddCommGroup X]
  [free : Module.Free ℤ X]
  [finite : Module.Finite ℤ X]
  q : QuadraticMap ℤ X ℝ
  pos : Filter.Tendsto q Filter.cofinite Filter.atTop
  yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range
  yy_onto : Function.Surjective yy
  isoFree : S.IsoFree (S.perp yy.ker)
  wt : X →+ (S.perp yy.ker →+ ZMod S.N)
  wt_eq : ∀ (x : S.Gam) (α : X), yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker,
    wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x)
  δ : ℝ
  δ_max : IsGreatest (Set.range fun x => ‖y ⟨S.th x, S.th_mem x⟩‖) δ
  δ_pos : 0 < δ
  supp : AddSubgroup.closure {x | ‖y ⟨S.th x, S.th_mem x⟩‖ = δ} = yy.ker
  tx : ∀ x, y ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : X, yy x = QuotientAddGroup.mk w ∧
    ‖y ⟨S.th x, S.th_mem x⟩‖ ≤ δ * Real.exp (-(q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))
  le : ∀ (α : X), (∀ v0, q α ≤ q (α + S.N • v0)) → ∀ h ∈ yy.ker, ∀ i,
    ‖∑ j, y (algebraMap o S.R (S.proj _ (wt α) j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ δ * Real.exp (-(q α / S.N))
  eq : ∀ (α : X), (∀ v0, q α ≤ q (α + S.N • v0)) → ∃ (k : _) (hk : S.FF _ (wt α) k ∈ S.R),
    ‖y ⟨S.FF _ (wt α) k, hk⟩‖ = δ * Real.exp (-(q α / S.N))
  unit0 : ∀ h ∈ yy.ker, ∃ i, ‖∑ j, y (algebraMap o S.R (S.proj _ (wt 0) j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ = δ
attribute [instance] Test.add Test.free Test.finite

def HasTests : Prop := ∀ (p : ℕ) [Fact p.Prime] (y : S.R →+* PadicAlgCl p),
  (∀ a : o, ‖y (algebraMap o S.R a)‖ ≤ 1) → Nonempty (S.Test p y)
variable (M : RatModel o Ω)

def supI (z : M.Z) : Set S.Gam := {x | M.Div S.th x z}

def HH (z : M.Z) : AddSubgroup S.Gam := AddSubgroup.closure (S.supI M z)

def TT (z : M.Z) : AddSubgroup S.Gam := S.perp (S.HH M z)

structure Over₀ (U₀ : M.Z.Opens) : Prop where
  normal : IsNormalScheme M.Z
  proj : IsProjOver M.s
  div : M.HasDiv S.th
  ne : (U₀ : Set M.Z).Nonempty
  le : S.R ≤ M.ringOn U₀
  th_unit : ∀ x, S.th x ≠ 0 → (S.th x)⁻¹ ∈ M.ringOn U₀
  FF_unit : ∀ T c k, S.IsoFree T → S.FF T c k ≠ 0 → (S.FF T c k)⁻¹ ∈ M.ringOn U₀

def admitted (U₀ : M.Z.Opens) : Prop :=
  S.Over₀ M U₀ ∧ ∀ T c, S.IsoFree T → S.FF T c ≠ 0 → M.HasDiv (S.FF T c)

def At {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) : Prop :=
  ∀ a : S.R, y₀ a = M.val (gPt p ≫ y) a

def Test.E {S : ThetaSys o Ω} {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y) :
    Submodule (OO p) (S.J → PadicAlgCl p) :=
  Submodule.span (OO p) {v | ∃ (α : τ.X) (l : PadicAlgCl p) (i : S.J), (∀ v0, τ.q α ≤ τ.q (α + S.N • v0)) ∧
    ‖l‖ ≤ Real.exp (τ.q α / S.N) ∧ v = fun j => l * y (algebraMap o S.R (S.proj _ (τ.wt α) j i))}

def IsEE (U₀ : M.Z.Opens) (EE : M.Lat S.J) : Prop :=
  (∀ z ∈ U₀, EE.E z = Submodule.span (M.O z) (Set.range fun i => Pi.single i (1 : Ω))) ∧
  ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀),
    M.Cen U₀ z y → S.At M y y₀ →
    Submodule.span (OO p) ((fun (v : S.J → Ω) j => M.val (gPt p ≫ y) (v j)) '' (EE.E z)) = τ.E
end ThetaSys

class ArithBase (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] : Prop where
  ded : IsDedekindDomain o
  ft : Algebra.FiniteType ℤ o
  char : CharZero Ω
  inj : Function.Injective (algebraMap o Ω)
end GlobalTheory.ZH
end
