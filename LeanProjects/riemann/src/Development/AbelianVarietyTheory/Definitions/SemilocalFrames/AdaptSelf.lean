import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast

noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
namespace GlobalTheory.DegAsm
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  {H : HermSpace K V} {r : ℕ}

def SameGr (F G : FlagD H r) : Prop := ∀ a : Fin (r + 1), G.e a - F.e a ∈ F.Xa a.val

def Adapt (F F' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) : Prop := N.𝔡 = 𝔡 ∧ SameGr F N.F ∧ SameGr F' N.F'

def omI (F F' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V) : ℝ :=
  sInf ((fun N : NF H r => N.om Λ) '' {N | Adapt F F' 𝔡 N})

def pairM (F F' : FlagD H r) (j : ℕ) : Fin (r + 1) → Fin (r + 1) → K :=
  fun a b => if a.val < j ∧ b.val < j then H.B (F.e a) (F'.e b) else 0

def lab (F F' : FlagD H r) (j : ℕ) : ℕ → K := fun l => if h : l ≤ j ∧ l ≤ r + 1 then Dl F F' l h.2 else 0

def IsEmb (F : FlagD H r) (HW : HermSpace K W) (e : W →ₗ[K] V) : Prop :=
  (∀ x y, H.B (e x) (e y) = HW.B x y) ∧
    ∀ v : V, (∀ a : Fin (r + 1), H.B (F.e a) v = 0) ↔ v ∈ LinearMap.range e ⊔ F.X

def lat0 (F : FlagD H r) (e : W →ₗ[K] V) (Λ : Submodule (𝓞 K) V) : Submodule (𝓞 K) W :=
  (Λ ⊔ rs (𝓞 K) F.X).comap (e.restrictScalars (𝓞 K))

def datOf (F F' : FlagD H r) (e : W →ₗ[K] V) (g : ℕ) (Λ : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) W × Submodule (𝓞 K) (W × W) :=
  ((flagPairDefinitePartLattice F' F Λ ⊔ rs (𝓞 K) F.X).comap (e.restrictScalars (𝓞 K)),
    (iotaGraph F F' Λ (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)).comap ((e.prodMap e).restrictScalars (𝓞 K)))

def IsH (F F' : FlagD H r) (e : W →ₗ[K] V) (γ : V ≃ₗ[K] V) (h : W ≃ₗ[K] W) : Prop :=
  ∀ w : W, ∃ y ∈ wSp F F', y - e (h w) ∈ F.X ∧ y - γ (e w) ∈ F'.X

def FrEqv (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (G G' : FlagD H r) : Prop :=
  ∃ n : V ≃ₗ[K] V, F.InN (n : V →ₗ[K] V) ∧ n • Λ = Λ ∧ ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val

def datBd (K : Type) [Field K] [NumberField K] [StarRing K] (k r : ℕ) (Del Db NT x : ℝ) : ℝ :=
  (Del / x) ^ ((k : ℝ) / 2) *
    (8 ^ (r + 1) * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ^ 2 * Del ^ (3 * cf K + 6) * NT ^ 2 * (Db * Del * NT) ^ (10000 * (r + 1) ^ 3))

theorem adapt_self (N : NF H r) : Adapt N.F N.F' N.𝔡 N :=
  ⟨rfl, fun a => by simp, fun a => by simp⟩
end GlobalTheory.DegAsm
