import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

def spanS {K V : Type} [Field K] [AddCommGroup V] [Module K V] (S : Subring K) {ι : Type}
    [Fintype ι] (b : ι → V) : AddSubgroup V where
  carrier := {v | ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i}
  zero_mem' := ⟨0, fun _ => S.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, fun i => S.add_mem (hc i) (hd i), by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro x ⟨c, hc, rfl⟩
    exact ⟨-c, fun i => S.neg_mem (hc i), by
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]⟩

section Abs

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def SplitAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ ξ ∈ Submodule.span K (Set.range b),
    IsUnitIn S (h ξ ξ * (π ^ e i₀)⁻¹) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ h (c i₀) (c i₀) = h ξ ξ ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b

def ExactAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ ξ ∈ Submodule.span K (Set.range b),
    IsUnitIn S (h ξ ξ * (π ^ e i₀)⁻¹) → ∃ X ∈ spanS S b, h X X = h ξ ξ

def RebaseAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ X ∈ spanS S b, IsUnitIn S (h X X * (π ^ e i₀)⁻¹) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ c i₀ = X ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b

theorem splitAt_of {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hE : ExactAt S π h)
    (hR : RebaseAt S π h) : SplitAt S π h := by
  intro ι _ _ b e i₀ horth hunit hmin ξ hξ hξu
  obtain ⟨X, hX, hXX⟩ := hE ι b e i₀ horth hunit hmin ξ hξ hξu
  have hXu : IsUnitIn S (h X X * (π ^ e i₀)⁻¹) := by rw [hXX]; exact hξu
  obtain ⟨c, hco, hcu, hc0, hsp, hmem⟩ := hR ι b e i₀ horth hunit hmin X hX hXu
  exact ⟨c, hco, hcu, by rw [hc0, hXX], hsp, hmem⟩

end Abs

def ExactVec : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h →
    ∀ P : Ideal (𝓞 K), P.IsMaximal → ∀ π : K, IsUnif (locRing P) π → ExactAt (locRing P) π h

def Rebase : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Subring K) (π : K)
    (h : V →ₗ⋆[K] V →ₗ[K] K), IsHermSemilocal S → IsUnif S π → h.IsSymm →
    (∀ x, h x x = 0 → x = 0) → RebaseAt S π h

def LocSpan : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ P : Ideal (𝓞 K), P.IsMaximal → ∀ (n : ℕ) (b : Fin n → V)
    (v : V), v ∈ Formalism.HermitianLatticesTheory.loc (K := K) P (Submodule.span (𝓞 K) (Set.range b)) ↔
      v ∈ spanS (locRing P) b

def UnifVal : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ P : Ideal (𝓞 K), P.IsMaximal →
    ∃ π : K, IsUnif (locRing P) π ∧ ∀ a : 𝓞 F, a ≠ 0 →
      IsUnitIn (locRing P)
        (algebraMap F K (a : F) * (π ^ vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) a)⁻¹)

def JordSpan : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V), Submodule.IsLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ (n : ℕ) (b : Fin n → V), locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L →
      Submodule.span K (Set.range b) = ⊤

end Formalism.L2.SG.Pf.G3
