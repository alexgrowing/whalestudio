import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.HarderNarasimhan.QuotRealize
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

open NumberField
open scoped Matrix ComplexOrder
open Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TotallyDefiniteSelfDualLattices

section Space

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {ν : ℕ}

def form (J : Matrix (Fin ν) (Fin ν) E) (x y : Fin ν → E) : E :=
  (fun a => IsCMField.complexConj E (y a)) ⬝ᵥ (J *ᵥ x)

def TotallyPosDef (J : Matrix (Fin ν) (Fin ν) E) : Prop :=
  (∀ a b, IsCMField.complexConj E (J a b) = J b a) ∧ ∀ φ : E →+* ℂ, (J.map φ).PosDef

def IsSelfDualLattice (J : Matrix (Fin ν) (Fin ν) E) (L : Submodule (𝓞 E) (Fin ν → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin ν → E)) = ⊤ ∧
    ∀ x : Fin ν → E, x ∈ L ↔ ∀ y ∈ L, form J x y ∈ (1 : Submodule (𝓞 E) E)

end Space

def SpreadLe {ν : ℕ} (lam : DomWeight ν) (R : ℝ) : Prop :=
  ∀ i j : Fin ν, ((lam.w i - lam.w j : ℤ) : ℝ) ≤ R

section Sum

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι C : Type} [Fintype ι] {ν N : ℕ}

def comp (lam : ι → DomWeight ν) (e : Fin N ≃ C × VVIdx lam) (c : C) : (Fin N → K) →ₗ[K] VV K lam :=
  (bVV K lam).equivFun.symm.toLinearMap ∘ₗ LinearMap.funLeft K K fun i => e.symm (c, i)

def sumLat (emb : ι → E →+* K) (lam : ι → DomWeight ν) (L : C → Submodule (𝓞 E) (Fin ν → E))
    (e : Fin N ≃ C × VVIdx lam) : Submodule (𝓞 K) (Fin N → K) :=
  ⨅ c : C, (delAt emb lam (L c)).comap ((comp lam e c).restrictScalars (𝓞 K))

open Classical in

def sumGram [StarRing K] (emb : ι → E →+* K) (lam : ι → DomWeight ν) (J : Matrix (Fin ν) (Fin ν) E)
    (e : Fin N ≃ C × VVIdx lam) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun p q =>
    if (e p).1 = (e q).1 then pairV emb lam J (bVV K lam (e p).2) (bVV K lam (e q).2) else 0

end Sum

def IsDualFrame {N : ℕ} (G X' : Matrix (Fin N) (Fin N) ℂ) : Prop := X' * X'ᴴ = Gᵀ

example {E : Type} [Field E] [NumberField E] [IsCMField E] {ν : ℕ} :
    TotallyPosDef (1 : Matrix (Fin ν) (Fin ν) E) := by
  refine ⟨fun a b => ?_, fun φ => ?_⟩
  · by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · rw [Matrix.map_one _ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one

example {E : Type} [Field E] [NumberField E] [IsCMField E] {ν : ℕ} :
    IsSelfDualLattice (1 : Matrix (Fin ν) (Fin ν) E)
      (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := by
  classical
  have hs : ∀ a : Fin ν, (Pi.single a 1 : Fin ν → E) ∈
      Submodule.pi Set.univ fun _ : Fin ν => (1 : Submodule (𝓞 E) E) := by
    intro a b _
    by_cases h : b = a
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun x => ⟨fun hx y hy => ?_, fun hx a _ => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin ν)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨a, rfl⟩
    simpa using hs a
  · unfold form
    rw [Matrix.one_mulVec]
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨u, hu⟩ := Submodule.mem_one.mp (hx a trivial)
    obtain ⟨w, hw⟩ := Submodule.mem_one.mp (hy a trivial)
    refine Submodule.mem_one.mpr ⟨IsCMField.ringOfIntegersComplexConj E w * u, ?_⟩
    rw [map_mul, hu]
    congr 1
    show ((IsCMField.ringOfIntegersComplexConj E w : 𝓞 E) : E) = IsCMField.complexConj E (y a)
    rw [IsCMField.coe_ringOfIntegersComplexConj, ← hw]
  · have := hx _ (hs a)
    unfold form at this
    rw [Matrix.one_mulVec] at this
    have h2 : (fun b => IsCMField.complexConj E ((Pi.single a 1 : Fin ν → E) b)) = Pi.single a 1 := by
      funext b
      by_cases h : b = a
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [h2] at this
    simpa using this

def Statement : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [IsCMField E]
    [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K],
    (∃ v₀ : InfinitePlace K, ∀ a : K, v₀.embedding (star a) = (starRingEnd ℂ) (v₀.embedding a)) →
  ∀ (ι : Type) [Fintype ι] (emb : ι → E →+* K) (ν : ℕ), 1 ≤ ν →
  ∀ (J : Matrix (Fin ν) (Fin ν) E), TotallyPosDef J →
  ∀ (lam : ι → DomWeight ν) (R : ℝ), 1 ≤ R → (∀ τ, SpreadLe (lam τ) R) →
  ∀ (C : Type) [Fintype C] [Nonempty C] (L : C → Submodule (𝓞 E) (Fin ν → E)),
    (∀ c, IsSelfDualLattice J (L c)) →
  ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X' : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ),
    (∀ v, IsDualFrame ((sumGram emb lam J e).map v.embedding) (X' v)) →
    Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts.TestLatticeCondition N X' (dualFr (sumLat emb lam L e))
      (4 * (Fintype.card ι : ℝ) * (ν : ℝ) * R * Real.log ((ν : ℝ) * R))

end GlobalTheory.IndefiniteRowSideFullHecke.TotallyDefiniteSelfDualLattices
