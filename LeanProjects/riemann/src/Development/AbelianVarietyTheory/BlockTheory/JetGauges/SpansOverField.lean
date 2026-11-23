import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement

open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

section Lattice

variable (E : Type) [Field E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

def GenMod (r₁ : ℕ) {ι : Type} (y : ι → X) : Prop :=
  ∀ x : X, ∃ z : X, x - r₁ • z ∈ Submodule.span (𝓞 E) (Set.range y)

def SpansOverField {ι : Type} (x : ι → X) : Prop :=
  ∀ u : X, ∃ n : ℕ, 0 < n ∧ n • u ∈ Submodule.span (𝓞 E) (Set.range x)

end Lattice

def LatticeStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (r₁ R : ℕ), 2 ≤ r₁ → r₁ ∣ R →
    ∀ (r : ℕ) (y : Fin r → X), GenMod E r₁ y →
    ∀ z : Fin r → X, SpansOverField E (fun b => y b + R • z b)

section PhiC

variable (E : Type) [Field E] [NumberField E] [IsCMField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

abbrev bar (a : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E a

def outer {n : ℕ} (x x' : Fin n → X) (η η' : Module.Dual (𝓞 E) X) : 𝓞 E :=
  ∑ i, η (x i) * bar E (η' (x' i))

def IsPosHerm (l : Module.Dual (𝓞 E) X → Module.Dual (𝓞 E) X → 𝓞 E) : Prop :=
  (∀ η η', l η' η = bar E (l η η')) ∧
    ∀ η, η ≠ 0 → ∀ τ : E →+* ℂ, 0 < (τ (l η η : E)).re

def IsBalanced (B : X → X → ℝ) : Prop :=
  ∀ (a : 𝓞 E) (x x' : X), B (a • x) x' = B x (bar E a • x')

def pairing (B : X → X → ℝ) {n : ℕ} (x x' : Fin n → X) : ℝ := (∑ i, B (x i) (x' i)) / 2

def phiC (B : X → X → ℝ) : EReal :=
  sInf {t : EReal | ∃ (n : ℕ) (x x' : Fin n → X), IsPosHerm E (outer E x x') ∧ t = (pairing B x x' : ℝ)}

private theorem bar_bar_jet_gauges (a : 𝓞 E) : bar E (bar E a) = a := by
  apply RingOfIntegers.ext
  simp [bar]

private theorem eq_sum_of_support_subset (s : X →ₗ[𝓞 E] X →₀ 𝓞 E)
    (hs : Finsupp.linearCombination (𝓞 E) id ∘ₗ s = LinearMap.id) (S : Finset X) (x : X)
    (hx : (s x).support ⊆ S) : x = ∑ m ∈ S, s x m • m := by
  have h : (s x).sum (fun m a => a • m) = x := by
    have := LinearMap.congr_fun hs x
    simpa [Finsupp.linearCombination_apply] using this
  rw [Finsupp.sum_of_support_subset (s x) hx (fun m a => a • m) (fun _ _ => zero_smul _ _)] at h
  exact h.symm

private theorem sum_B_eq_sum_bar_outer (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hB : IsBalanced E (fun a c => B a c))
    (s : X →ₗ[𝓞 E] X →₀ 𝓞 E) (hs : Finsupp.linearCombination (𝓞 E) id ∘ₗ s = LinearMap.id)
    (S : Finset X) {n : ℕ} (x x' : Fin n → X)
    (hx : ∀ i, (s (x i)).support ⊆ S) (hx' : ∀ i, (s (x' i)).support ⊆ S) :
    ∑ i, B (x i) (x' i) = ∑ m ∈ S, ∑ p ∈ S,
      B m (bar E (outer E x x' ((Finsupp.lapply m).comp s) ((Finsupp.lapply p).comp s)) • p) := by
  have hB' : ∀ (a : 𝓞 E) (y y' : X), B (a • y) y' = B y (bar E a • y') := hB
  have h1 : ∀ i, B (x i) (x' i) = ∑ m ∈ S, ∑ p ∈ S, B m ((bar E (s (x i) m) * s (x' i) p) • p) := by
    intro i
    have e1 := eq_sum_of_support_subset E s hs S (x i) (hx i)
    have e2 := eq_sum_of_support_subset E s hs S (x' i) (hx' i)
    conv_lhs => rw [e1, e2]
    simp only [map_sum, LinearMap.sum_apply, hB', smul_smul]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← map_sum, ← Finset.sum_smul]
  refine congrArg (fun a => B m (a • p)) ?_
  simp only [outer, map_sum, map_mul, bar_bar_jet_gauges, LinearMap.comp_apply, Finsupp.lapply_apply]

theorem pairing_eq_of_outer_eq [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hB : IsBalanced E (fun a c => B a c)) {n m : ℕ}
    (x x' : Fin n → X) (u u' : Fin m → X) (h : outer E x x' = outer E u u') :
    pairing (fun a c => B a c) x x' = pairing (fun a c => B a c) u u' := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective (𝓞 E) X)
  let S : Finset X := Finset.univ.biUnion (fun i => (s (x i)).support ∪ (s (x' i)).support) ∪
    Finset.univ.biUnion (fun j => (s (u j)).support ∪ (s (u' j)).support)
  have hx : ∀ i, (s (x i)).support ⊆ S := fun i a ha => by
    simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inl ⟨i, Or.inl ha⟩
  have hx' : ∀ i, (s (x' i)).support ⊆ S := fun i a ha => by
    simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inl ⟨i, Or.inr ha⟩
  have hu : ∀ j, (s (u j)).support ⊆ S := fun j a ha => by
    simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨j, Or.inl ha⟩
  have hu' : ∀ j, (s (u' j)).support ⊆ S := fun j a ha => by
    simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨j, Or.inr ha⟩
  unfold pairing
  rw [sum_B_eq_sum_bar_outer E B hB s hs S x x' hx hx',
    sum_B_eq_sum_bar_outer E B hB s hs S u u' hu hu', h]

example [Subsingleton X] (B : X → X → ℝ) (hB : B 0 0 = 0) : phiC E B = 0 := by
  have hp : ∀ {n : ℕ} (x x' : Fin n → X), pairing B x x' = 0 := by
    intro n x x'
    simp [pairing, fun i => Subsingleton.elim (x i) 0, fun i => Subsingleton.elim (x' i) 0, hB]
  have : {t : EReal | ∃ (n : ℕ) (x x' : Fin n → X), IsPosHerm E (outer E x x') ∧
      t = (pairing B x x' : ℝ)} = {0} := by
    ext t
    constructor
    · rintro ⟨n, x, x', -, rfl⟩
      simp [hp]
    · rintro rfl
      refine ⟨0, Fin.elim0, Fin.elim0, ⟨fun _ _ => by simp [outer], fun η hη => ?_⟩, by simp [hp]⟩
      exact absurd (LinearMap.ext fun a => by simp [Subsingleton.elim a 0]) hη
  rw [phiC, this, sInf_singleton]

end PhiC

def valToEReal (t : WithTop ℚ) : EReal :=
  WithTop.recTopCoe (⊤ : EReal) (fun q : ℚ => (((q : ℝ)) : EReal)) t

def ValuationStep_vw : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Module (𝓞 E) D.toPre.X],
      IsBalanced E (fun χ χ' : D.toPre.X => (bOf D.toPre Q χ χ' : ℝ)) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (r₁ R : ℕ), 2 ≤ r₁ → 1 ≤ R → r₁ ∣ R →
    ∀ (r : ℕ) (y : Fin r → D.toPre.X), GenMod E r₁ y →
    ∀ (s : Fin r → Fam D.toPre F (R ^ 2)) (w : Fin r → F),
      (∀ b, NuGe D Q F v (R ^ 2) (s b) 0) →
      (∀ b, ∀ α : D.toPre.X, (∀ z : D.toPre.X, α ≠ y b + R • z) → ∀ j, ((s b).s α).f j = 0) →
      (∀ b, ValAt0 D F v (R ^ 2) (s b) (w b)) →
      phiC E (fun χ χ' : D.toPre.X => (bOf D.toPre Q χ χ' : ℝ)) / (((R : ℝ) ^ 2 : ℝ) : EReal) ≤
        valToEReal (∑ b, v (w b))

def PointStep : Prop := LatticeStep ∧ ValuationStep_vw

end GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement
