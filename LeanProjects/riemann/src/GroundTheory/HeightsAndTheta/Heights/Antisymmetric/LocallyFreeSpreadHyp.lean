import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Antisym

open MvPolynomial

section Antisymmetric

abbrev Poly (T : Type) (N : ℕ) := MvPolynomial (T × Fin N) ℝ

def SameBlock {N : ℕ} (j : ℕ) (a b : Fin N) : Prop := (a.val < j ↔ b.val < j)

def IsLeviPerm {T : Type} {N : ℕ} (j : ℕ) (w : Equiv.Perm (T × Fin N)) : Prop :=
  ∀ τ i, (w (τ, i)).1 = τ ∧ SameBlock j (w (τ, i)).2 i

def IsSimpleTransp {T : Type} [DecidableEq T] {N : ℕ} (j : ℕ) (s : Equiv.Perm (T × Fin N)) : Prop :=
  ∃ (τ : T) (a b : Fin N), b.val = a.val + 1 ∧ SameBlock j a b ∧ s = Equiv.swap (τ, a) (τ, b)

def delta (T : Type) [Fintype T] (N : ℕ) : Poly T N :=
  ∏ τ : T, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b))

def deltaDeg (T : Type) [Fintype T] (N : ℕ) : ℕ := Fintype.card T * (N * (N - 1) / 2)

def antiSpace (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) : Set (Poly T N) :=
  {P | P.IsHomogeneous (deltaDeg T N + 1) ∧
    ∀ s : Equiv.Perm (T × Fin N), IsSimpleTransp j s → rename s P = -P}

def invForms (T : Type) (N j : ℕ) : Set (Poly T N) :=
  {l | l.IsHomogeneous 1 ∧ ∀ w : Equiv.Perm (T × Fin N), IsLeviPerm j w → rename w l = l}

def IsCross {N : ℕ} (j : ℕ) (a b : Fin N) : Prop := a.val < j ∧ j ≤ b.val

def hyperplane {T : Type} {N : ℕ} (τ : T) (a b : Fin N) : Set (T × Fin N → ℝ) :=
  {x | x (τ, a) = x (τ, b)}

def HasRelInterior {T : Type} [Fintype T] {N : ℕ} (H S : Set (T × Fin N → ℝ)) : Prop :=
  ∃ p ∈ S, ∃ ε > 0, H ∩ Metric.ball p ε ⊆ S

def supAbs {T : Type} {N : ℕ} (S : Set (T × Fin N → ℝ)) (P : Poly T N) : ℝ :=
  sSup ((fun x => |eval x P|) '' S)

def crossUnion {T : Type} {N : ℕ} (j : ℕ) (Om : T → Fin N → Fin N → Set (T × Fin N → ℝ)) :
    Set (T × Fin N → ℝ) :=
  ⋃ (τ : T) (a : Fin N) (b : Fin N) (_ : IsCross j a b), Om τ a b

def IsCrossFamily {T : Type} [Fintype T] {N : ℕ} (j : ℕ) (Om : T → Fin N → Fin N → Set (T × Fin N → ℝ)) : Prop :=
  ∀ τ a b, IsCross j a b → Om τ a b ⊆ hyperplane τ a b ∧ IsCompact (Om τ a b) ∧
    HasRelInterior (hyperplane τ a b) (Om τ a b)

def adjHyperplane {T : Type} {N : ℕ} (j : ℕ) (hj : 0 < j) (hjN : j < N) (τ : T) :
    Set (T × Fin N → ℝ) :=
  hyperplane τ ⟨j - 1, by omega⟩ ⟨j, hjN⟩

def IsAdjFamily {T : Type} [Fintype T] {N : ℕ} (j : ℕ) (hj : 0 < j) (hjN : j < N) (h : Poly T N)
    (K : T → Set (T × Fin N → ℝ)) : Prop :=
  ∀ τ, K τ ⊆ adjHyperplane j hj hjN τ ∧ IsCompact (K τ) ∧
    HasRelInterior (adjHyperplane j hj hjN τ) (K τ) ∧ ∀ x ∈ K τ, eval x h = 0

def AntisymDivisible.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (P : Poly T N),
    P ∈ antiSpace T N j →
    (∀ (τ : T) (a b : Fin N), IsCross j a b →
      ∃ U ⊆ hyperplane τ a b, HasRelInterior (hyperplane τ a b) U ∧ ∀ x ∈ U, eval x P = 0) →
    ∃ l ∈ invForms T N j, P = delta T N * l

def AntisymStable.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ)
    (Om : T → Fin N → Fin N → Set (T × Fin N → ℝ)), IsCrossFamily j Om →
    ∃ C : ℝ, ∀ P ∈ antiSpace T N j, ∃ l ∈ invForms T N j,
      ∀ m, |coeff m (P - delta T N * l)| ≤ C * supAbs (crossUnion j Om) P

def AntisymPerturbed.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (hj : 0 < j) (hjN : j < N) (h : Poly T N)
    (K : T → Set (T × Fin N → ℝ)), IsAdjFamily j hj hjN h K →
    ∃ C : ℝ, ∀ (P : Poly T N) (v ε : ℝ), P - v • h ∈ antiSpace T N j →
      (∀ τ, ∀ x ∈ K τ, |eval x P| ≤ ε) →
      ∃ l ∈ invForms T N j, ∀ m, |coeff m (P - v • h - delta T N * l)| ≤ C * ε

end Antisymmetric

section Gluing

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing segreJoin NefOnFibres mCoordIdeal)
open TensorProduct

variable {Ω : Type} [Field Ω]

def locPrimeTo (A : Subalgebra ℤ Ω) (p : ℕ) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ ((A : Set Ω) ∪ {u | ∃ s : ℕ, ¬ p ∣ s ∧ u = (s : Ω)⁻¹})

def invertNat (A : Subalgebra ℤ Ω) (m : ℕ) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ ((A : Set Ω) ∪ {(m : Ω)⁻¹})

def IsLocFreeLattice {E : Type} [AddCommGroup E] [Module Ω E] (B : Subalgebra ℤ Ω) (r : ℕ)
    (L : AddSubgroup E) : Prop :=
  (∀ a ∈ B, ∀ e ∈ L, a • e ∈ L) ∧
  ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ B) ∧ (∀ l, c l ∈ B) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ L) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ B) ∧ e = ∑ q, a q • b q

def LocallyFreeSpread.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ι : Type) [Fintype ι] (x : ι → Ω) (c : ι) (p r : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (L : AddSubgroup E),
    p.Prime → x c ≠ 0 → IsLocFreeLattice (locPrimeTo (chartRing ℤ x c) p) r L →
    ∃ m : ℕ, ¬ p ∣ m ∧ ∃ L' : AddSubgroup E, IsLocFreeLattice (invertNat (chartRing ℤ x c) m) r L' ∧
      ∀ e, e ∈ L ↔ ∃ s : ℕ, ¬ p ∣ s ∧ (s : Ω) • e ∈ L'

def pullLat {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] {ι κ : Type} {E : Type} [AddCommGroup E]
    [Module Ω E] (x : ι → Ω) (z : κ → Ω') (L : ι → AddSubgroup E) (q : ι × κ) :
    AddSubgroup (Ω' ⊗[Ω] E) :=
  AddSubgroup.closure {v | ∃ a ∈ chartRing ℤ (segreJoin (fun i => algebraMap Ω Ω' (x i)) z) q,
    ∃ e ∈ L q.1, v = a • ((1 : Ω') ⊗ₜ[Ω] e)}

def AddBlockPullback.Statement : Prop :=
  ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] (ι κ : Type)
    [Fintype ι] [Fintype κ] (x : ι → Ω) (z : κ → Ω') (r : ℕ) (E : Type) [AddCommGroup E]
    [Module Ω E] (B : ChartBundle ℤ x r E),
    ∃ B' : ChartBundle ℤ (segreJoin (fun i => algebraMap Ω Ω' (x i)) z) r (Ω' ⊗[Ω] E),
      ∀ q, B'.lat q = pullLat x z B.lat q

instance joinFintype {K K' : Type} {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] : ∀ k, Fintype (Sum.elim ι ι' k)
  | Sum.inl k => inferInstanceAs (Fintype (ι k))
  | Sum.inr k => inferInstanceAs (Fintype (ι' k))

def joinPt {Ω' : Type} {K K' : Type} {ι : K → Type} {ι' : K' → Type} (y : (Σ k, ι k) → Ω')
    (z : (Σ k, ι' k) → Ω') : (Σ k : K ⊕ K', Sum.elim ι ι' k) → Ω'
  | ⟨Sum.inl k, i⟩ => y ⟨k, i⟩
  | ⟨Sum.inr k, i⟩ => z ⟨k, i⟩

def AddBlockNef.Statement : Prop :=
  ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] (K K' : Type)
    [Fintype K] [Fintype K'] (ι : K → Type) (ι' : K' → Type) [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] (y : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω') (a : K → ℤ),
    NefOnFibres (mCoordIdeal y) a →
    NefOnFibres (mCoordIdeal (joinPt (fun q => algebraMap Ω Ω' (y q)) z)) (Sum.elim a 0)

end Gluing

section Inhabitants

def Vandermonde₂ : Poly Unit 3 := delta Unit 3 * X ((), 0)

def adjProd (T : Type) [Fintype T] (N j : ℕ) (hj : 0 < j) (hjN : j < N) : Poly T N :=
  ∏ τ : T, (X (τ, ⟨j - 1, by omega⟩) - X (τ, ⟨j, hjN⟩))

example : ReciprocityTheory.ChartRestriction.G.Geo.ChartBundle ℤ (fun _ : Fin 2 => (1 : ℚ)) 1 ℚ :=
  ReciprocityTheory.ChartRestriction.G.Geo.lineBundle ℤ _ 1

example : FiniteDimensional ℚ ℚ := inferInstance

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Antisym
