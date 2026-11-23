import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial
open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def stdForm (x y : Fin n → E) : E := ∑ j, x j * IsCMField.complexConj E (y j)

def stdMod (E : Type) [Field E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

structure Lat (E : Type) [Field E] (n : ℕ) where
  L : Submodule (𝓞 E) (Fin n → E)
  fg : L.FG
  span_top : Submodule.span E (L : Set (Fin n → E)) = ⊤

omit [NumberField E] [IsCMField E] in
theorem mem_stdMod {x : Fin n → E} : x ∈ stdMod E n ↔ ∀ j, ∃ a : 𝓞 E, (a : E) = x j := by
  simp only [stdMod, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]

omit [NumberField E] [IsCMField E] in
theorem single_mem_stdMod (j : Fin n) : (Pi.single j 1 : Fin n → E) ∈ stdMod E n := by
  rw [mem_stdMod]
  intro i
  by_cases h : i = j
  · subst h
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

def Lat.std (E : Type) [Field E] (n : ℕ) : Lat E n where
  L := stdMod E n
  fg := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  span_top := by
    classical
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    simpa using single_mem_stdMod j

def Lat.inter (Λ : Lat E n) : Submodule (𝓞 E) (Fin n → E) := stdMod E n ⊓ Λ.L

def Lat.SelfDual (Λ : Lat E n) : Prop :=
  ∀ x : Fin n → E, x ∈ Λ.L ↔ ∀ y ∈ Λ.L, ∃ a : 𝓞 E, (a : E) = stdForm x y

def EqAtPrime (p : ℕ) (L₁ L₂ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  (∀ x ∈ L₁, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ L₂) ∧ ∀ x ∈ L₂, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ L₁

def Lat.StdAt (Λ : Lat E n) (s : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ s → EqAtPrime p Λ.L (stdMod E n)

def mulStd (E : Type) [Field E] (n N : ℕ) : Submodule (𝓞 E) (Fin n → E) := (N : 𝓞 E) • stdMod E n

def Lat.Admissible (Λ : Lat E n) (M N : ℕ) : Prop :=
  Odd N ∧ M ∣ N ∧ mulStd E n N ≤ Λ.inter

def Lat.cardCenterZero (Λ : Lat E n) (r N : ℕ) : ℕ :=
  (mulStd E n N).toAddSubgroup.relIndex Λ.inter.toAddSubgroup ^ r

def Lat.cardZ (Λ : Lat E n) (r N : ℕ) : ℕ :=
  (mulStd E n N).toAddSubgroup.relIndex Λ.L.toAddSubgroup ^ r

def halfPart {H : Host E} (l : Level H) (N : ℕ) : Ideal (𝓞 E) :=
  ⨅ k : ℕ, Ideal.span {(N : 𝓞 E)} ⊔ l.Mb ^ k

def IsUnitary (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop := ∀ x y, stdForm (γ x) (γ y) = stdForm x y

def Lat.map (Λ : Lat E n) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Lat E n where
  L := Λ.L.map (γ.toLinearMap.restrictScalars (𝓞 E))
  fg := Λ.fg.map _
  span_top := by
    have h : ((Λ.L.map (γ.toLinearMap.restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
        γ.toLinearMap '' (Λ.L : Set (Fin n → E)) := rfl
    rw [h, ← Submodule.map_span, Λ.span_top, Submodule.map_top, LinearEquiv.range]

def Lat.InGenus (Λ : Lat E n) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
    IsUnitary γ ∧ EqAtPrime p Λ.L ((Lat.std E n).map γ).L

section Poly

variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

def letter (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (b : Fin n → E) : MvPolynomial (LtN Dw n) c.F :=
  ∑ j, C (embF c σ (b j)) * X ⟨σ, i, j⟩

def symLat (Λ : Lat E n) : Subalgebra (integralClosure ℤ c.F) (MvPolynomial (LtN Dw n) c.F) :=
  Algebra.adjoin (integralClosure ℤ c.F) {P | ∃ σ i, ∃ b ∈ Λ.L, P = letter Dw c σ i b}

def harmSpace (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (MvPolynomial (LtN Dw n) c.F) :=
  HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)

def harmLat (a : (E →+* ℂ) × ℕ → ℕ) (Λ : Lat E n) : Set (MvPolynomial (LtN Dw n) c.F) :=
  {P | P ∈ harmSpace Dw c a n ∧ P ∈ symLat Dw c Λ}

def push (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ => letter Dw c ℓ.1 ℓ.2.1 (γ (Pi.single ℓ.2.2 1))

def HarmLatFGFull : Prop :=
  ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (Λ : Lat E n),
    (∃ S : Submodule (integralClosure ℤ c.F) (MvPolynomial (LtN Dw n) c.F),
      S.FG ∧ (S : Set (MvPolynomial (LtN Dw n) c.F)) = harmLat Dw c a Λ) ∧
    ∀ P ∈ harmSpace Dw c a n, ∃ k : ℕ, 0 < k ∧ k • P ∈ harmLat Dw c a Λ

def HarmLatStd : Prop :=
  ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), harmLat Dw c a (Lat.std E n) = harmA c a n

def HarmLatPush : Prop :=
  ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (Λ : Lat E n) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)), IsUnitary γ →
    push Dw c γ '' harmLat Dw c a Λ = harmLat Dw c a (Λ.map γ)

abbrev TorsSq (n N : ℕ) : Type :=
  Fin n → Dw.La ⧸ (Ideal.span {(N : 𝓞 E) ^ 2} • (⊤ : Submodule (𝓞 E) Dw.La))

def killed (N : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hN : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ L) :
    Set (TorsSq Dw n N) :=
  {t | ∀ μ : L →ₗ[𝓞 E] (Fin n → 𝓞 E), ∀ i, ∑ j, μ ⟨_, hN j⟩ i • t j = 0}

def CardZClaim : Prop :=
  ∀ (n M N : ℕ) (Λ : Lat E n), Λ.SelfDual → Λ.Admissible M N →
    ∀ (h₀ : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ Λ.inter) (h : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ Λ.L),
      Nat.card (killed Dw N Λ.inter h₀) = Λ.cardCenterZero (Dw.p + Dw.q) N ∧
      Nat.card (killed Dw N Λ.L h) = Λ.cardZ (Dw.p + Dw.q) N ∧
      0 < Λ.cardCenterZero (Dw.p + Dw.q) N ∧ 0 < Λ.cardZ (Dw.p + Dw.q) N

end Poly

def GenusIffSelfDual (_H : Host E) : Prop := ∀ (n : ℕ) (Λ : Lat E n), Λ.InGenus ↔ Λ.SelfDual

def AdmissibleExists {H : Host E} (l : Level H) : Prop :=
  ∀ (n s : ℕ) (Λ : Lat E n), Λ.StdAt (2 * s) → s.Coprime l.M → ∃ N, Λ.Admissible l.M N ∧ N.Coprime s

def Lat.IsMarking (Λ : Lat E n) (I : Ideal (𝓞 E)) (φ : Λ.L →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ I)) : Prop :=
  Function.Surjective φ ∧ LinearMap.ker φ = I • (⊤ : Submodule (𝓞 E) Λ.L)

def RepresentativeExists {H : Host E} (l : Level H) : Prop :=
  ∀ (n s N : ℕ) (Λ : Lat E n) (φ : Λ.L →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ halfPart l N)), s ≠ 0 → N ≠ 0 → Λ.InGenus →
    Λ.IsMarking (halfPart l N) φ →
    ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E), IsUnitary γ ∧ (Λ.map γ).StdAt (s * l.M) ∧
      ∀ (x : Λ.L) (y : Fin n → 𝓞 E), (∀ j, γ x j = (y j : E)) → ∀ j, φ x j = Ideal.Quotient.mk _ (y j)

def ClassesFinite {H : Host E} (l : Level H) : Prop :=
  ∀ (n N : ℕ), N ≠ 0 →
    ∃ T : Set (Σ Λ : Lat E n, Λ.L →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ halfPart l N)), T.Finite ∧
      ∀ (Λ : Lat E n) (φ : Λ.L →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ halfPart l N)), Λ.InGenus → Λ.IsMarking (halfPart l N) φ →
        ∃ t ∈ T, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E), IsUnitary γ ∧ (Λ.map γ).L = t.1.L ∧
          ∀ (x : Λ.L) (y : t.1.L), γ x = y → φ x = t.2 y

theorem std_selfDual : (Lat.std E n).SelfDual := by
  intro x
  change x ∈ stdMod E n ↔ ∀ y ∈ stdMod E n, _
  constructor
  · intro hx y hy
    rw [mem_stdMod] at hx hy
    choose a ha using hx
    choose b hb using hy
    refine ⟨∑ j, a j * IsCMField.ringOfIntegersComplexConj E (b j), ?_⟩
    simp [stdForm, ← ha, ← hb]
  · intro h
    rw [mem_stdMod]
    intro j
    obtain ⟨a, ha⟩ := h _ (single_mem_stdMod j)
    refine ⟨a, ?_⟩
    rw [ha]
    simp [stdForm, Pi.single_apply, apply_ite]

omit [NumberField E] [IsCMField E] in
theorem std_stdAt (s : ℕ) : (Lat.std E n).StdAt s := by
  intro p hp _
  have h1 : ¬ p ∣ 1 := fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
  exact ⟨fun x hx => ⟨1, h1, by rw [one_smul]; exact hx⟩, fun x hx => ⟨1, h1, by rw [one_smul]; exact hx⟩⟩

theorem std_admissible {H : Host E} (l : Level H) : (Lat.std E n).Admissible l.M l.M := by
  refine ⟨l.odd, dvd_rfl, ?_⟩
  intro x hx
  change x ∈ stdMod E n ⊓ stdMod E n
  rw [inf_idem]
  rw [mulStd, Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (stdMod E n).smul_mem _ hy

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
