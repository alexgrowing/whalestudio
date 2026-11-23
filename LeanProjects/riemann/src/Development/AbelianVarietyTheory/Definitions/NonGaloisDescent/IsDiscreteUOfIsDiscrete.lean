import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Formalism.L2.Host Formalism.UG
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.BCWords

section Linear

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a N c : ℕ} {n : Fin c → ℕ}

structure IsDiscreteU (V : Submodule ℂ (Sm E a)) : Prop where
  aut : ∀ φ ∈ V, IsAutForm φ
  central : ∃ s : ℝ, ∀ φ ∈ V, ∀ (t : ℝ) (g : GA E a),
    φ.1 (splitCentre E a t * g) = Complex.exp (Complex.I * s * t) * φ.1 g
  sqInt : ∀ φ ∈ V, letI : MeasurableSpace (GA E a) := borel _
    ∃ (μ : Measure (GA E a)) (𝓕 : Set (GA E a)), μ.IsHaarMeasure ∧ IsFundamentalDomain (latticeGL E a) 𝓕 μ ∧
      ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ < ⊤
  stable : IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V

theorem isDiscreteU_of_isDiscrete {V : Submodule ℂ (Sm E a)} (h : IsDiscrete V) : IsDiscreteU V :=
  ⟨h.aut, ⟨0, fun φ hφ t g => by simpa using (h.sqInt φ hφ).1 t g⟩, fun φ hφ => (h.sqInt φ hφ).2, h.stable, h.ne_bot,
    h.irred⟩

def PairedGL (V V' : Submodule ℂ (Sm E a)) (s : Op E a → Op E a) : Prop :=
  ∃ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) ∧ (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) ∧
    (∀ k (φ φ' : V) (ψ ψ' : V'), φ'.1 = act (.fin k) φ.1 → ψ'.1 = act (s (.fin k)) ψ.1 → B φ' ψ' = B φ ψ) ∧
    (∀ k (φ φ' : V) (ψ ψ' : V'), φ'.1 = act (.cpt k) φ.1 → ψ'.1 = act (s (.cpt k)) ψ.1 → B φ' ψ' = B φ ψ) ∧
    ∀ X (φ φ' : V) (ψ ψ' : V'), φ'.1 = act (.lie X) φ.1 → ψ'.1 = act (s (.lie X)) ψ.1 → B φ' ψ + B φ ψ' = 0

def tensorSp (V : ∀ i, Submodule ℂ (Sm E (n i))) : Submodule ℂ ((∀ i, GA E (n i)) → ℂ) :=
  Submodule.span ℂ {F | ∃ φ : ∀ i, V i, F = fun m => ∏ i, (φ i).1.1 (m i)}

def InInd (h : ∑ i, n i = N) (V : ∀ i, Submodule ℂ (Sm E (n i))) (φ : Sm E N) : Prop :=
  (∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, φ.1 (u * g) = φ.1 g) ∧
    φ ∈ GlobalTheory.PRep.smoothPart (finRep E N) ∧ φ ∈ finVec (cptRep E N) ∧
    ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)),
      (fun m => φ.1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈ tensorSp V

theorem inInd_iff (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (φ : Sm E N) :
    InInd h (fun i => (π i).V) φ ↔ φ ∈ indForms h π := Iff.rfl

def InNormInd (h : ∑ i, n i = N) (V : ∀ i, Submodule ℂ (Sm E (n i))) (φ : Sm E N) : Prop :=
  ∃ ν : Fin c → HChar E, (∀ i, (ν i).IsAbsPow ((modExp (fun i => Fin (n i)) i : ℝ) / 2)) ∧
    InInd h (fun i => (V i).map (mulChi (n i) (ν i)).toLinearMap) φ

structure IsInfSubquot (h : ∑ i, n i = N) (V : ∀ i, Submodule ℂ (Sm E (n i))) (W₁ W₂ : Submodule ℂ (Sm E N)) : Prop where
  lt : W₂ < W₁
  mem : ∀ φ ∈ W₁, InNormInd h V φ
  cpt : ∀ k, (∀ φ ∈ W₁, act (.cpt k) φ ∈ W₁) ∧ ∀ φ ∈ W₂, act (.cpt k) φ ∈ W₂
  lie : ∀ X, (∀ φ ∈ W₁, act (.lie X) φ ∈ W₁) ∧ ∀ φ ∈ W₂, act (.lie X) φ ∈ W₂

def QuotHasInfChar (W₁ W₂ : Submodule ℂ (Sm E N)) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = N ∧ ∀ u, ∀ φ ∈ W₁, cap τ u φ - (m.map (u + ·)).prod • φ ∈ W₂

end Linear

def diagGL {n : ℕ} (t : Fin n → ℂˣ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal fun i => (t i : ℂ), Matrix.diagonal fun i => ((t i)⁻¹ : ℂˣ), by simp, by simp⟩

def torusParam {n : ℕ} (t : Fin n → ℂˣ) (i : Fin (n / 2)) : ℂˣ :=
  t (Fin.castLE (Nat.div_le_self n 2) i) / t (Fin.castLE (Nat.div_le_self n 2) i).rev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def IsUnramBC (π : Submodule ℂ (UA E n → ℂ)) (w : HeightOneSpectrum (𝓞 E))
    (P : SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
    ∀ t : Fin n → ℂˣ, HasSatAt π w s ϖ q (torusParam t) → ∀ B : Multiset ℂˣ,
      (B.map fun z => (X - C (z : ℂ) : ℂ[X])).prod = (diagGL t * thetaGL n (RingHom.id ℂ) (diagGL t)).val.charpoly →
      GlobalTheory.LFun.HasSatGL w P.ρ B

end GlobalTheory.BCWords

end
