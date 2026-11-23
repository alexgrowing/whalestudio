import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateKernelCount

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Data

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V))

def NuZero (Q : D.toPre.X → ℤ) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (v : AddValuation F (WithTop ℚ)) (k : ℕ) (s : Fam D.toPre F k) : Prop :=
  NuGe D Q F v k s 0 ∧ ∀ r : ℚ, 0 < r → ¬ NuGe D Q F v k s r

def IsFrame (ϖ : V) (Q : D.toPre.X → ℤ) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (v : AddValuation F (WithTop ℚ)) (θ : Fam D.toPre F 1) : Prop :=
  NuGe D Q F v 1 θ 0 ∧
    ∃ (σ : D.toPre.SecB 1 0)
      (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F 0) (DegPre.famε 1))),
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F 0) (DegPre.famε 1) σF
        (D.toPre.famφB 0) (DegPre.famε 1) σ (DegPre.prB D.toPre F).left 1 ∧
      (∀ j, (θ.s 0).f j = σF.f j) ∧
      ¬ ∃ σ' : D.toPre.SecB 1 0, ∀ j, σ.f j = constFn D.toPre.P.A.hom _ ϖ * σ'.f j

def FiniteOrderLifts (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) : Prop :=
  ∀ p : QkPt D.toPre F k,
    ∃ (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ : F),
      w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D F k p w ζ

end Data

section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
  (P : PELUnif (maximalIdeal V) t) (F : Type) [Field F] [Algebra (FractionRing V) F]

def kerPts (a : 𝓞 E) : Set (TFK (R := V) F ⟶ P.A.A) :=
  letI := H.starRing
  {x | x ≫ P.oA.act a = 1}

def ConjKernelCount (α : 𝓞 E) (N : ℕ) : Prop :=
  (kerPts P F (H.bar α)).Finite ∧ (kerPts P F (H.bar α)).ncard = N ^ P.A.g ∧
    ∀ b ∈ kerPts P F (H.bar α), ∃ p : QkPt P.D.toPre F (1 * N), P.ToA F (1 * N) p b

def FixingLifts (α : 𝓞 E) (N : ℕ) (s₀ : Fam P.D.toPre F (1 * N)) : Prop :=
  ∀ x ∈ kerPts P F α,
    ∃ (p : QkPt P.D.toPre F (1 * N))
      (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * N))))
      (ζ : F),
      P.ToA F (1 * N) p x ∧ w.IsGen ∧ ζ ≠ 0 ∧ FinOrd P.D F (1 * N) p w ζ ∧
        ∃ s' : Fam P.D.toPre F (1 * N),
          PhiRel P.D.toPre F (1 * N) p w s₀ s' ∧ Fam.IsSmul P.D.toPre F ζ s' s₀

def PairingSeparates (α : 𝓞 E) (N : ℕ) : Prop :=
  ∀ b ∈ kerPts P F (H.bar α), ∀ b' ∈ kerPts P F (H.bar α), b ≠ b' →
    ∃ x ∈ kerPts P F α, ∃ z z' : Fˣ,
      WeilIs P.A.A P.A.L (N : ℤ) x b (unitOn z) ∧ WeilIs P.A.A P.A.L (N : ℤ) x b' (unitOn z') ∧
        z ^ N = 1 ∧ z' ^ N = 1 ∧ z ≠ z'

def TorsionFacts (α : 𝓞 E) (N : ℕ) (Q : P.D.toPre.X → ℤ) (v : AddValuation F (WithTop ℚ))
    (s₀ : Fam P.D.toPre F (1 * N)) : Prop :=
  ConjKernelCount P F α N ∧ FixingLifts P F α N s₀ ∧ PairingSeparates P F α N ∧
    (∀ k : ℕ, 1 ≤ k → FiniteOrderLifts P.D F k) ∧ NuZero P.D Q F v (1 * N) s₀

end Unif

def InWeilActionSetting
    (Φ : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
      [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)} (P : PELUnif (maximalIdeal V) t)
      (F : Type) [Field F] [Algebra (FractionRing V) F] (_ : 𝓞 E) (N : ℕ) (_ : P.D.toPre.X → ℤ)
      (_ : AddValuation F (WithTop ℚ)) (_ : Fam P.D.toPre F (1 * N)), Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    letI := H.starRing
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v →
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
        (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c))),
    ∀ θ : Fam P.D.toPre F 1, IsFrame P.D ϖ Q F v θ →
    ∀ s₀ : Fam P.D.toPre F (1 * N), PullAl P.D F P.oD α 1 N θ s₀ → Φ P F α N Q v s₀

def ConjKernelCountStatement : Prop := InWeilActionSetting fun P F _ _ α N _ _ _ => ConjKernelCount P F α N

def FixingLiftsStatement : Prop := InWeilActionSetting fun P F _ _ α N _ _ s₀ => FixingLifts P F α N s₀

def PairingSeparatesStatement : Prop := InWeilActionSetting fun P F _ _ α N _ _ _ => PairingSeparates P F α N

def FiniteOrderLiftsStatement : Prop :=
  InWeilActionSetting fun P F _ _ _ _ _ _ _ => ∀ k : ℕ, 1 ≤ k → FiniteOrderLifts P.D F k

def PullFrameNuZeroStatement : Prop := InWeilActionSetting fun P F _ _ _ N Q v s₀ => NuZero P.D Q F v (1 * N) s₀

def TorsionFactsStatement : Prop := InWeilActionSetting fun P F _ _ α N Q v s₀ => TorsionFacts P F α N Q v s₀

theorem torsionFactsStatement_iff : TorsionFactsStatement ↔
    ConjKernelCountStatement ∧ FixingLiftsStatement ∧ PairingSeparatesStatement ∧
      FiniteOrderLiftsStatement ∧ PullFrameNuZeroStatement := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      intro E _ _ _ H V _ _ _ t P hP α N h1 h2 h3 h4 ϖ h5 Q h6 F _ _ _ v h7 Dw I θ h8 s h9 <;>
      have := h E H V t P hP α N h1 h2 h3 h4 ϖ h5 Q h6 F v h7 Dw I θ h8 s h9
    exacts [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]
  · rintro ⟨a, b, c, d, e⟩ E _ _ _ H V _ _ _ t P hP α N h1 h2 h3 h4 ϖ h5 Q h6 F _ _ _ v h7 Dw I θ h8 s h9
    exact ⟨a E H V t P hP α N h1 h2 h3 h4 ϖ h5 Q h6 F v h7 Dw I θ h8 s h9,
      b E H V t P hP α N h1 h2 h3 h4 ϖ h5 Q h6 F v h7 Dw I θ h8 s h9,
      c E H V t P hP α N h1 h2 h3 h4 ϖ h5 Q h6 F v h7 Dw I θ h8 s h9,
      d E H V t P hP α N h1 h2 h3 h4 ϖ h5 Q h6 F v h7 Dw I θ h8 s h9,
      e E H V t P hP α N h1 h2 h3 h4 ϖ h5 Q h6 F v h7 Dw I θ h8 s h9⟩

example {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
    (Q : D.toPre.X → ℤ) (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ))
    (k : ℕ) : ¬ NuZero D Q F v k 0 := fun h =>
  h.2 1 one_pos fun χ => ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
    fun j => by simp⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateKernelCount
