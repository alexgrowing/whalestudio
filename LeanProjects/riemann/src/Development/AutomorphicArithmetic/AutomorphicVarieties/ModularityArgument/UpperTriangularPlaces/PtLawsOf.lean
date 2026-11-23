import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

namespace UpperTheory.V.Keep

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

def LocL (T : Tower D) : Prop :=
  ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → (∃ g ∈ Ine (F := T.F) A, Raw.bar D.om (resQ T.F g) ≠ 1) ∨
      ∃ g ∈ Dec (F := T.F) A, Raw.bar D.om (resQ T.F g) = 1 ∧ T.rb wPs g = 1 ∧ T.rb wAl g ≠ 1

structure OrdAt (T : Tower D) (r : G ℚ Ω →* M4 (PadicAlgCl l)) (A : ValuationSubring Ω)
    (κ : Fin 4 → ↥(Dec (F := T.F) A) →* (PadicAlgCl l)ˣ) : Prop where
  flag : Af.IsFlagOn (r.toHomUnits.comp (resQ T.F)) (Dec (F := T.F) A) κ
  red : ∀ i s, ‖(κ i s : PadicAlgCl l) - ((chi D T.pr i (resQ T.F s) : c.Oˣ) : c.O)‖ < 1
  wts : ∃ U : Subgroup (G T.F Ω), IsOpen (U : Set (G T.F Ω)) ∧ ∀ i (s : ↥(Dec (F := T.F) A)), (s : G T.F Ω) ∈ U ⊓ Ine (F := T.F) A →
    κ i s ^ 2 = cycBar T.F Ω l s ^ (2 * (D.wts4 i : ℤ))

end

def FlagF : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), ∀ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l),
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r →
    ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ κ, OrdAt T r A κ

def InfCyc : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
    A.valuation (l : Ω) < 1 → ∀ U : Subgroup (G F Ω), IsOpen (U : Set (G F Ω)) →
      ∃ s ∈ U ⊓ Ine (F := F) A, ¬ IsOfFinOrder (cycBar F Ω l s)

def UnlF : Prop :=
  InfCyc → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → T.Ok → LocL T → ∀ (r : G ℚ Ω →* M4 (PadicAlgCl l)) (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
    ∀ κ, OrdAt T r A κ → ∀ i j, κ i ≠ κ j * (cycBar T.F Ω l).comp (Dec (F := T.F) A).subtype

def UnlL : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → T.Ok → ∀ r : G ℚ Ω →* M4 (PadicAlgCl l),
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ κ, OrdAt T r A κ ∧
      ∀ i j, κ i ≠ κ j * (cycBar T.F Ω l).comp (Dec (F := T.F) A).subtype) →
    ∀ w : HeightOneSpectrum (𝓞 T.L), ((l : ℕ) : 𝓞 T.L) ∈ w.asIdeal → Unl1 (r.toHomUnits.comp (resQ T.L)) w

def UpTri : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (M M' B : Matrix (Fin n) (Fin n) k) (d : Fin n → k), Function.Injective d →
    (∀ i j, j < i → M i j = 0) → (∀ i j, j < i → M' i j = 0) → (∀ i, M i i = d i) → (∀ i, M' i i = d i) →
    B * M = M' * B → ∀ i j, j < i → B i j = 0

def FlagQ : Prop :=
  InfCyc → UpTri → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → ∀ r : G ℚ Ω →* M4 (PadicAlgCl l),
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ κ, OrdAt T r A κ) → Flagged r.toHomUnits

def IneOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G ℚ Ω →* GL (Fin n) (PadicAlgCl l))
    (H : Subgroup (G ℚ Ω)), IsOpen (H : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ H →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, g ∈ H → r g = 1) → IneAb r

def IneQ : Prop :=
  IneOf → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l),
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → IneAb r.toHomUnits

def PtLaws : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → T.Ok → LocL T → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l),
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r →
    IneAb r.toHomUnits ∧ Flagged r.toHomUnits ∧
      ∀ w : HeightOneSpectrum (𝓞 T.L), ((l : ℕ) : 𝓞 T.L) ∈ w.asIdeal → Unl1 (r.toHomUnits.comp (resQ T.L)) w

theorem ptLaws_of (h1 : FlagF) (h2 : InfCyc) (h3 : UnlF) (h4 : UnlL) (h5 : UpTri) (h6 : FlagQ) (h7 : IneOf) (h8 : IneQ) : PtLaws := by
  intro Ω _ _ _ l _ c D T hD ho hL c' h X y hw r hr
  have f := h1 D T c' h X y hw r hr
  exact ⟨h8 h7 D T hD c' h X y hw r hr, h6 h2 h5 D T hD r f, h4 D T hD ho r fun A hA =>
    (f A hA).imp fun κ hκ => ⟨hκ, h3 h2 D T hD ho hL r A hA κ hκ⟩⟩

end UpperTheory.V.Keep
