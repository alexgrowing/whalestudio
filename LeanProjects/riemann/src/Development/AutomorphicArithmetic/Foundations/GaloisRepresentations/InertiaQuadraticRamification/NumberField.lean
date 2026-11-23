import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def Fixes {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Field K] [Algebra K Ω] (g : G F Ω) : Prop :=
  ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x

def fixGrp (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Field K] [Algebra K Ω] : Subgroup (G F Ω) where
  carrier := {g | Fixes K g}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb x => by rw [AlgEquiv.mul_apply, hb x, ha x]
  inv_mem' := fun {a} ha x => by
    have := congrArg (a⁻¹ : G F Ω) (ha x)
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at this
    exact this.symm

theorem mem_fixGrp {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {K : Type} [Field K] [Algebra K Ω] {g : G F Ω} :
    g ∈ fixGrp F Ω K ↔ Fixes K g := Iff.rfl

structure Good {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (H : Subgroup (G F Ω)) : Prop where
  isOpen : IsOpen (H : Set (G F Ω))
  comm : commutator (G F Ω) ≤ H
  real : ∀ (j : Ω →+* ℂ) (c : G F Ω), (∀ x, j (c x) = starRingEnd ℂ (j x)) → c ∈ H

theorem Good.top {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] : Good (⊤ : Subgroup (G F Ω)) :=
  ⟨isOpen_univ, le_top, fun _ _ _ => trivial⟩

theorem Good.inf {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {H H' : Subgroup (G F Ω)} (h : Good H) (h' : Good H') :
    Good (H ⊓ H') :=
  ⟨h.isOpen.inter h'.isOpen, le_inf h.comm h'.comm, fun j c hc => ⟨h.real j c hc, h'.real j c hc⟩⟩

theorem Good.mono {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {H H' : Subgroup (G F Ω)} (hle : H ≤ H') (h : Good H) :
    Good H' :=
  ⟨Subgroup.isOpen_mono hle h.isOpen, h.comm.trans hle, fun j c hc => hle (h.real j c hc)⟩

structure Fld (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] where
  K : Type
  [field : Field K]
  [numberField : NumberField K]
  [isCM : IsCMField K]
  [algE : Algebra E K]
  [algΩ : Algebra K Ω]
  [tower : IsScalarTower E K Ω]
  [closure : IsAlgClosure K Ω]
  [abelian : IsAbelianGalois E K]

attribute [instance] Fld.field Fld.numberField Fld.isCM Fld.algE Fld.algΩ Fld.tower Fld.closure Fld.abelian

section

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

variable (E Ω) in

def Fld.base : Fld E Ω := { K := E }

instance : Inhabited (Fld E Ω) := ⟨Fld.base E Ω⟩

def SplitsIn (Ω : Type) [Field Ω] [Algebra E Ω] (K : Type) [Field K] [Algebra K Ω] (u : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g ∧ Fixes K g

def Layer (S : Set (HeightOneSpectrum (𝓞 E))) (X Y : Fld E Ω) : Prop :=
  ∃ (_ : Algebra X.K Y.K) (_ : IsScalarTower E X.K Y.K) (_ : IsScalarTower X.K Y.K Ω), IsGalois X.K Y.K ∧
    (Module.finrank X.K Y.K).Prime ∧ ∃ u ∉ S, SplitsIn Ω X.K u ∧
      ∃ A : ValuationSubring Ω, IsPlaceOver A u ∧ ∃ τ ∈ Ine (F := X.K) A, ¬ Fixes Y.K τ

def Tower (S : Set (HeightOneSpectrum (𝓞 E))) (X : Fld E Ω) : Prop :=
  Relation.ReflTransGen (Layer S) (Fld.base E Ω) X

theorem Tower.base (S : Set (HeightOneSpectrum (𝓞 E))) : Tower S (Fld.base E Ω) := Relation.ReflTransGen.refl

theorem Tower.step {S : Set (HeightOneSpectrum (𝓞 E))} {X Y : Fld E Ω} (h : Tower S X) (h' : Layer S X Y) : Tower S Y :=
  Relation.ReflTransGen.tail h h'

theorem Layer.mono {S S' : Set (HeightOneSpectrum (𝓞 E))} (hS : S ⊆ S') {X Y : Fld E Ω} (h : Layer S' X Y) : Layer S X Y := by
  obtain ⟨a, b, c, h1, h2, u, hu, h3⟩ := h
  exact ⟨a, b, c, h1, h2, u, fun h => hu (hS h), h3⟩

theorem Tower.mono {S S' : Set (HeightOneSpectrum (𝓞 E))} (hS : S ⊆ S') {X : Fld E Ω} (h : Tower S' X) : Tower S X := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih => exact Relation.ReflTransGen.tail ih (Layer.mono hS h2)

theorem Tower.induction {S : Set (HeightOneSpectrum (𝓞 E))} {P : Fld E Ω → Prop} (h0 : P (Fld.base E Ω))
    (hs : ∀ X Y, Tower S X → Layer S X Y → P X → P Y) {X : Fld E Ω} (h : Tower S X) : P X := by
  induction h with
  | refl => exact h0
  | tail h1 h2 ih => exact hs _ _ h1 h2 ih

def Cuts (X : Fld E Ω) (H : Subgroup (G (maximalRealSubfield E) Ω)) : Prop :=
  ∀ g : G E Ω, Fixes X.K g ↔ AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g ∈ H

end

def FreshChar : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)),
    IsOpen (U : Set (G F Ω)) → ∀ T : Set (HeightOneSpectrum (𝓞 F)), T.Finite → ∀ n : ℕ, 0 < n →
    ∃ ψ : G F Ω →* ℂˣ, Good ψ.ker ∧ ψ ^ n = 1 ∧
      (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := F) A, ψ g = 1) ∧
      ∃ u ∉ T, (normV u).Prime ∧ (∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := F) A ≤ U ∧
          ∃ τ ∈ Ine (F := F) A, orderOf (ψ τ) = n) ∧
        ∀ (t : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A t → ((normV u : ℕ) : 𝓞 F) ∉ t.asIdeal →
          ∀ τ ∈ Ine (F := F) A, ψ τ = 1

def OneLayer : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (p : ℕ), p.Prime →
    ∀ (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → ∀ T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), T.Finite →
    ∃ Y : Fld E Ω, Layer S (Fld.base E Ω) Y ∧ Module.finrank E Y.K = p ∧
      Good (fixGrp (maximalRealSubfield E) Ω (maximalRealSubfield Y.K)) ∧
      ∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := maximalRealSubfield E) A,
        Fixes (maximalRealSubfield Y.K) g

def FieldTop : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (H : Subgroup (G (maximalRealSubfield E) Ω)), Good H →
    ∀ (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → ∀ T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), T.Finite →
    ∃ X : Fld E Ω, Tower S X ∧ Good (fixGrp (maximalRealSubfield E) Ω (maximalRealSubfield X.K)) ∧ ∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t →
      ∀ g ∈ Dec (F := maximalRealSubfield E) A, (Fixes (maximalRealSubfield X.K) g ↔ g ∈ H)

def LocalTop : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ι : Type) [Finite ι]
    (v : ι → HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (A : ι → ValuationSubring Ω), Function.Injective v →
    (∀ i, IsPlaceOver (A i) (v i)) → ∀ V : ∀ i, Subgroup (Dec (F := maximalRealSubfield E) (A i)),
    (∀ i, IsOpen (V i : Set (Dec (F := maximalRealSubfield E) (A i)))) →
    (∀ i, commutator (Dec (F := maximalRealSubfield E) (A i)) ≤ V i) →
    ∀ T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), T.Finite → (∀ i, v i ∉ T) →
    ∀ (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) →
    ∃ X : Fld E Ω, Tower S X ∧ Good (fixGrp (maximalRealSubfield E) Ω (maximalRealSubfield X.K)) ∧
      GlobalTheory.AboveL.SolvDisj X.K N ∧
      (∀ i (g : Dec (F := maximalRealSubfield E) (A i)),
        Fixes (maximalRealSubfield X.K) (g : G (maximalRealSubfield E) Ω) ↔ g ∈ V i) ∧
      ∀ t ∈ T, ∀ B : ValuationSubring Ω, IsPlaceOver B t → ∀ g ∈ Dec (F := maximalRealSubfield E) B,
        Fixes (maximalRealSubfield X.K) g

def UnrTop : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (W : Set (HeightOneSpectrum (𝓞 E))), W.Finite → (∀ w ∈ W, SplitsIn Ω E w) →
    ∀ d : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ, (∀ t, 0 < d t) →
    ∀ T : Set (HeightOneSpectrum (𝓞 E)), T.Finite →
    (∀ w ∈ W, ∀ u ∈ T, w.under (𝓞 (maximalRealSubfield E)) ≠ u.under (𝓞 (maximalRealSubfield E))) →
    ∀ (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) →
    ∃ X : Fld E Ω, Tower S X ∧ GlobalTheory.AboveL.SolvDisj X.K N ∧
      (∀ w ∈ W, ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ τ ∈ Ine (F := E) A, Fixes X.K τ) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' →
          normV w' = normV w ^ d (w.under (𝓞 (maximalRealSubfield E)))) ∧
      ∀ u ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ g ∈ Dec (F := E) A, Fixes X.K g

def RealSpan : Prop :=
  ∀ (E M Ω F : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Field Ω] [Field F]
    [Algebra E M] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] [Algebra F Ω] (g : G F Ω),
    Fixes E g → Fixes (maximalRealSubfield M) g → Fixes M g

def StaySplit : Prop :=
  ∀ (E M Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Field Ω]
    [Algebra E M] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] (A : ValuationSubring Ω),
    ((∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g) → ∀ g ∈ Dec (F := maximalRealSubfield M) A, Fixes M g) ∧
    ((∀ g ∈ Ine (F := maximalRealSubfield E) A, Fixes E g) → ∀ g ∈ Ine (F := maximalRealSubfield M) A, Fixes M g)

def NormRam : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsGalois K M], (Module.finrank K M).Prime →
    ∀ η : HChar K, IsNormChar M η → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v →
    (∃ τ ∈ Ine (F := K) A, ¬ Fixes M τ) → ¬ η.UnrAt v

def NoSelfTwist : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [Field Ω] [Algebra K M]
    [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsGalois K M], (Module.finrank K M).Prime →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (∃ τ ∈ Ine (F := K) A, ¬ Fixes M τ) →
    ∀ a : ℕ, 1 ≤ a → ∀ (π : CG K a) (B : Multiset ℂˣ), π.HasSat v B → ∀ η : HChar K, IsNormChar M η → π.twist η ≠ π

def SplitIso : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 M)), IsPlaceOver A v → IsPlaceOver A w → (∀ g ∈ Dec (F := K) A, Fixes M g) →
    ∃ i : v.adicCompletion K ≃+* w.adicCompletion M, Continuous i ∧
      (∀ x : K, i (algebraMap K _ x) = algebraMap M _ (algebraMap K M x)) ∧ ∀ x, Valued.v (i x) = Valued.v x

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
