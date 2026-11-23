import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Published

namespace Kato

section Sel

variable {l : ℕ} [Fact l.Prime] {C V : Type} [CommRing C] [Algebra ℤ_[l] C] [AddCommGroup V] [Module C V]
  [Module ℤ_[l] V] [IsScalarTower ℤ_[l] C V]

def quotRep {Γ : Type} [Group Γ] (ρ : Representation C Γ V) (T : Submodule ℤ_[l] V) (hT : ∀ g, ∀ x ∈ T, ρ g x ∈ T) :
    Representation ℤ_[l] Γ (V ⧸ T) :=
  (Loc.resCoef ℤ_[l] ρ).quotient T fun g x hx => hT g x hx

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Algebra ℚ_[l] C] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
  [ContinuousConstSMul ℤ_[l] V] (ρ : Representation C (G K Ω) V) (T : Submodule ℤ_[l] V) (hT : ∀ g, ∀ x ∈ T, ρ g x ∈ T)

structure IsSel (z : G K Ω → V ⧸ T) : Prop where
  away : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ y ∈ Z1 (ρ.comp (Dec (F := K) A).subtype),
      (∃ x : V, ∀ s : ↥(Dec (F := K) A), (s : G K Ω) ∈ Ine (F := K) A → y s = ρ s x - x) ∧
      ∃ t : V ⧸ T, ∀ s : ↥(Dec (F := K) A), z s - T.mkQ (y s) = quotRep ρ T hT s t - t
  above : ∀ τ : K →+* Om l, ∃ j : Ω →+* Om l, j.comp (algebraMap K Ω) = τ ∧
    ∃ y ∈ Loc.finiteCocycles ((MonoidHom.snd _ _).comp (decJ K j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (decJ K j).subtype)),
      ∃ t : V ⧸ T, ∀ s : ↥(decJ K j), z s.1.1 - T.mkQ (y s) = quotRep ρ T hT s.1.1 t - t
  arch : ∀ (j : Ω →+* ℂ) (s : G K Ω), (∀ x, j (s x) = starRingEnd ℂ (j x)) → ∃ t : V ⧸ T, z s = quotRep ρ T hT s t - t

def Sel : Set (H1 (quotRep ρ T hT)) :=
  {x | ∃ z : ↥(Z1 (quotRep ρ T hT)), Submodule.Quotient.mk z = x ∧ IsSel ρ T hT z.1}

end Sel

variable {l : ℕ} [Fact l.Prime]

def coefField {k : ℕ} (g : Newform k) (ι : Qbar l ≃+* ℂ) : IntermediateField ℚ_[l] (Qbar l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun n => ι.symm (g.a n))

def cycE (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (E : IntermediateField ℚ_[l] (Qbar l)) : G F Ω →* (↥E)ˣ :=
  (Units.map (algebraMap ℤ_[l] ↥E : ℤ_[l] →* ↥E)).comp (cycZ F Ω l)

def toBar {Γ : Type} [Group Γ] {n : ℕ} {E : IntermediateField ℚ_[l] (Qbar l)} (r : Γ →* GL (Fin n) ↥E) :
    Γ →* GL (Fin n) (Qbar l) :=
  (Matrix.GeneralLinearGroup.map (algebraMap ↥E (Qbar l))).comp r

structure IsLat {Γ : Type} [Group Γ] {n : ℕ} {E : IntermediateField ℚ_[l] (Qbar l)} (r : Γ →* GL (Fin n) ↥E)
    (T : Submodule ℤ_[l] (Fin n → ↥E)) : Prop where
  fg : T.FG
  span : Submodule.span ℚ_[l] (T : Set (Fin n → ↥E)) = ⊤
  int : ∀ a : ↥E, ‖(a : Qbar l)‖ ≤ 1 → ∀ x ∈ T, a • x ∈ T
  stable : ∀ g, ∀ x ∈ T, Loc.colRep r g x ∈ T

end Kato

open Kato in

def Kato : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ), FiniteDimensional ℚ_[l] ↥(coefField g ι) ∧
    ∃ V : G ℚ Ω →* GL (Fin 2) ↥(coefField g ι), Continuous V ∧ g.Att ι (toBar V) ∧
      ∀ (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] [Algebra K Ω] [IsScalarTower ℚ K Ω] (r : ℕ),
        1 ≤ r → r ≤ k - 1 → 2 * r ≠ k →
        ∀ (T : Submodule ℤ_[l] (Fin 2 → ↥(coefField g ι))) (hT : IsLat (tw V (cycE ℚ Ω (coefField g ι) ^ r)) T),
          (Sel ((Loc.colRep (tw V (cycE ℚ Ω (coefField g ι) ^ r))).comp
              (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) T (fun s => hT.stable _)).Finite

end UpperTheory.V.Published
