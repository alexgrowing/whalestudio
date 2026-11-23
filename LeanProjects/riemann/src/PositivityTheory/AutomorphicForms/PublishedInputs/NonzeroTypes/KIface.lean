import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
  {w : HeightOneSpectrum (𝓞 E)}

theorem hsm (h : IsPlaceOver A w) {n : ℕ} (χ : Fin n → Dec (F := E) A →* ℂˣ)
    (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A))) :
    ∀ i, GlobalTheory.WeilDeligne.IsSmooth ((χ i).comp (Subgroup.inclusion (Weil_le_Dec h))) := fun i =>
  (ho i).preimage (continuous_inclusion (Ine_le_Dec A))

abbrev xOf (h : IsPlaceOver A w) {n : ℕ} (χ : Fin n → Dec (F := E) A →* ℂˣ)
    (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A))) : WD h :=
  WD.mk (WDRep.ofChars h _ (hsm h χ ho))

def Cond (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h) {n : ℕ} (χ : Fin n → Dec (F := E) A →* ℂˣ)
    (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A))) (π : SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  (rc (IrrGL.of π.ρ π.smooth π.irred)).mono0 ∧ ∀ s : ↥(Ine (F := E) A),
    (rc (IrrGL.of π.ρ π.smooth π.irred)).charPol (ineIncl h s) = (xOf h χ ho).charPol (ineIncl h s)

def NZ : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ) (χ : Fin n → Dec (F := E) A →* ℂˣ) (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A))),
      ∃ (d : ℕ) (ξ : Representation ℂ ↥(GlobalTheory.LFun.KGL w n) (Fin d → ℂ)), ξ.IsIrreducible ∧ GlobalTheory.PRep.IsSmooth ξ ∧
        ∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)),
          (∃ f : (Fin d → ℂ) →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ k v, f (ξ k v) = π.ρ k (f v)) ↔ Cond h rc χ ho π

def TypeData : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ) (χ : Fin n → Dec (F := E) A →* ℂˣ) (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A))),
      ∃ (J : Subgroup ↥(GlobalTheory.LFun.KGL w n)) (lam : ↥J →* ℂˣ) (m : ℕ) (V0 : Representation ℂ ↥(GlobalTheory.LFun.KGL w n) (Fin m → ℂ))
        (v0 : Fin m → ℂ), IsOpen (J : Set ↥(GlobalTheory.LFun.KGL w n)) ∧ IsOpen (lam.ker : Set ↥J) ∧ GlobalTheory.PRep.IsSmooth V0 ∧
        v0 ≠ 0 ∧ (∀ j : ↥J, V0 (j : ↥(GlobalTheory.LFun.KGL w n)) v0 = ((lam j : ℂˣ) : ℂ) • v0) ∧
        (∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)),
          (∃ x : π.V, x ≠ 0 ∧ ∀ j : ↥J, π.ρ ((j : ↥(GlobalTheory.LFun.KGL w n)) : GL (Fin n) (w.adicCompletion E)) x = ((lam j : ℂˣ) : ℂ) • x) →
            Cond h rc χ ho π) ∧
        ∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)), Cond h rc χ ho π →
          ∃ f : (Fin m → ℂ) →ₗ[ℂ] π.V, Function.Injective f ∧ ∀ k v, f (V0 k v) = π.ρ k (f v)

end UpperTheory.NonzeroTypeTheory
