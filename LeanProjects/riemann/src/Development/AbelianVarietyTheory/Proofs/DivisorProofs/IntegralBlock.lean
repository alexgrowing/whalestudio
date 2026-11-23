import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb

set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
open Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.ExpFrame Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachBlock

section Galois

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]

def ofOL (LL : FinExt l) : ↥(OL LL) →+* PadicAlgCl l :=
  (LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)

def IntegralBlock (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ) : Prop :=
  ∃ (LL : FinExt l) (r : G E Ω →* GL (Fin n) ↥(OL LL)) (ψ : Fin t → G E Ω →* (↥(OL LL))ˣ) (ϖ : ↥(OL LL))
    (R : ℕ) (M : Fin (R + 1) → Submodule ↥(OL LL) (Fin n → ↥(OL LL))) (rs : Fin t → Fin R),
    (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧
    CrysWith ((Matrix.GeneralLinearGroup.map (ofOL l LL)).comp r) (fun τ => Finset.univ.val.map (J τ)) ∧
    (∀ s, CrysWith (GlobalTheory.TripleGal.rk1 ((Units.map (ofOL l LL).toMonoidHom).comp (ψ s)))
      fun τ => {bot τ + ((s : ℕ) : ℤ)}) ∧
    Irreducible ϖ ∧ (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → ↥(OL LL), x = fun a => ϖ * y a) ∧ M (Fin.last R) = ⊤ ∧ Monotone M ∧
    (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) ↥(OL LL)).mulVec x ∈ M k) ∧
    Function.Injective rs ∧
    ∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧
      M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span ↥(OL LL) {x} ∧
      ∀ g, (r g : Matrix (Fin n) (Fin n) ↥(OL LL)).mulVec x - (fun a => ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)) * x a) ∈
        M (rs s).castSucc

end Galois

section Reduced

variable {F : Type} [Field F] {n : ℕ}

def lau (y : Fin n → F⟦X⟧) : Fin n → LaurentSeries F := fun a => ((y a : F⟦X⟧) : LaurentSeries F)

def phiV (l : ℕ) (P : Matrix (Fin n) (Fin n) F⟦X⟧) (y : Fin n → F⟦X⟧) : Fin n → F⟦X⟧ :=
  P.mulVec fun a => frob0 l (y a)

def gamV (un : F⟦X⟧) (D : Matrix (Fin n) (Fin n) F⟦X⟧) (y : Fin n → F⟦X⟧) : Fin n → F⟦X⟧ :=
  (1 + (X : F⟦X⟧) • D).mulVec fun a => gam0 0 un (y a)

def RedFilt {ι : Type} (σ : Equiv.Perm ι) (l : ℕ) {t : ℕ} (un : F⟦X⟧) (P D : ι → Matrix (Fin n) (Fin n) F⟦X⟧)
    (Pψ Dψ : Fin t → ι → F⟦X⟧) : Prop :=
  ∃ (R : ℕ) (V : ι → Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (rs : Fin t → Fin R)
    (e : ι → Fin t → Fin n → F⟦X⟧) (m : ι → Fin t → ℤ),
    Function.Injective rs ∧
    (∀ i, V i 0 = ⊥ ∧ V i (Fin.last R) = ⊤ ∧ Monotone (V i)) ∧
    (∀ k i j, Module.finrank (LaurentSeries F) (V i k) = Module.finrank (LaurentSeries F) (V j k)) ∧
    (∀ i k y, lau y ∈ V (σ i) k → lau (phiV l (P i) y) ∈ V i k) ∧
    (∀ i k y, lau y ∈ V i k → lau (gamV un (D i) y) ∈ V i k) ∧
    (∀ i s, lau (e i s) ∉ V i (rs s).castSucc ∧
      V i (rs s).succ = V i (rs s).castSucc ⊔ Submodule.span (LaurentSeries F) {lau (e i s)}) ∧
    (∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • lau (phiV l (P i) (e (σ i) s)) -
        (((X : F⟦X⟧) : LaurentSeries F) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i : F⟦X⟧) : LaurentSeries F)) •
          lau (e i s) ∈ V i (rs s).castSucc) ∧
    ∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • lau (gamV un (D i) (e i s)) -
        (((gamSer 0 un : F⟦X⟧) : LaurentSeries F) ^ m i s *
          ((1 + X * Dψ s i : F⟦X⟧) : LaurentSeries F)) • lau (e i s) ∈ V i (rs s).castSucc

end Reduced

end GlobalTheory.WachBlock

end
