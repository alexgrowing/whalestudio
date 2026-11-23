import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ColumnAvoidanceConditions

noncomputable section

namespace GlobalTheory.ColPeriodCompare

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Mem

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]

def unramOff (S : Set ℕ) (v : HeightOneSpectrum (𝓞 F)) : Subgroup (Chr F E L) :=
  ⟨⟨⟨fun x => ∀ t : Set (Chr F E L), (∃ K : Subgroup (Chr F E L), (fun y => ∀ t' : Set (Chr F E L),
      (∃ _ : (∃ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v) = K), (K : Set (Chr F E L)) = t') → t' y) = t) → t x,
    (⨅ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v)).mul_mem'⟩, (⨅ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v)).one_mem'⟩,
    (⨅ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v)).inv_mem'⟩

def IsTwist (S : Set ℕ) (x : Chr F E L) : Prop :=
  x ∈ finChar F E L ⊓ kills Lˣ (idF F E).range ⊓ (⨅ v : HeightOneSpectrum (𝓞 F), kills Lˣ (wildAt E v)) ∧
    ∀ t : Set (Chr F E L), (∃ K : Subgroup (Chr F E L), (fun y => ∀ t' : Set (Chr F E L),
      (∃ _ : (∃ v, unramOff F E L S v = K), (K : Set (Chr F E L)) = t') → t' y) = t) → t x

end Mem

section Transport

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S S' : Set ℕ}
  {χ : Chr X.F X.E X.K} (h : IsTwist X.F X.E X.K S χ) (h' : IsTwist X.F X.E X.K S' χ)
  (cst : LocCst X (uSG Pr.vGs (QE sel χ))) (L : ChIdx X Pr R (QE sel χ))

end Transport

section Chain

variable (D : D7) (EX : ErrX D) (Ch : Chars (ColumnAvoidanceConditions.fieldsOf D) (ColumnAvoidanceConditions.primesOf D EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 (ColumnAvoidanceConditions.fieldsOf D).F) → HeightOneSpectrum (𝓞 (ColumnAvoidanceConditions.fieldsOf D).E)) {S S' : Set ℕ}
  (A : Amb (ColumnAvoidanceConditions.fieldsOf D)) (u : D.what₂.Word) (μ : D.what₂.Tup)

end Chain

end GlobalTheory.ColPeriodCompare
