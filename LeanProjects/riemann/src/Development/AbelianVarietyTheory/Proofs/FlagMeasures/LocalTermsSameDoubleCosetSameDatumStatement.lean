import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermsSameDoubleCosetSameDatum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTerms_same_doubleCoset_same_datum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (t₁ t₂ : Term V M r), H.IsTerm t₁ → H.IsTerm t₂ → t₂.abelian₂ = t₁.abelian₂ → t₂.T = t₁.T → t₂.T' = t₁.T' → ∀ n ∈ NU H t₁.f, ∀ m ∈ NU H t₁.f', img (n * m) t₁.abelian₂ = t₁.abelian₂ → Tri E t₁.f t₂.f → Tri E (fun b => (n * m) (t₁.f' b)) t₂.f' → (M.split ≠ none → ∀ x' ∈ t₁.abelian₂, ∀ x ∈ t₁.abelian₂, x' ∈ H.perp (H.X t₁.f') → x ∈ H.perp (H.X t₁.f) → (Cong H t₁.abelian₂ t₁.f t₁.f' (x - x') ↔ Cong H t₁.abelian₂ t₂.f t₂.f' (x - (n * m) x'))) → ∀ d : Datum P, Over P d t₁ → Over P d t₂ := by
  first | exact @GlobalTheory.LocOver.SameDC.same_datum | exact GlobalTheory.LocOver.SameDC.same_datum | (intros; apply GlobalTheory.LocOver.SameDC.same_datum <;> assumption)
