import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut

open Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def SAPairOne : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), IsAAOp S T v Θ →
      ∀ K ∈ smoothFormsPositiveCone S T v, ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ K ∈ smoothFormsPositiveCone S T v → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
        (∀ π, trJ S T v e K π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) →
        (∀ π, trJ S T v e (B.opApply Θ K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (B.opApply Θ K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (B.opAdj Θ J))

def SAZero : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ X ∈ smoothFormsPositiveCone S T v, ∀ y (hy : y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
        (∀ π, ((trJ S T v e X π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) ⟨y, hy⟩ = 0) →
          X (B.gq (T v).base y) = 0

def SALocal : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ → ∀ K ∈ smoothFormsPositiveCone S T v,
      ∀ V : Set (MA.E (D.parOf S v).r), IsOpen V → V ⊆ MA.Qset (D.parOf S v).r (D.parOf S v).TT → (∀ y ∈ V, K (B.gq (T v).base y) = 0) →
        ∀ y ∈ V, B.opApply Θ K (B.gq (T v).base y) = 0

def SAExh : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v, ∀ X ∈ smoothFormsPositiveCone S T v, ∀ Cs : Set (MA.E (D.parOf S v).r), IsCompact Cs → Cs ⊆ MA.Qset (D.parOf S v).r (D.parOf S v).TT →
      ∃ (F : GFn S v) (U : Set (MA.E (D.parOf S v).r)), IsOpen U ∧ Cs ⊆ U ∧ B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧
        HasCompactSupport F ∧ tsupport F ⊆ OmP S T v ∧
        ∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, (y ∈ U → B.JF (T v).base F (B.gq (T v).base y) = X (B.gq (T v).base y)) ∧
          (X (B.gq (T v).base y) = 0 → B.JF (T v).base F (B.gq (T v).base y) = 0)

def SAJCommC : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ →
      ∀ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F → HasCompactSupport F → tsupport F ⊆ OmP S T v →
      ∀ (U : Set (MA.E (D.parOf S v).r)) (X : GFn S v), IsOpen U → X ∈ smoothFormsPositiveCone S T v →
        (∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, y ∈ U → X (B.gq (T v).base y) = B.JF (T v).base F (B.gq (T v).base y)) →
        ∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, y ∈ U →
          B.opApply Θ X (B.gq (T v).base y) = B.JF (T v).base (B.opApply Θ F) (B.gq (T v).base y) ∧
          B.opAdj Θ X (B.gq (T v).base y) = B.JF (T v).base (B.opAdj Θ F) (B.gq (T v).base y)

def CompactSupportClassMembership : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ →
      ∀ F F' : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F → HasCompactSupport F → tsupport F ⊆ OmP S T v →
        B.CkOn ⊤ (B.GV S.G.k S.G.r) F' → HasCompactSupport F' → tsupport F' ⊆ OmP S T v →
        B.InCC (B.AB S.G.k S.G.r) 5 F ∧ B.InCC (B.AB S.G.k S.G.r) 5 F' ∧
          B.InCC (B.AB S.G.k S.G.r) 5 (B.opApply Θ F) ∧ B.InCC (B.AB S.G.k S.G.r) 5 (B.opAdj Θ F') ∧
          B.beta (T v).base (B.opApply Θ F) F' = B.beta (T v).base F (B.opAdj Θ F')

theorem sAPairL_of_one (hF : JAFFStable) (h1 : SAPairOne) : SAPairL := by
  obtain ⟨C1, hF'⟩ := hF
  obtain ⟨C2, h1'⟩ := h1
  refine ⟨max C1 C2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he Θs hΘs K hK J hJ hKt
  have hB1 : BuiltOW C1 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_left _ _) hB.1, hB.2⟩
  have hB2 : BuiltOW C2 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_right _ _) hB.1, hB.2⟩
  have stab := hF' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v
  have hmem : ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      applyL S v Θs K ∈ smoothFormsPositiveCone S T v := by
    intro Θs
    induction Θs with
    | nil => intro _; exact hK
    | cons Θ Θs ih =>
      intro h
      exact (stab Θ (h Θ (by simp)) _ (ih fun Θ' hΘ' => h Θ' (by simp [hΘ']))).1
  have key : ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      ∀ J ∈ smoothFormsPositiveCone S T v,
        (∀ π, trJ S T v e (applyL S v Θs K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (applyL S v Θs K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (adjL S v Θs J)) := by
    intro Θs
    induction Θs with
    | nil => intro _ J _; exact ⟨hKt, rfl⟩
    | cons Θ Θs ih =>
      intro h J hJ
      have hΘ : IsAAOp S T v Θ := h Θ (by simp)
      have hrest : ∀ Θ' ∈ Θs, IsAAOp S T v Θ' := fun Θ' hΘ' => h Θ' (by simp [hΘ'])
      have hX := hmem Θs hrest
      obtain ⟨ihT, ihE⟩ := ih hrest (B.opAdj Θ J) (stab Θ hΘ J hJ).2
      obtain ⟨hT, hE⟩ := h1' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e he Θ hΘ (applyL S v Θs K) hX J hJ
        (stab Θ hΘ _ hX).1 (stab Θ hΘ J hJ).2 ihT
      exact ⟨hT, hE.trans ihE⟩
  exact key Θs hΘs J hJ

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
