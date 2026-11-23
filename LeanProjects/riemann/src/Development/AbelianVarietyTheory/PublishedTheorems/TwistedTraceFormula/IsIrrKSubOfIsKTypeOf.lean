import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsKStableOnKFiniteVectors

noncomputable section

open Matrix
open Formalism.REAL (Jm Kset inG)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsKTypeOf IsDS lowKSub UJset)
open Formalism.L2.Theta (SmoothVec dRep)

namespace GlobalTheory.KFinVec

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFinSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H :=
  GlobalTheory.KFiniteVectors.kFiniteVectors ε σ

@[simp] theorem mem_kFinSub {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H} :
    v ∈ kFinSub ε σ ↔ IsKFin ε σ v := Iff.rfl

theorem isKStableOn_kFinSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (kFinSub ε σ) := by
  rintro g hg v ⟨S, hS, hv, hK⟩
  exact ⟨S, hS, hK g hg v hv, hK⟩

def IsIrrKSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ S ≠ ⊥ ∧ IsKStableOn ε σ S ∧
    ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S

def IsKMapFrom (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H)
    (T : S →ₗ[ℂ] H) : Prop :=
  ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s)

def kIsotypic (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    Submodule ℂ H :=
  ⨆ T : {T : S →ₗ[ℂ] H // IsKMapFrom ε σ S T}, LinearMap.range T.1

theorem range_le_kIsotypic {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
    {T : S →ₗ[ℂ] H} (hT : IsKMapFrom ε σ S T) : LinearMap.range T ≤ kIsotypic ε σ S :=
  le_iSup (fun T : {T : S →ₗ[ℂ] H // IsKMapFrom ε σ S T} => LinearMap.range T.1) ⟨T, hT⟩

def IsAdmissible (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H, IsIrrKSub ε σ S → FiniteDimensional ℂ (kIsotypic ε σ S)

def IsLieStable (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) : Prop :=
  ∀ X, inG ε X → ∀ v ∈ S, dRep σ X v ∈ S

theorem isIrrKSub_of_isKTypeOf {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ : Fin n → ℝ}
    {S : Submodule ℂ H} (h : IsKTypeOf ε σ Λ S) : IsIrrKSub ε σ S := by
  refine ⟨h.1, ?_, h.2.1, h.2.2.1⟩
  rintro rfl
  obtain ⟨v, hv, hv0, -⟩ := h.2.2.2.1
  exact hv0 ((Submodule.mem_bot ℂ).1 hv)

end GlobalTheory.KFinVec

namespace GlobalTheory.Published

open GlobalTheory.KFinVec

def KFiniteVectorsUnitary : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    IsAdmissible ε σ ∧
    (∀ v : H, IsKFin ε σ v → AnalyticOnUJ ε fun g => σ g v) ∧
    Dense (kFinSub ε σ : Set H) ∧
    IsLieStable ε σ (kFinSub ε σ) ∧
    ∀ S : Submodule ℂ H, S ≤ kFinSub ε σ → IsLieStable ε σ S → S = ⊥ ∨ S = kFinSub ε σ

namespace KFiniteVectorsUnitary

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem analytic [CompleteSpace H] (h : KFiniteVectorsUnitary) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : AnalyticOnUJ ε fun g => σ g v := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, analyticOnNhd_const, fun _ _ _ => Subsingleton.elim _ _⟩
  · exact (h n ε H σ hU hI).2.1 v hv

theorem smoothOnH [CompleteSpace H] (h : KFiniteVectorsUnitary) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) :
    Formalism.QuantumDeterminants.SmoothOnH (Jm ε) fun g => σ g v :=
  (h.analytic hU hI hv).smoothOnH

theorem smoothVec_conj [CompleteSpace H] (h : KFiniteVectorsUnitary) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v)
    {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hG : Pᴴ * Jm ε * P = G) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v :=
  (h.analytic hU hI hv).smoothVec hP hG

theorem smoothVec [CompleteSpace H] (h : KFiniteVectorsUnitary) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : SmoothVec {X | inG ε X} σ v := by
  have := h.smoothVec_conj hU hI hv (P := 1) (G := Jm ε) isUnit_one (by simp)
  simp only [Matrix.one_mul, inv_one, Matrix.mul_one] at this
  exact this

theorem hasDerivAt [CompleteSpace H] (h : KFiniteVectorsUnitary) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0 := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by simp [UJset, Formalism.REAL.inUJ]
  have := ((h.analytic hU hI hv).analytic_exp h1 hX 0).differentiableAt
  simp only [Matrix.one_mul] at this
  exact this.hasDerivAt

theorem of_isDS (h : KFiniteVectorsUnitary) {lam : Fin n → ℝ} (hσ : IsDS ε lam σ) :
    IsAdmissible ε σ ∧
    (∀ v : H, IsKFin ε σ v → AnalyticOnUJ ε fun g => σ g v) ∧
    Dense (kFinSub ε σ : Set H) ∧
    IsLieStable ε σ (kFinSub ε σ) ∧
    ∀ S : Submodule ℂ H, S ≤ kFinSub ε σ → IsLieStable ε σ S → S = ⊥ ∨ S = kFinSub ε σ :=
  haveI := hσ.1
  haveI := hσ.2.1
  h n ε H σ hσ.2.2.1 hσ.2.2.2.1

end KFiniteVectorsUnitary

end GlobalTheory.Published

end
