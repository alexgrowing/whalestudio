import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalTrilinearFormUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombinStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiHandOffAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelStepFourierJacobiPeriodLinkStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDataDistinctPlacesCommuteStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ValDbl

variable {D : D7}

theorem vac_at {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {v : Pl D}
    {f : WO S T → ℂ} (hv : P v) (h : Vac ψ S T LS LT P f) : Vac ψ S T LS LT (· = v) f := by
  have hle : latO S T (LS : Set _) (LT : Set _) (· = v) ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hz, rest⟩
    exact ⟨α, hα, fun v' hv' => hz v' (fun e => hv' (by subst e; exact hv)), rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sOp_smul {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (P : Pair k n)
    (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (c : ℂ) (φ₀ : GA D S → ℂ) :
    sOp β P q χ ε (c • φ₀) = c • sOp β P q χ ε φ₀ := by
  have h : formAt β P (c • φ₀) = c • formAt β P φ₀ := by
    funext P₁
    simp only [formAt, map_smul, Pi.smul_apply]
  simp only [sOp, h, map_smul, Pi.smul_apply]

theorem over_keep {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {p : SplitPt D k}
    {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (hstd : IsStdChar D ψ (-1))
    {α : Frame p S m'} {β : Frame p T m} {g f : WO S T → ℂ} {Φ : Matrix m m' k → ℂ}
    (h : Over ψ α β LS LT g Φ f) :
    IsThetaFunO ψ S T f ∧ ∀ v, v ≠ p.v → Vac ψ S T LS LT (· = v) g → Vac ψ S T LS LT (· = v) f := by
  have H := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p m m' ψ hstd S T α β LS LT h.1 h.2.1 g h.2.2.1).2.1 Φ f h
  exact ⟨H.1, fun v hv hg => H.2 LS LT (· = v) (fun e => hv e.symm) hg⟩

variable {ι : Type} {p : ι → SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type} [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S}
  {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

theorem overAll_nil {f f' : WO S T → ℂ} : OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {i : ι} {l : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: l) f f' ↔ ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' :=
  Iff.rfl

theorem overAll_theta (hstd : IsStdChar D ψ (-1)) (l : List ι) :
    ∀ f f', OverAll ψ α β LS LT Ψ l f f' → IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' := by
  induction l with
  | nil => intro f f' h hf; rw [overAll_nil.1 h]; exact hf
  | cons i l _ =>
    intro f f' h _
    obtain ⟨g, -, hf'⟩ := overAll_cons.1 h
    exact (over_keep hstd hf').1

theorem overAll_vac (hstd : IsStdChar D ψ (-1)) (hinj : Function.Injective fun i => (p i).v) (l : List ι) :
    ∀ f f', OverAll ψ α β LS LT Ψ l f f' → ∀ j, j ∉ l →
      Vac ψ S T LS LT (· = (p j).v) f → Vac ψ S T LS LT (· = (p j).v) f' := by
  induction l with
  | nil => intro f f' h j _ hf; rw [overAll_nil.1 h]; exact hf
  | cons i l ih =>
    intro f f' h j hj hf
    obtain ⟨g, hg, hf'⟩ := overAll_cons.1 h
    have hji : j ≠ i := fun e => hj (by simp [e])
    have hjl : j ∉ l := fun h' => hj (by simp [h'])
    exact (over_keep hstd hf').2 _ (fun e => hji (hinj e)) (ih f g hg j hjl hf)

theorem overAll_last (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (l : List ι) : l.Nodup → ∀ f f', (∀ j, Vac ψ S T LS LT (· = (p j).v) f) → OverAll ψ α β LS LT Ψ l f f' →
      ∀ i ∈ l, ∃ g, Over ψ (α i) (β i) LS LT g (Ψ i) f' ∧ ∀ j, (j = i ∨ j ∉ l) → Vac ψ S T LS LT (· = (p j).v) g := by
  induction l with
  | nil => intro _ _ _ _ _ i hi; simp at hi
  | cons j l ih =>
    intro hl f f' hf h i hi
    rw [List.nodup_cons] at hl
    obtain ⟨g₀, hg₀, hf'⟩ := overAll_cons.1 h
    by_cases hij : i = j
    · subst hij
      refine ⟨g₀, hf', fun j' hj' => ?_⟩
      have hj'l : j' ∉ l := by
        rcases hj' with rfl | hj'
        · exact hl.1
        · exact fun h' => hj' (List.mem_cons_of_mem _ h')
      exact overAll_vac hstd hinj l f g₀ hg₀ j' hj'l (hf j')
    · have hil : i ∈ l := by simpa [hij] using hi
      obtain ⟨g₁, hg₁, hv₁⟩ := ih hl.2 f g₀ hf hg₀ i hil
      have hjv : Vac ψ S T LS LT (· = (p j).v) g₁ := hv₁ j (Or.inr hl.1)
      obtain ⟨g', hg'1, hg'2⟩ := GlobalTheory.T.splitPlaceData_distinct_places_commute D k (p i) (p j) n n' n n' ψ hstd (hunit i) (hunit j)
        (fun e => hij (hinj e)) S T (α i) (β i) (α j) (β j) LS LT g₁ g₀ f' (Ψ i) (Ψ j) hjv hg₁ hf'
      refine ⟨g', hg'2, fun j' hj' => ?_⟩
      have hne : j' ≠ j := by
        rcases hj' with rfl | hj'
        · exact hij
        · exact fun e => hj' (by simp [e])
      have hj'' : j' = i ∨ j' ∉ l := by
        rcases hj' with rfl | hj'
        · exact Or.inl rfl
        · exact Or.inr fun h' => hj' (List.mem_cons_of_mem _ h')
      exact (over_keep hstd hg'1).2 _ (fun e => hne (hinj e)) (hv₁ j' hj'')

end Local

theorem contAut_hand0 {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) {φ : GA D B.A → ℂ}
    {Ξ₁ : WO B.V₀ J.W₀ → ℂ} {Ξ₂ : WO J.W₀ B'.V₀ → ℂ} (hφ : IsContAut B.A φ) (h₁ : IsThetaFunO ψ B.V₀ J.W₀ Ξ₁)
    (h₂ : IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂) : IsContAut B'.A (hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂) :=
  GlobalTheory.T.fourierJacobiHandOff_automorphic D ψ σ J B' s₂ vL _ Ξ₂ (GlobalTheory.T.bessel_level_step_fourierJacobi_period_link D ψ (σ + 1) B J s₁ B'.L B'.ζ B'.line l φ Ξ₁ hφ h₁).1 h₂

end GlobalTheory.FinPl.ValDbl
