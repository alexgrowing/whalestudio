import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

def PullRWStatement : Prop :=
  ∀ {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (h : X' → X) (hc : Continuous h)
    (L : LocPot X) (s : X → X → ℂ),
    rW (L.pullback h hc) (fun x y => s (h x) (h y)) = rW L s ∘ h ∧
      bdry (fun x y => s (h x) (h y)) = h ⁻¹' bdry s

def PullPshStatement : Prop :=
  ∀ {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h) (P : LocPot X) (U : Set X)
    (f : X → ℝ), IsOpen U → IsPotential A P →
      (A.SmoothOn U f → A'.SmoothOn (h ⁻¹' U) (f ∘ h)) ∧
      (IsPsh A P → IsPsh A' (P.pullback h hh.1)) ∧
      (A.SmoothOn U f → IsPshOn A U (P + LocPot.ofFun f) →
        IsPshOn A' (h ⁻¹' U) (P.pullback h hh.1 + LocPot.ofFun (f ∘ h)))

def PullDominateStatement : Prop :=
  ∀ {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X']
    [T2Space X'] (A : FinHolAtlas e X) (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h)
    (Θ : LocPot X) (Θ' : LocPot X'), IsPotential A Θ → IsPotential A' Θ' → IsPosPot A' Θ' →
      ∃ K : ℝ, 0 ≤ K ∧ IsPsh A' (Θ'.rsmul K + (Θ.pullback h hh.1).rsmul (-1))

def RegFamilyC2Pullback : Prop :=
  ∀ {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h) (s : X → X → ℂ) (ph : X → ℝ)
    (phT : ℝ → X → ℝ), A.SmoothOn (bdry s)ᶜ ph →
    (∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), A.Smooth (phT t)) → IsRegFamilyC2 A s ph phT →
      IsRegFamilyC2 A' (fun x y => s (h x) (h y)) (ph ∘ h) (fun t => phT t ∘ h)

end

end ReciprocityTheory.AnForm.P
