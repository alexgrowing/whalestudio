import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.ZuckTensor
import Formalism.PeriodIntegrals.DSExist

open MeasureTheory Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

structure Fam (n : ℕ) where
  Hs : Fin n → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  σs : ∀ s, Matrix (Fin n) (Fin n) ℂ → (Hs s →L[ℂ] Hs s)

attribute [instance] Fam.nH Fam.iH Fam.cH

def Ineq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam lam' : Fin n → ℝ), vNormSq ε (lowK ε lam) ≠ vNormSq ε (lowK ε lam') →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      IsDS ε lam' σ' → ¬ ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x)

def ToSum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ F : Fam n, (∀ s, IsHCParam (μ + Pi.single s 1) → IsDS ε (μ + Pi.single s 1) (F.σs s)) →
    ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, F.Hs (sI i)),
      (∀ i, IsHCParam (μ + Pi.single (sI i) 1) ∧ IsKFin ε (F.σs (sI i)) (vI i) ∧ IsKFin ε (F.σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g *ᵥ x)) = ∑ i, ⟪wI i, F.σs (sI i) g (vI i)⟫_ℂ

def OfSum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ (s : Fin n), IsHCParam (μ + Pi.single s 1) →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsDS ε (μ + Pi.single s 1) σ' →
    ∀ v w : H', IsKFin ε σ' v → IsKFin ε σ' w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ' g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g *ᵥ xI i))

def ToSumd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ F : Fam n, (∀ s, IsHCParam (μ - Pi.single s 1) → IsDS ε (μ - Pi.single s 1) (F.σs s)) →
    ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, F.Hs (sI i)),
      (∀ i, IsHCParam (μ - Pi.single (sI i) 1) ∧ IsKFin ε (F.σs (sI i)) (vI i) ∧ IsKFin ε (F.σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g⁻¹ *ᵥ x)) = ∑ i, ⟪wI i, F.σs (sI i) g (vI i)⟫_ℂ

def OfSumd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ (s : Fin n), IsHCParam (μ - Pi.single s 1) →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsDS ε (μ - Pi.single s 1) σ' →
    ∀ v w : H', IsKFin ε σ' v → IsKFin ε σ' w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ' g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g⁻¹ *ᵥ xI i))

def NormNe : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ), IsHCParam μ → ∀ s s' : Fin n, s ≠ s' →
    vNormSq ε (lowK ε (μ + Pi.single s 1)) ≠ vNormSq ε (lowK ε (μ + Pi.single s' 1)) ∧
    vNormSq ε (lowK ε (μ - Pi.single s 1)) ≠ vNormSq ε (lowK ε (μ - Pi.single s' 1))

theorem fam_of (hE : PI.DSExist) {n : ℕ} (ε : Fin n → Bool) (ν : Fin n → Fin n → ℝ) :
    ∃ F : Fam n, ∀ s, IsHCParam (ν s) → IsDS ε (ν s) (F.σs s) := by
  classical
  have key : ∀ s, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam (ν s) → IsDS ε (ν s) σ := by
    intro s
    by_cases h : IsHCParam (ν s)
    · obtain ⟨H, i1, i2, σ, hσ⟩ := hE n ε (ν s) h
      exact ⟨H, i1, i2, hσ.1, σ, fun _ => hσ⟩
    · exact ⟨ℂ, inferInstance, inferInstance, inferInstance, fun _ => 0, fun h' => absurd h' h⟩
  choose Hs i1 i2 i3 σs hσ using key
  exact ⟨{ Hs := Hs, nH := i1, iH := i2, cH := i3, σs := σs }, hσ⟩

theorem zuck_of (hE : PI.DSExist) (hI : Ineq) (hN : NormNe) (hT : ToSum) (hO : OfSum) : Zuck := by
  classical
  intro n ε μ H _ _ _ σ hμ hσ hg
  obtain ⟨F, hF⟩ := fam_of hE ε (fun s => μ + Pi.single s 1)
  refine ⟨{ Sm := Finset.univ.filter fun s => IsHCParam (μ + Pi.single s 1)
            Hs := F.Hs, σs := F.σs
            ds := fun s hs => ⟨(Finset.mem_filter.1 hs).2, hF s (Finset.mem_filter.1 hs).2⟩
            inequiv := fun s hs s' hs' hne =>
              hI n ε (μ + Pi.single s 1) (μ + Pi.single s' 1) (hN n ε μ hμ s s' hne).1 (F.Hs s) (F.σs s) (hF s (Finset.mem_filter.1 hs).2) (F.Hs s') (F.σs s')
                (hF s' (Finset.mem_filter.1 hs').2)
            toSum := fun v w x y hv hw => by
              obtain ⟨ι, i1, sI, vI, wI, h1, h2⟩ := hT n ε μ H σ hμ hσ hg F hF v w x y hv hw
              exact ⟨ι, i1, sI, vI, wI, fun i => ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, (h1 i).1⟩, (h1 i).2⟩, h2⟩
            ofSum := fun s hs v w hv hw =>
              hO n ε μ H σ hμ hσ hg s (Finset.mem_filter.1 hs).2 (F.Hs s) (F.σs s) (hF s (Finset.mem_filter.1 hs).2) v w hv hw }, fun s => ?_⟩
  simp

theorem zuckDual_of (hE : PI.DSExist) (hI : Ineq) (hN : NormNe) (hT : ToSumd) (hO : OfSumd) : ZuckDual := by
  classical
  intro n ε μ H _ _ _ σ hμ hσ hg
  obtain ⟨F, hF⟩ := fam_of hE ε (fun s => μ - Pi.single s 1)
  refine ⟨{ Sm := Finset.univ.filter fun s => IsHCParam (μ - Pi.single s 1)
            Hs := F.Hs, σs := F.σs
            ds := fun s hs => ⟨(Finset.mem_filter.1 hs).2, hF s (Finset.mem_filter.1 hs).2⟩
            inequiv := fun s hs s' hs' hne =>
              hI n ε (μ - Pi.single s 1) (μ - Pi.single s' 1) (hN n ε μ hμ s s' hne).2 (F.Hs s) (F.σs s) (hF s (Finset.mem_filter.1 hs).2) (F.Hs s') (F.σs s')
                (hF s' (Finset.mem_filter.1 hs').2)
            toSum := fun v w x y hv hw => by
              obtain ⟨ι, i1, sI, vI, wI, h1, h2⟩ := hT n ε μ H σ hμ hσ hg F hF v w x y hv hw
              exact ⟨ι, i1, sI, vI, wI, fun i => ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, (h1 i).1⟩, (h1 i).2⟩, h2⟩
            ofSum := fun s hs v w hv hw =>
              hO n ε μ H σ hμ hσ hg s (Finset.mem_filter.1 hs).2 (F.Hs s) (F.σs s) (hF s (Finset.mem_filter.1 hs).2) v w hv hw }, fun s => ?_⟩
  simp

end PI.ZuckTensorWork
end
