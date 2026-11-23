import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt

open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

private theorem cont_prodFn {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ) :
    Continuous fun y : Fin m → G => (List.ofFn y).prod := by
  simp only [List.ofFn_eq_map]
  exact continuous_list_prod (f := fun i (y : Fin m → G) => y i) _ fun i _ => continuous_apply i

private theorem cont_fib {G : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ) :
    Continuous fun p : G × (Fin m → G) => fib p.2 p.1 := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [fib, Fin.snoc_last]
    exact ((cont_prodFn m).comp continuous_snd).inv.mul continuous_fst
  · simp only [fib, Fin.snoc_castSucc]
    exact (continuous_apply j).comp continuous_snd

private theorem prod_fib {G : Type} [Group G] [MeasurableSpace G] {m : ℕ} (y : Fin m → G) (x : G) :
    (List.ofFn (fib y x)).prod = x := by
  rw [List.ofFn_succ']
  simp [fib]

private theorem integrable_fib {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ)
    (Φ : (Fin (m + 1) → G) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    ∃ K : Set (Fin m → G), IsCompact K ∧ (∀ x y, y ∉ K → Φ (fib y x) = 0) ∧
      ∀ x, Integrable (fun y : Fin m → G => Φ (fib y x)) (Measure.pi fun _ => μ) := by
  have hK : IsCompact ((fun g : Fin (m + 1) → G => fun i : Fin m => g i.castSucc) '' tsupport Φ) :=
    hs.isCompact.image (continuous_pi fun i => continuous_apply _)
  have h0 : ∀ x y, y ∉ ((fun g : Fin (m + 1) → G => fun i : Fin m => g i.castSucc) '' tsupport Φ) →
      Φ (fib y x) = 0 := by
    intro x y hy
    by_contra h
    exact hy ⟨fib y x, subset_tsupport _ h, funext fun i => by simp [fib]⟩
  refine ⟨_, hK, h0, fun x => ?_⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK (h0 x))
  exact hc.comp ((cont_fib m).comp (Continuous.prodMk_right x))

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.pushTest :
    UpperTheory.ConvolutionTheory.L1.PushTest := by
  intro G _ _ _ _ _ _ _ _ μ _ m Φ hc hs
  obtain ⟨K, hK, h0, hint⟩ := integrable_fib μ m Φ hc hs
  have hsup : ∀ x, push μ m Φ x ≠ 0 → ∃ g, Φ g ≠ 0 ∧ (List.ofFn g).prod = x := by
    intro x hx
    by_contra h
    apply hx
    have : ∀ y : Fin m → G, Φ (fib y x) = 0 := fun y => by
      by_contra h'
      exact h ⟨_, h', prod_fib y x⟩
    simp [push, this]
  refine ⟨?_, ?_, hsup, hint, ?_, ?_⟩
  · have e : push μ m Φ = fun x => ∫ y in K, Φ (fib y x) ∂(Measure.pi fun _ => μ) := by
      funext x
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 x)).symm
    rw [e]
    exact continuous_parametric_integral_of_continuous (f := fun x y => Φ (fib y x)) (hc.comp (cont_fib m)) hK
  · refine HasCompactSupport.intro (hs.isCompact.image (cont_prodFn (m + 1))) fun x hx => ?_
    by_contra h
    obtain ⟨g, hg, rfl⟩ := hsup x h
    exact hx ⟨g, subset_tsupport _ hg, rfl⟩
  · intro c
    funext x
    simp [push, integral_const_mul]
  · intro Ψ hc' hs'
    obtain ⟨_, _, _, hint'⟩ := integrable_fib μ m Ψ hc' hs'
    funext x
    simp only [push, Pi.add_apply]
    exact integral_add (hint x) (hint' x)
