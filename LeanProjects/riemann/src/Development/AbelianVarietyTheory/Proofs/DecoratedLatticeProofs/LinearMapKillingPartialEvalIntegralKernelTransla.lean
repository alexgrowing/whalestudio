import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRead
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatLinearFunctional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.FlatFactor

theorem fill_add_single {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) (x : {e : m × m' // e ∈ it} → k) (e : m × m') (he : e ∈ it) (a : k) :
    fill ev it β t x + Matrix.single e.1 e.2 a = fill ev it β t (x + Pi.single ⟨e, he⟩ a) := by
  ext r q
  simp only [fill, Matrix.add_apply, Matrix.of_apply, Matrix.single_apply, Pi.add_apply]
  by_cases h : (r, q) ∈ it
  · rw [dif_pos h, dif_pos h]
    by_cases hrq : (r, q) = e
    · subst hrq
      simp [Pi.single_apply]
    · have h1 : ¬ (e.1 = r ∧ e.2 = q) := fun ⟨h1, h2⟩ => hrq (by rw [← h1, ← h2])
      have h2 : (⟨(r, q), h⟩ : {e : m × m' // e ∈ it}) ≠ ⟨e, he⟩ := fun h' => hrq (congrArg Subtype.val h')
      simp [h1, Pi.single_apply, h2]
  · rw [dif_neg h, dif_neg h]
    have h1 : ¬ (e.1 = r ∧ e.2 = q) := fun ⟨h1, h2⟩ => h (by rw [← h1, ← h2]; exact he)
    simp [h1]

theorem continuous_fill {k : Type} [Field k] [TopologicalSpace k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) : Continuous (fill ev it β t) := by
  refine continuous_pi fun r => continuous_pi fun q => ?_
  simp only [fill, Matrix.of_apply]
  by_cases h : (r, q) ∈ it
  · simp only [dif_pos h]; exact continuous_apply _
  · simp only [dif_neg h]; exact continuous_const

theorem hasCompactSupport_comp_fill {k : Type} [Field k] [TopologicalSpace k] [T2Space k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) (Θ : Matrix m m' k → ℂ) (hΘ : HasCompactSupport Θ) :
    HasCompactSupport (fun x => Θ (fill ev it β t x)) := by
  let pr : Matrix m m' k → ({e : m × m' // e ∈ it} → k) := fun T i => T i.1.1 i.1.2
  have hpr : Continuous pr := continuous_pi fun i => (continuous_apply i.1.2).comp (continuous_apply i.1.1)
  have hK : IsCompact (pr '' tsupport Θ) := hΘ.isCompact.image hpr
  refine HasCompactSupport.intro' hK hK.isClosed fun x hx => ?_
  by_contra h
  apply hx
  refine ⟨fill ev it β t x, subset_tsupport _ h, ?_⟩
  funext i
  simp [pr, fill, i.2]

theorem kerRed_translate_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ it, ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) := by
  intro k _ _ _ _ _ _ ψ ν _ _ hν m m' _ _ _ _ M _ _ l β ev it _ hK e he a Θ Θ' hΘ'
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  rw [← sub_eq_zero, ← map_sub]
  apply hK
  intro t
  have hint : Integrable (fun x => Θ.1 (fill ev it β t x)) (Measure.pi fun _ : {e : m × m' // e ∈ it} => ν) :=
    ((Θ.2.1.continuous).comp (continuous_fill ev it β t)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_fill ev it β t Θ.1 Θ.2.2)
  have hint' : Integrable (fun x => Θ.1 (fill ev it β t (x + Pi.single ⟨e, he⟩ a)))
      (Measure.pi fun _ : {e : m × m' // e ∈ it} => ν) :=
    hint.comp_add_right _
  unfold red
  simp only [Submodule.coe_sub, Pi.sub_apply]
  have h1 : ∀ x, Θ'.1 (fill ev it β t x) = Θ.1 (fill ev it β t (x + Pi.single ⟨e, he⟩ a)) := by
    intro x; rw [hΘ', fill_add_single]
  simp_rw [h1]
  rw [integral_sub hint' hint, integral_add_right_eq_self (fun x => Θ.1 (fill ev it β t x)), sub_self]

end GlobalTheory.FlatFactor
