import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefMeas

theorem image_meas {ι X Y Z : Type} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace Z]
    (μ : Measure X) [SigmaFinite μ] (ν : Measure Z) (c : X → Y) (hc : Measurable c) (hi : Function.Injective c)
    (a : Z → ι → X) (ha : MeasurePreserving a ν (Measure.pi fun _ : ι => μ)) (hai : Function.Injective a)
    (S : Set Z) (hS : MeasurableSet S) :
    MeasurableSet ((fun p v => c (a p v)) '' S) ∧
      Measure.pi (fun _ : ι => μ.map c) ((fun p v => c (a p v)) '' S) = ν S := by
  have he : MeasurableEmbedding c := hc.measurableEmbedding hi
  haveI : SigmaFinite (μ.map c) := he.sigmaFinite_map
  have h1 : MeasurePreserving (fun (q : ι → X) (v : ι) => c (q v)) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : ι => μ.map c) :=
    measurePreserving_pi _ _ fun _ => ⟨hc, rfl⟩
  have h2 : MeasurePreserving (fun (p : Z) (v : ι) => c (a p v)) ν (Measure.pi fun _ : ι => μ.map c) := h1.comp ha
  have hinj : Function.Injective (fun (p : Z) (v : ι) => c (a p v)) := fun p q h =>
    hai (funext fun v => hi (congrFun h v))
  have hm : MeasurableSet ((fun p v => c (a p v)) '' S) := hS.image_of_measurable_injOn h2.measurable hinj.injOn
  refine ⟨hm, ?_⟩
  rw [← h2.measure_preimage hm.nullMeasurableSet, Set.preimage_image_eq _ hinj]

theorem box_meas : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) → ∀ (F₁ : UTin β → Set (ι → ℂ)) (F₂ : {a : Fin r // j ≤ a.val} → Set (ι → Fin (k + 1) → ℂ)) (F₃ : {p : UT r // j ≤ p.1.1.val} → Set (ι → ℂ)) (F₄ : {a : Fin r // j ≤ a.val} → Set (ι → ℝ)), (∀ i, MeasurableSet (F₁ i)) → (∀ i, MeasurableSet (F₂ i)) → (∀ i, MeasurableSet (F₃ i)) → (∀ i, MeasurableSet (F₄ i)) → ∀ Ω : Set (ι → Mt k r), Ω = (fun (p : Crd ι k r j β) (v : ι) => (Matrix.of.symm (CC p v) : Mt k r)) '' (Set.pi Set.univ F₁ ×ˢ Set.pi Set.univ F₂ ×ˢ (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄)) → MeasurableSet Ω ∧ Measure.pi (fun _ : ι => lebR0 k r j β) Ω = (∏ i, volume (F₁ i)) * ((∏ i, volume (F₂ i)) * ((∏ i, volume (F₃ i)) * ∏ i, volume (F₄ i))) := by
  intro ι _ k r j β hm hβ hat F₁ F₂ F₃ F₄ h₁ h₂ h₃ h₄ Ω hΩ
  obtain ⟨hl, -, hinj, -⟩ := Swap.range_eq_and_injective_parabolic_unipotent_product k r j β hm hβ
  haveI s1 : SigmaFinite (volume : Measure (Swap.STop r j)) := Measure.prod.instSigmaFinite
  haveI s2 : SigmaFinite (volume : Measure (PTop k r j)) := Measure.prod.instSigmaFinite
  haveI s3 : SigmaFinite (volume : Measure ((UTin β → ℂ) × PTop k r j)) := Measure.prod.instSigmaFinite
  haveI b1 : BorelSpace (Swap.STop r j) := Prod.borelSpace
  haveI b2 : BorelSpace (PTop k r j) := Prod.borelSpace
  haveI b3 : BorelSpace ((UTin β → ℂ) × PTop k r j) := Prod.borelSpace
  have hG : Continuous fun q : (UTin β → ℂ) × PTop k r j =>
      (Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1)) : Mt k r) :=
    (Swap.cont_pTop.comp continuous_snd).matrix_mul ((GlobalTheory.Amp.Swap.cont_uEmb k r).comp
      ((Swap.extZ (fun p : UT r => β p.1.1 = β p.1.2) ℂ).continuous_of_finiteDimensional.comp continuous_fst))
  have hS : MeasurableSet ((Set.pi Set.univ F₁ ×ˢ Set.pi Set.univ F₂ ×ˢ (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄)) : Set (Crd ι k r j β)) :=
    (MeasurableSet.univ_pi h₁).prod ((MeasurableSet.univ_pi h₂).prod ((MeasurableSet.univ_pi h₃).prod (MeasurableSet.univ_pi h₄)))
  haveI d1 : StandardBorelSpace (Swap.STop r j) := StandardBorelSpace.prod
  haveI d2 : StandardBorelSpace (PTop k r j) := StandardBorelSpace.prod
  haveI d3 : StandardBorelSpace ((UTin β → ℂ) × PTop k r j) := StandardBorelSpace.prod
  haveI d4 : StandardBorelSpace (Mt k r) := StandardBorelSpace.pi_countable
  haveI d5 : StandardBorelSpace (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)) := StandardBorelSpace.prod
  haveI d6 : StandardBorelSpace ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) := StandardBorelSpace.pi_countable
  haveI d7 : StandardBorelSpace (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) := StandardBorelSpace.prod
  haveI d8 : StandardBorelSpace (Crd ι k r j β) := StandardBorelSpace.prod
  have key := image_meas (volume : Measure ((UTin β → ℂ) × PTop k r j)) volume _ hG.measurable
    (Matrix.of.symm.injective.comp hinj) atP hat usage₂.1 _ hS
  rw [← hl] at key
  subst hΩ
  refine ⟨key.1, key.2.trans ?_⟩
  haveI t1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) :=
    Measure.prod.instSigmaFinite
  haveI t3 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := Measure.pi.sigmaFinite _
  haveI t4 : SigmaFinite (volume : Measure ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ)) := Measure.pi.sigmaFinite _
  haveI t2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))) :=
    Measure.prod.instSigmaFinite
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    volume_pi_pi, volume_pi_pi, volume_pi_pi, volume_pi_pi]

end GlobalTheory.DegVol.RefMeas
