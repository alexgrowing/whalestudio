import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Lattice

theorem tsum_setIntegral_sub_rat : ∀ (D : D7) (m r : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r)), IsCovolOne (ratMx D m r) μr 𝓕r →
    ∀ f : Mx D m r → ℂ, Continuous f → ∀ B : ℝ≥0, (∀ y, ∑' p : Matrix (Fin m) (Fin r) D.host.E, ‖f (y - rat p)‖ₑ ≤ B) →
      Integrable f μr ∧ ∑' p : Matrix (Fin m) (Fin r) D.host.E, ∫ y in 𝓕r, f (y - rat p) ∂μr = ∫ t, f t ∂μr := by
  intro D m r μr 𝓕r h f hf B hB
  obtain ⟨hHaar, hFD, hvol⟩ := h
  haveI := hHaar
  haveI : BorelSpace (Mx D m r) := ⟨rfl⟩
  haveI : Countable D.host.E :=
    Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin m) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin m → Fin r → D.host.E))
  have hinc : Function.Injective (Formalism.L2.Theta.incA D) := by
    have h0 : Function.Injective (algebraMap ↥D.host.F (AF ↥D.host.F)) :=
      NumberField.AdeleRing.algebraMap_injective _ _
    exact Algebra.TensorProduct.includeRight_injective h0
  have hmem : ∀ p : Matrix (Fin m) (Fin r) D.host.E, rat p ∈ ratMx D m r :=
    fun p => AddMonoidHom.mem_range.mpr ⟨p, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Matrix (Fin m) (Fin r) D.host.E ≃ ratMx D m r,
      ∀ p, ((e p : ratMx D m r) : Mx D m r) = rat p := by
    refine ⟨Equiv.ofBijective (fun p => ⟨rat p, hmem p⟩) ⟨fun p q hpq => ?_, fun g => ?_⟩, fun p => rfl⟩
    · have h2 : p.map (Formalism.L2.Theta.incA D) = q.map (Formalism.L2.Theta.incA D) :=
        congrArg Subtype.val hpq
      exact Matrix.map_injective hinc h2
    · obtain ⟨p, hp⟩ := AddMonoidHom.mem_range.mp g.2
      exact ⟨p, Subtype.ext hp⟩
  haveI : Countable (ratMx D m r) := Countable.of_equiv _ e
  haveI : VAddInvariantMeasure (ratMx D m r) (Mx D m r) μr :=
    ⟨fun c s _ => measure_preimage_add μr (c : Mx D m r) s⟩
  have hv : ∀ (p : Matrix (Fin m) (Fin r) D.host.E) (x : Mx D m r), -(e p) +ᵥ x = x - rat p := by
    intro p x
    change ((-(e p) : ratMx D m r) : Mx D m r) + x = x - rat p
    rw [AddSubgroup.coe_neg, he]
    exact neg_add_eq_sub (rat p) x
  have hmeas : ∀ p : Matrix (Fin m) (Fin r) D.host.E, Measurable (fun x => ‖f (x - rat p)‖ₑ) :=
    fun p => (hf.comp (continuous_id.sub continuous_const)).measurable.enorm
  have hlin : ∫⁻ x, ‖f x‖ₑ ∂μr ≤ B := by
    rw [hFD.lintegral_eq_tsum', ← e.tsum_eq]
    simp_rw [hv]
    rw [← lintegral_tsum (fun p => (hmeas p).aemeasurable)]
    calc ∫⁻ x in 𝓕r, ∑' p, ‖f (x - rat p)‖ₑ ∂μr ≤ ∫⁻ _ in 𝓕r, (B : ℝ≥0∞) ∂μr :=
          lintegral_mono fun x => hB x
      _ = B := by rw [lintegral_const, Measure.restrict_apply_univ, hvol, mul_one]
  have hint : Integrable f μr := ⟨hf.aestronglyMeasurable, lt_of_le_of_lt hlin ENNReal.coe_lt_top⟩
  refine ⟨hint, ?_⟩
  rw [hFD.integral_eq_tsum' f hint, ← e.tsum_eq]
  simp_rw [hv]

end GlobalTheory.CompanionTheory.EisUnfold.Lattice
