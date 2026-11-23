import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicPeriodLocalPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodConjRatioUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterFiltrationOneStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.LTChar.main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (s : ℕ), 0 < s → ∃ (K' : FinExt l) (_ : K.1 ≤ K'.1) (x : P.R.Bˣ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ), (∀ c : ↥(MaximalUnramifiedExtension l), fr l s c = c → (c : Om l) ∈ K'.1) ∧ (∀ g, fr l s (χ g : ↥(MaximalUnramifiedExtension l)) = χ g) ∧ (Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) ∧ P.ιB x ∈ Fil P 1 ∧ P.ιB x ∉ Fil P 2 ∧ ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := by
  intro l _ P AI T K s hs
  obtain ⟨E, ω, -, -, hE, -⟩ := GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l s hs
  obtain ⟨x, hu, hφ, h1, h2, hj⟩ := GlobalTheory.LTPeriod.main l P AI T K s hs
  have h1' : P.ιB x ∈ Fil P 1 := (mem_Fil_iff P K).2 h1
  have h2' : P.ιB x ∉ Fil P 2 := fun h => h2 ((mem_Fil_iff P K).1 h)
  have hj' : ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := fun j h0 hjs =>
    ⟨(mem_Fil_iff P K).2 (hj j h0 hjs).1, fun h => (hj j h0 hjs).2 ((mem_Fil_iff P K).1 h)⟩
  let K' : FinExt l := supExt K E
  have hKK' : K.1 ≤ K'.1 := le_sup_left
  have hEK' : E.1 ≤ K'.1 := le_sup_right
  choose a ha hax using fun g : GQ l => GlobalTheory.T.lubinTate_period_conj_ratio_unramified l P AI T s hs x hu hφ h1' h2' hj' g
  have hx0 : x ≠ 0 := by
    intro h0
    apply h2'
    rw [h0, map_zero]
    exact Fil_zero_mem 2
  haveI : Nontrivial P.R.B := ⟨⟨x, 0, hx0⟩⟩
  have hcancel : ∀ c c' : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c * x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c' * x → c = c' :=
    fun c c' h => (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (hu.mul_right_cancel h)
  have hfix : ∀ (g : ↥(GK K')) (h : GQ l), P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h)) =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) := fun g h => act_kur P g (hEK' ((hE (a h)).1 (ha h)))
  have hmul : ∀ g h : ↥(GK K'), a ((g : GQ l) * (h : GQ l)) = a g * a h := by
    intro g h
    apply hcancel
    calc algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a ((g : GQ l) * (h : GQ l))) * x = P.actQ ((g : GQ l) * (h : GQ l)) x := (hax _).symm
      _ = P.actQ (g : GQ l) (P.actQ (h : GQ l) x) := by rw [map_mul, AlgEquiv.mul_apply]
      _ = P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) * x) := by rw [hax]
      _ = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) * (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a g) * x) := by rw [map_mul, hfix, hax]
      _ = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a g * a h) * x := by rw [map_mul]; ring
  have hone : a 1 = 1 := by
    apply hcancel
    rw [← hax, map_one, AlgEquiv.one_apply, map_one, one_mul]
  have hne : ∀ g, a g ≠ 0 := by
    intro g h0
    have h := hax g
    rw [h0, map_zero, zero_mul] at h
    exact hx0 ((P.actQ g).injective (h.trans (map_zero _).symm))
  let χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ :=
    { toFun := fun g => Units.mk0 (a g) (hne g)
      map_one' := Units.ext hone
      map_mul' := fun g h => Units.ext (hmul g h) }
  refine ⟨K', hKK', hu.unit, χ, fun c hc => hEK' ((hE c).1 hc), fun g => ha _, ?_, fun g => ?_, ?_, ?_,
    fun j h0 hjs => ?_⟩
  · exact GlobalTheory.T.continuous_galois_character_filtration_one l P AI T K' x h1' h2' (fun g => a g) (fun g => hax g)
  · rw [IsUnit.unit_spec]
    exact hax g
  · rw [IsUnit.unit_spec]
    exact h1'
  · rw [IsUnit.unit_spec]
    exact h2'
  · rw [IsUnit.unit_spec]
    exact hj' j h0 hjs

end
