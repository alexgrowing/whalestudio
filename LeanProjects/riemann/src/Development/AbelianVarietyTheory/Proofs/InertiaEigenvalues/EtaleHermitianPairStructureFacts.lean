import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteNormedAlgebraEqModuleTopology
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitsQuotSqFiniteEtaleHermitianPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarProperSubmoduleEqZeroModuleTopologyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubringEqOKStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactFiniteEtaleHermitianPairOKStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenFiniteEtaleHermitianPairOKStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

namespace GlobalTheory.JR.EtFacts

theorem normE [U : Unram F E] (z : E) : algebraMap F E (Algebra.norm F z) = z * star z := by
  have := U.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  have h2 := (IsUnit.mk0 (2 : F) two_ne_zero)
  exact (quadratic_star_structure b d hb0 hs hd U.star_fix (IsUnit.mk0 d hd0) h2).2.1 z

theorem free_L_E [Unram F E] (A : Et F E) : Module.Free E A.L := by
  have hbc := A.push.out
  exact Module.Free.of_basis (hbc.basis (Module.Free.chooseBasis F A.K))

theorem free_L_K [Unram F E] (A : Et F E) : Module.Free A.K A.L := by
  obtain ⟨⟨b⟩, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  exact Module.Free.of_basis b

theorem eta_NL [U : Unram F E] (A : Et F E) (y : A.L) : A.etaK (A.NL y) = 1 := by
  have := free_L_E A
  have := free_L_K A
  have h1 : Algebra.norm F (A.NL y) = Algebra.norm F (Algebra.norm E y) := by
    rw [Et.NL, Algebra.norm_norm, Algebra.norm_norm]
  rw [Et.etaK, h1, eta]
  obtain ⟨x, hx⟩ := U.unram (Algebra.norm E y)
  have hx2 : ‖Algebra.norm F (Algebra.norm E y)‖ = ‖x‖ ^ 2 := by
    rw [← norm_algebraMap' E, normE, norm_mul, U.norm_star, hx, sq]
  rw [if_pos ⟨x, hx2⟩]

theorem eta_neg_one [Unram F E] (A : Et F E) : A.etaK (-1) = 1 := by
  rw [Et.etaK, eta]
  refine if_pos ⟨1, ?_⟩
  have h : Algebra.norm F (-1 : A.K) * Algebra.norm F (-1 : A.K) = 1 := by
    rw [← map_mul]; simp
  have h' := congrArg norm h
  rw [norm_mul, norm_one] at h'
  have h0 : 0 ≤ ‖Algebra.norm F (-1 : A.K)‖ := norm_nonneg _
  simp only [norm_one, one_pow]
  nlinarith

end GlobalTheory.JR.EtFacts

namespace GlobalTheory.JR.EtFacts

theorem sq_le_range [Unram F E] (A : Et F E) :
    (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range ≤ (EtMeas.normU A).range := by
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  rintro _ ⟨k, rfl⟩
  refine ⟨Units.map (algebraMap A.K A.L).toMonoidHom k, Units.ext (hinj ?_)⟩
  rw [EtMeas.normU_val, hN]
  simp [A.star_K, sq]

theorem finite_quot [Unram F E] (A : Et F E) (hsq : Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range)) :
    Finite (A.Kˣ ⧸ (EtMeas.normU A).range) := by
  have : (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have := Subgroup.finiteIndex_of_le (sq_le_range A)
  exact Subgroup.finite_quotient_of_finiteIndex

theorem key_rel (A : Et F E) (a x : A.Kˣ) : (∃ y : A.L, IsUnit y ∧ (a : A.K) = x * A.NL y) ↔
    (QuotientGroup.mk x : A.Kˣ ⧸ (EtMeas.normU A).range) = QuotientGroup.mk a := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨y, hy, h⟩
    refine ⟨hy.unit, Units.ext ?_⟩
    simp [h, Et.NL, EtMeas.normU]
  · rintro ⟨y, h⟩
    refine ⟨y, y.isUnit, ?_⟩
    have := congrArg Units.val h
    simp only [EtMeas.normU, Units.coe_map, Units.val_mul] at this
    rw [Et.NL, this]; simp

theorem finite_reps_exists [Unram F E] (A : Et F E) (hf : Finite (A.Kˣ ⧸ (EtMeas.normU A).range)) :
    ∃ S : Set A.Kˣ, S.Finite ∧ A.IsReps S := by
  refine ⟨Set.range (Quotient.out : A.Kˣ ⧸ (EtMeas.normU A).range → A.Kˣ), Set.finite_range _, fun a =>
    ⟨Quotient.out (QuotientGroup.mk a : A.Kˣ ⧸ (EtMeas.normU A).range),
    ⟨⟨_, rfl⟩, (key_rel A _ _).2 (QuotientGroup.out_eq' _)⟩, ?_⟩⟩
  rintro _ ⟨⟨q, rfl⟩, h⟩
  rw [← (key_rel A _ _).1 h, QuotientGroup.out_eq']

theorem finite_of_reps [Unram F E] (A : Et F E) (hf : Finite (A.Kˣ ⧸ (EtMeas.normU A).range)) (S : Set A.Kˣ)
    (hS : A.IsReps S) : S.Finite := by
  have hinj : Function.Injective (fun x : S => (QuotientGroup.mk (x : A.Kˣ) : A.Kˣ ⧸ (EtMeas.normU A).range)) := by
    rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
    obtain ⟨z, -, hz⟩ := hS x'
    have e1 := hz x ⟨hx, (key_rel A _ _).2 h⟩
    have e2 := hz x' ⟨hx', (key_rel A _ _).2 rfl⟩
    exact Subtype.ext (e1.trans e2.symm)
  exact Set.finite_coe_iff.1 (Finite.of_injective _ hinj)

end GlobalTheory.JR.EtFacts

namespace GlobalTheory.JR.EtFacts

theorem nonunits_null [U : Unram F E] (A : Et F E) (μ : Measure A.K) (hμ : μ.IsAddHaarMeasure) :
    μ {t | ¬ IsUnit t} = 0 := by
  have := U.lcF
  have : IsArtinianRing A.K := IsArtinianRing.of_finite F A.K
  have hfin := IsArtinianRing.setOfPred_isMaximal_finite A.K
  have hsub : {t : A.K | ¬ IsUnit t} ⊆ ⋃ m ∈ {I : Ideal A.K | I.IsMaximal}, (m : Set A.K) := by
    intro t ht
    obtain ⟨m, hm, htm⟩ := exists_max_ideal_of_mem_nonunits (show t ∈ nonunits A.K from ht)
    exact Set.mem_biUnion hm htm
  refine measure_mono_null hsub ((measure_biUnion_null_iff hfin.countable).2 fun m hm => ?_)
  have h := GlobalTheory.T.addHaar_proper_submodule_eq_zero_moduleTopology F A.K μ hμ (m.restrictScalars F) (fun h => hm.ne_top ?_)
  · exact h
  · rw [Ideal.eq_top_iff_one]
    have : (1 : A.K) ∈ m.restrictScalars F := h ▸ Submodule.mem_top
    exact this

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ y : A.L, algebraMap A.K A.L (A.NL y) = y * star y) ∧ (∀ y : A.L, algebraMap A.K A.L (Algebra.trace A.K A.L y) = y + star y) ∧ (Algebra.traceForm F A.K).Nondegenerate ∧ (∀ y : A.L, IsUnit y → A.etaK (A.NL y) = 1) ∧ A.etaK (-1) = 1 ∧ (∀ᶠ v in 𝓝 (1 : A.K), ∃ s : A.K, s ^ 2 = v) ∧ (∃ S : Set A.Kˣ, S.Finite ∧ A.IsReps S) ∧ (∀ S : Set A.Kˣ, A.IsReps S → S.Finite) ∧ (∀ μ : Measure A.K, μ.IsAddHaarMeasure → μ {t | ¬ IsUnit t} = 0) ∧ IsOpen A.OK ∧ IsCompact A.OK ∧ ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  intro F E _ _ _ _ U A
  have := U.charZero; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  obtain ⟨-, -, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hq := finite_quot A (GlobalTheory.T.finite_units_quot_sq_finiteEtaleHermitianPair F E A)
  refine ⟨hN, htr, ⟨fun x hx => ?_, fun x hx => ?_⟩, fun y _ => eta_NL A y, eta_neg_one A,
    (GlobalTheory.isOpenUnits_and_eventually_sq F A.K).2, finite_reps_exists A hq, finite_of_reps A hq,
    nonunits_null A, GlobalTheory.T.isOpen_finiteEtaleHermitianPair_OK F E A, GlobalTheory.T.isCompact_finiteEtaleHermitianPair_OK F E A, GlobalTheory.T.exists_subring_eq_OK F E A⟩
  · exact EtMeas.eq_zero_of_trace F A.K x fun y => by simpa using hx y
  · exact EtMeas.eq_zero_of_trace F A.K x fun y => by simpa [mul_comm] using hx y

end GlobalTheory.JR.EtFacts
