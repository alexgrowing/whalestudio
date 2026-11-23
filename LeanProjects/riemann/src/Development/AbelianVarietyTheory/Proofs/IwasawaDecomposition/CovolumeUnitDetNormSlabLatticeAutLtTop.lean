import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeOneEqResidue
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeSiegelStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanTraceFormDualLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapInfiniteGLHaarMeasureMulLeft

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.SlabFinVol

open GlobalTheory.FlagMeas GlobalTheory.MeanDual

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

theorem covol_le_of_mul_left (Γ Γ' : Set (MatInf E j)) (h : MatInf E j) (hh : 0 < detNorm E j h)
    (A B : Set (MatInf E j)) (hAB : ∀ x ∈ A, h * x ∈ B)
    (hΓ : ∀ δ ∈ Γ', ∃ δ₀ ∈ Γ, ∀ x, h * (δ₀ * x) = δ * (h * x)) :
    covol Γ (haarGL E j) A ≤ covol Γ' (haarGL E j) B := by
  unfold covol
  refine le_iInf fun D' => le_iInf fun hD' => le_iInf fun hc => ?_
  have hmeas : Measurable (fun g : MatInf E j => h * g) :=
    (GlobalTheory.MeanDual.measurePreserving_mul_left E j h hh).measurable
  refine iInf_le_of_le ((fun g => h * g) ⁻¹' D') (iInf_le_of_le (hmeas hD') (iInf_le_of_le ?_ ?_))
  · intro x hx
    obtain ⟨δ, hδ, hx'⟩ := hc (h * x) (hAB x hx)
    obtain ⟨δ₀, hδ₀, H⟩ := hΓ δ hδ
    refine ⟨δ₀, hδ₀, ?_⟩
    show h * (δ₀ * x) ∈ D'
    rw [H]; exact hx'
  · rw [← Measure.map_apply hmeas hD', GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq E j h hh]

def scal (r : ℝ) : MatInf E j := fun _ a b => if a = b then (r : ℂ) else 0

theorem of_scal (r : ℝ) (w : InfinitePlace E) :
    Matrix.of (scal E j r w) = (r : ℂ) • (1 : Matrix (Fin j) (Fin j) ℂ) := by
  ext a b
  simp [scal, Matrix.one_apply]

theorem scal_mul_comm (r : ℝ) (δ x : MatInf E j) : scal E j r * (δ * x) = δ * (scal E j r * x) := by
  apply matInf_ext
  intro w
  simp only [of_mul, of_scal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]

theorem detNorm_scal (r : ℝ) (hr : 0 < r) :
    detNorm E j (scal E j r) = (r ^ (2 * j)) ^ Fintype.card (InfinitePlace E) := by
  unfold detNorm
  simp only [of_scal, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [Finset.prod_const, Finset.card_univ]
  congr 1
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, ← pow_mul, mul_comm]

theorem exists_scal (hj : 1 ≤ j) (c : ℝ) (hc : 0 < c) : ∃ r : ℝ, 0 < r ∧ detNorm E j (scal E j r) = c := by
  have hN : Fintype.card (InfinitePlace E) ≠ 0 := Fintype.card_ne_zero
  refine ⟨c ^ (((2 * j * Fintype.card (InfinitePlace E) : ℕ) : ℝ))⁻¹, Real.rpow_pos_of_pos hc _, ?_⟩
  rw [detNorm_scal E j _ (Real.rpow_pos_of_pos hc _), ← pow_mul]
  exact Real.rpow_inv_natCast_pow hc.le (by positivity)

def slab (c : ℝ) : Set (MatInf E j) := {x | c ≤ detNorm E j x ∧ detNorm E j x < c * Real.exp 1}

theorem covol_slab_le (hj : 1 ≤ j) (Λ : Submodule (𝓞 E) (Fin j → E)) (c : ℝ) (hc : 0 < c) :
    covol (autGL E j Λ) (haarGL E j) (slab E j c) ≤
      covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} := by
  obtain ⟨r, hr, hd⟩ := exists_scal E j hj c⁻¹ (inv_pos.2 hc)
  refine covol_le_of_mul_left E j _ _ (scal E j r) (hd ▸ inv_pos.2 hc) _ _ ?_
    (fun δ hδ => ⟨δ, hδ, fun x => scal_mul_comm E j r δ x⟩)
  rintro x ⟨h1, h2⟩
  simp only [Set.mem_setOf_eq, detNorm_mul, hd]
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]; exact h1
  · rw [inv_mul_eq_div, div_lt_iff₀ hc, mul_comm]; exact h2

theorem covol_le_of_carries {γ : GL (Fin j) E} {Λ Λ' : Submodule (𝓞 E) (Fin j → E)} (h : Carries E j γ Λ Λ') :
    covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ≤
      covol (autGL E j Λ') (haarGL E j) (slab E j (detNorm E j (embInf E j γ))) := by
  refine covol_le_of_mul_left E j _ _ (embInf E j γ) (detNorm_embInf E j γ) _ _ ?_ ?_
  · rintro x ⟨h1, h2⟩
    simp only [slab, Set.mem_setOf_eq, detNorm_mul]
    have hp := detNorm_embInf E j γ
    exact ⟨le_mul_of_one_le_right hp.le h1, mul_lt_mul_of_pos_left h2 hp⟩
  · intro x hx
    obtain ⟨δ, hδ, rfl⟩ := (mem_autGL E j).1 hx
    refine ⟨embInf E j (γ⁻¹ * δ * γ), (mem_autGL E j).2 ⟨_, (h.inv.mul hδ).mul h, rfl⟩, fun x => ?_⟩
    apply matInf_ext
    intro w
    simp only [of_mul, embInf_mul, ← Matrix.mul_assoc]
    have := embInf_inv_mul E j γ⁻¹ w
    rw [inv_inv] at this
    rw [this, Matrix.one_mul]

theorem glVol_lt_top (hE : IsTotallyComplex E) : ∀ j : ℕ, 1 ≤ j → glVol E j < ⊤ := by
  intro j hj
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [GlobalTheory.NormOneVol.glVol_one E hE]; exact ENNReal.ofReal_lt_top
    · have h := ih hn
      have hs := GlobalTheory.FlagBase.SiegelStep.glVol_step E hE (n + 1) (by omega) (by simpa using h)
      rw [hs]
      simp only [Nat.add_sub_cancel] at h ⊢
      exact ENNReal.mul_lt_top h ENNReal.ofReal_lt_top

end GlobalTheory.SlabFinVol

open GlobalTheory.FlagMeas GlobalTheory.MeanDual in

theorem GlobalTheory.SlabFinVol.covol_unitSlab_lt_top : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → GlobalTheory.FlagMeas.covol (GlobalTheory.FlagMeas.autGL E j Λ) (GlobalTheory.FlagMeas.haarGL E j) {x | 1 ≤ GlobalTheory.FlagMeas.detNorm E j x ∧ GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} < ⊤ := by
  intro E _ _ hE j hj Λ hΛ
  have hfin := GlobalTheory.SlabFinVol.glVol_lt_top E hE j hj
  let R : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} →
      {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} → Prop :=
    fun Λ Λ' => ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1
  have hle : _ ≤ glVol E j := ENNReal.le_tsum (Quot.mk R ⟨Λ, hΛ⟩)
  have hrel := Quot.eqvGen_exact (Quot.out_eq (Quot.mk R ⟨Λ, hΛ⟩))
  have key : ∀ a b : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ},
      Relation.EqvGen (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} =>
        ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1) a b →
      ∃ γ : GL (Fin j) E, Carries E j γ a.1 b.1 := by
    intro a b hab
    induction hab with
    | rel x y h => exact h
    | refl x => exact ⟨1, fun y => by simp⟩
    | symm x y _ ih => obtain ⟨γ, h⟩ := ih; exact ⟨γ⁻¹, h.inv⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨γ, h⟩ := ih1; obtain ⟨δ, h'⟩ := ih2; exact ⟨δ * γ, h'.mul h⟩
  obtain ⟨γ, hγ⟩ := key _ _ hrel
  exact lt_of_le_of_lt ((covol_le_of_carries E j hγ.inv).trans
    (GlobalTheory.SlabFinVol.covol_slab_le E j hj _ _ (detNorm_embInf E j _))) (lt_of_le_of_lt hle hfin)
