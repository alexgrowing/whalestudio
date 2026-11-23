import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IntegrableOfIsAniso
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsTraceClassOfRankZero

noncomputable section

open scoped ComplexConjugate NNReal ENNReal
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Cusp GlobalTheory.MixModel
open GlobalTheory.Mem.Th (InfF CptF)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (delta swSec sZero IsKFinVec ThetaClause DoublingIso)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RallisIP.Model

variable {D : D7} {A B : HSp D}

theorem range_iff (h : A.rank < B.rank) :
    (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) ↔ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
  omega

theorem exists_splitting (D : D7) (k : ℕ) : ∃ χ, IsHeckeChar D χ ∧ ResEta D χ k := by
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hr := hη.2.2.1
  exact ⟨η ^ k, ⟨by
    have : ((η ^ k : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ k := by funext x; simp
    rw [this]; exact hη.1.1.pow k, fun x => by rw [MonoidHom.pow_apply, hη.1.2 x, one_pow]⟩,
    hr.1, fun e he a => by rw [MonoidHom.pow_apply, hr.2 e he a, pow_one]⟩

theorem hypotheses_inhabited (H : GlobalTheory.Published.WeilRepresentationUnitaryPair) (D : D7) (hD : DoublingIso D) (n k : ℕ) :
    ∃ (A B : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χA χB : (AE D)ˣ →* Circle)
      (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
      (ωd : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
      (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (θ : InfF D) (C : CptF A) (m : Measure (GA D A)) (_ : m.IsHaarMeasure)
      (_ : m.IsMulRightInvariant) (mH : Measure (GA D B)) (U : Submodule ℂ (DividedPowerChartLift A m)),
      A.rank = n ∧ B.rank = k ∧ Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∧ IsWeilDatumO ψ A B χA χB ω ∧
        IsWeilDatumO ψ (dblSp A) B 1 χB ωd ∧ ThetaClause ψ A B χB ω ωd ∧ IsMaj A a ∧ IsCovolOne (ratL B A) ν 𝓕 ∧
        IsInfFam θ ∧ A.SigOK ∧ IsCartanFrame A C ∧ mH.IsHaarMeasure ∧ IsIrredSubrep (RG A m) U ∧ U ≤ L2cusp A m ∧
        LowerLiftsZero m ψ B χA χB (AutMult.formsIn A m (A0 θ A C) U) ∧
        (fun _ => (1 : ℂ)) ∈ AutMult.formsIn A m (A0 θ A C) U := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  let A : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n
  let B : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral k
  have hA : IsAniso A := GlobalTheory.ThetaMean.Model.isAniso_posSpace n
  have hB : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 :=
    (wittIdx_eq_wittIndex B).trans (wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.ThetaMean.Model.isAniso_posSpace k))
  have hs : A.SigOK := Examples₂.posSpace_sigOK _ _
  obtain ⟨χA, h1, h2⟩ := exists_splitting D A.rank
  obtain ⟨χB, h3, h4⟩ := exists_splitting D B.rank
  obtain ⟨ω, hω⟩ := H D ψ A B χA χB hψ h1 h3 h2 h4
  obtain ⟨ωd, hωd, hc, -⟩ := hD ψ A B χA χB ω hω
  obtain ⟨a, ha⟩ := exists_isMaj A
  obtain ⟨ν, 𝓕, hν⟩ := exists_isCovolOne D B.rank A.rank
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨C, hC⟩ := exists_isCartanFrame A hs
  haveI hr := AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A Measure.haar inferInstance
  have hcc : (fun _ => (1 : ℂ)) ∈ cuspCont A := ⟨continuous_const, fun _ _ _ => rfl, fun r C hC => absurd hC (hA r C)⟩
  refine ⟨A, B, ψ, χA, χB, ω, ωd, a, ν, 𝓕, θ, C, Measure.haar, inferInstance, hr, Measure.haar, _, rfl, rfl, hB, hω, hωd,
    hc, ha, hν, hθ, hs, hC, inferInstance, isIrredSubrep_const, ?_, lowerLiftsZero_of_wittIdx_eq_zero hB _ _ _ _ _, ?_, _,
    Submodule.mem_span_singleton_self _, MemL2Quotient.lift_toL2_ae_eq _⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 (toL2_mem_cuspidal _ hcc)
  · exact ⟨⟨isAutFunSm_const θ A 1, .of_invariant fun _ _ _ => rfl⟩, hcc⟩

theorem vol_pos (mH : Measure (GA D B)) [mH.IsHaarMeasure] : 0 < (autMeasure B mH).real Set.univ :=
  ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 (NeZero.ne _)) (measure_ne_top _ _)

theorem petersson_smul_measure (μ : Measure (GA D A)) (c : ℝ≥0) (φ φ' : GA D A → ℂ) :
    petersson A (c • μ) φ φ' = c * petersson A μ φ φ' := by
  have e : AutomorphicL2Unitary.quotMeasure (GQ A) (c • μ) = c • AutomorphicL2Unitary.quotMeasure (GQ A) μ := quotMeasure_smul (c : ℝ≥0∞)
  rw [petersson, pet, e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rfl

theorem value_smul (mH : Measure (GA D B)) {c : ℝ≥0} (hc : c ≠ 0) (φ φ' : GA D B → ℂ) :
    (((autMeasure B (c • mH)).real Set.univ : ℝ) : ℂ)⁻¹ * petersson B (c • mH) φ φ' =
      (((autMeasure B mH).real Set.univ : ℝ) : ℂ)⁻¹ * petersson B mH φ φ' := by
  have e : autMeasure B (c • mH) = c • autMeasure B mH := quotMeasure_smul (c : ℝ≥0∞)
  have h : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [petersson_smul_measure, e, measureReal_nnreal_smul_apply]
  push_cast
  field_simp

variable {ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)} {m : Measure (GA D A)}

theorem petersson_lift_smul_measure (mH : Measure (GA D B)) (c : ℝ≥0) (Φ₁ Φ₂ : WO A B → ℂ) (f₁ f₂ : GA D A → ℂ) :
    petersson B mH (thetaLift ω (c • m) Φ₁ f₁) (thetaLift ω (c • m) Φ₂ f₂) =
      (c : ℂ) ^ 2 * petersson B mH (thetaLift ω m Φ₁ f₁) (thetaLift ω m Φ₂ f₂) := by
  have e : ∀ Φ f, thetaLift ω (c • m) Φ f = (c : ℂ) • thetaLift ω m Φ f := fun Φ f =>
    funext fun h => petersson_smul_measure m c _ _
  rw [e, e, petersson_smul_left, ← petersson_conj_symm, petersson_smul_left, map_mul, petersson_conj_symm,
    Complex.conj_ofReal]
  ring

theorem petersson_lift_smul (mH : Measure (GA D B)) (c₁ c₂ : ℂ) (Φ₁ Φ₂ : WO A B → ℂ) (f₁ f₂ : GA D A → ℂ) :
    petersson B mH (thetaLift ω m Φ₁ (c₁ • f₁)) (thetaLift ω m Φ₂ (c₂ • f₂)) =
      conj c₁ * c₂ * petersson B mH (thetaLift ω m Φ₁ f₁) (thetaLift ω m Φ₂ f₂) := by
  rw [thetaLift_smul, thetaLift_smul, petersson_smul_left, ← petersson_conj_symm, petersson_smul_left, map_mul,
    petersson_conj_symm, Complex.conj_conj]
  ring

theorem dblInt_theta [SigmaFinite m] {ψ : AddChar (AF D.host.F) ℂ} {χB : (AE D)ˣ →* Circle}
    {ωd : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)} (hc : ThetaClause ψ A B χB ω ωd)
    {Φ₁ Φ₂ : WO A B → ℂ} (h₁ : IsThetaFunO ψ A B Φ₁) (h₂ : IsThetaFunO ψ A B Φ₂) (f₁ f₂ : GA D A → ℂ) (h : GA D B) :
    dblInt A χB⁻¹ m (fun g => thetaKO ωd g h (delta A B Φ₁ Φ₂)) f₁ f₂ =
      thetaLift ω m Φ₁ f₁ h * conj (thetaLift ω m Φ₂ f₂ h) := by
  rw [dblInt_of_factor (A := fun g => thetaKO ω g h Φ₁) (B := fun g => thetaKO ω g h Φ₂)
    fun g₁ g₂ => ((hc Φ₁ Φ₂ h₁ h₂).2 g₁ g₂ h).2, thetaLift, thetaLift, petersson_conj_symm]

theorem conclusion_zero (χB : (AE D)ˣ →* Circle) (ωd : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))
    (a : GL (Fin A.rank) (AE D)) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (mH : Measure (GA D B)) (Φ₁ : WO A B → ℂ)
    (f₁ f₂ : GA D A → ℂ) :
    ZetaValueAt A χB⁻¹ m (flat A a (swSec A B ωd ν 𝓕 (delta A B Φ₁ 0)) (sZero A B)) f₁ f₂ (sZero A B)
      ((((autMeasure B mH).real Set.univ : ℝ) : ℂ)⁻¹ * petersson B mH (thetaLift ω m Φ₁ f₁) (thetaLift ω m 0 f₂)) := by
  have h0 : delta A B Φ₁ 0 = 0 := funext fun x => by simp [IndefiniteRowSideFullHecke.SphericalZero.delta]
  have h1 : flat A a (swSec A B ωd ν 𝓕 (delta A B Φ₁ 0)) (sZero A B) = fun _ _ => 0 := by
    funext s g
    refine (flatH_apply _ _ _ _).trans ?_
    simp [h0, swSec, IndefiniteRowSideFullHecke.SphericalZero.evZero]
  have h2 : thetaLift ω m 0 f₂ = 0 := funext fun h => by simp [thetaLift, petersson, pet, AutomorphicL2Unitary.descend, thetaKO]
  have h3 : eis A (fun _ => (0 : ℂ)) = fun _ => 0 := funext fun g => by simp [eis, cosetSum, term]
  have h4 : dblIntegrand A χB⁻¹ (fun _ => (0 : ℂ)) f₁ f₂ = fun _ => 0 := funext fun g => by simp [dblIntegrand]
  have h5 : dblIntegrandQ A χB⁻¹ (fun _ => (0 : ℂ)) f₁ f₂ = fun _ => 0 := funext fun g => by simp [dblIntegrandQ, h4]
  rw [h1, h2, show petersson B mH (thetaLift ω m Φ₁ f₁) 0 = 0 by simp [petersson, pet, AutomorphicL2Unitary.descend], mul_zero]
  refine ⟨⟨fun s _ => ⟨fun _ _ _ => rfl, fun g => ?_⟩, fun s _ => ?_⟩, ?_⟩
  · simp [EisConv, CosetConv, term, summable_zero]
  · rw [h3, DblConv, h4, h5]
    exact ⟨fun _ _ _ => rfl, integrable_zero _ _ _⟩
  · have : zeta A χB⁻¹ m (fun _ _ => (0 : ℂ)) f₁ f₂ = fun _ => 0 := funext fun s => by
      rw [zeta, h3, dblInt, h5, integral_zero]
    rw [this]
    exact (GlobalTheory.Cont.holValueAt_const 0 _).valueAt

end GlobalTheory.RallisIP.Model

end
