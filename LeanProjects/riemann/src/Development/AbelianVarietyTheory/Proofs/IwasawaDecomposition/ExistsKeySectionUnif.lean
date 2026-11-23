import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalTripleFibresBaseChangeKeyDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPowerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqUnitOfContinuousComplexRootStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseFieldMultipleOfNthRootComplexificationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegularStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnKeySectionComplexValueStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSectionOfGenericValuesRegularOnCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem exists_eq_smul_pow {K : Type} [Field K] [Algebra K ℂ] {A : Type} [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] [IsDomain (ℂ ⊗[K] A)] {n : ℕ} (hn : 0 < n) (u : Aˣ) {C : ℂ} (hC : C ≠ 0)
    (ρ : (A →ₐ[K] ℂ) → ℂ)
    (hρ : ∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (A →ₐ[K] ℂ)), IsOpen V →
      (∀ a : A, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V)
    (hu : ∀ ψ : A →ₐ[K] ℂ, ρ ψ ^ n = C * ψ (u : A)) : ∃ (a : K) (b : A), a ≠ 0 ∧ (u : A) = a • b ^ n := by
  haveI : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (ℂ ⊗[K] A) inferInstance
  let res : (ℂ ⊗[K] A →ₐ[ℂ] ℂ) → (A →ₐ[K] ℂ) := fun χ =>
    (χ.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let u' : (ℂ ⊗[K] A)ˣ := Units.map (algebraMap ℂ (ℂ ⊗[K] A) : ℂ →* _) (Units.mk0 C hC) *
    Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] ℂ ⊗[K] A) : A →* _) u
  have hu' : (u' : ℂ ⊗[K] A) = C ⊗ₜ[K] (u : A) := by
    simp [u', Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_pow_eq_unit_of_continuous_complex_root (ℂ ⊗[K] A) n u' (fun χ => ρ (res χ)) hn
    (fun m V s hV hs => hρ m V (fun p => res (s p)) hV fun a => hs _) (fun χ => by
      rw [hu, hu']
      have : C ⊗ₜ[K] (u : A) = C • ((1 : ℂ) ⊗ₜ[K] (u : A)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
      rfl)
  exact GlobalTheory.T.exists_base_field_multiple_of_nth_root_complexification K A n w C u hn hC u.ne_zero (hw.trans hu')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem keySec_of_generic (h : GenFrEx Xo c) (b : ∀ Z : Comp Xo c, Om Z) (hb0 : ∀ Z, b Z ≠ 0)
    (hb : ∀ C : FChart h, ((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R ∧
      (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z)⁻¹ ∈ C.R) : Nonempty (KeySec Xo c) := by
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨f, hf, hfb⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (keyEx Dw) b fun C => (hb C).1
  obtain ⟨f', hf', hfb'⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (-keyEx Dw) (fun Z => (b Z)⁻¹) fun C => by
    have := (hb C).2
    rw [mul_inv, ← Units.val_inv_eq_inv_val] at this
    simpa only [kch, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib] using this
  have h0 : GlobalTheory.AllWt.secZ Xo c 0 = sec Xo c 0 0 := by
    rw [← GlobalTheory.AllWt.secZ_nat]
    congr 1
    funext i
    cases i <;> rfl
  have hm := GlobalTheory.AllWt.mul_mem_secZ hf hf'
  rw [add_neg_cancel, h0] at hm
  have h1 := GlobalTheory.AllWt.one_mem_secZ (Xo := Xo) (c := c)
  rw [h0] at h1
  have hff : f * f' = 1 := by
    refine sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hm h1) fun Z => ?_)
    have e₁ : evC h Z (f * f') = evC h Z f * evC h Z f' := by simp only [evC, evR, evalAt_mul]
    have e₂ : evC h Z (1 : Rul Xo c) = 1 := evalAt_one _ _ _ (hL.test _ _)
    have e₃ := (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)).map_sub
      (f * f') 1
    refine e₃.trans ?_
    change evC h Z (f * f') - evC h Z 1 = 0
    rw [e₁, e₂, hfb, hfb', mul_inv_cancel₀ (hb0 Z), sub_self]
  exact ⟨⟨⟨f, f', hff, (mul_comm _ _).trans hff⟩, hf⟩⟩

theorem exists_chart_units {κ : GlobalTheory.KeyCl.Rule} (h₁ : GlobalTheory.KeyCl.Homog (fun _ => 1) κ) (h₂ : GlobalTheory.KeyCl.Funct κ)
    (h₃ : GlobalTheory.KeyCl.FamUnit κ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (hpq : 1 ≤ Dw.p + Dw.q)
    (h : GenFrEx Xo c) : ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e C.y.s C.y.u Φ ∧ GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧
        ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
  refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
  haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e C.R C.y hpq
  obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om C.Z) C.yg hpq
  obtain ⟨u, hu⟩ := h₃ C.R Φ.key
  refine ⟨Φ, u, hΦ, hu, ?_⟩
  rw [← GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E H Dw l Xo c g e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
  exact (hu (Om C.Z) _ _ (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm

theorem rule_eq_of_rootVal {κ : GlobalTheory.KeyCl.Rule} (h₁ : GlobalTheory.KeyCl.Homog (fun _ => 1) κ) (h₂ : GlobalTheory.KeyCl.Funct κ)
    (h₃ : GlobalTheory.KeyCl.ThetaOne κ) {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom)
      (fun j => Formalism.L2.PjFree.relab c σ (e j).1)} {r : ℕ} {M : ModelsOf F r} (T : ∀ k, ThetaData e F M k)
    {un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)} (hun : ∀ k, IsNormUn (T k) (un k)) (hpq : 1 ≤ Dw.p + Dw.q)
    {N : ℂ} (hN : N ≠ 0) (hNk : ∀ k, (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) = N)
    {y : FrPt Xo c (CAt σ)} {v : ℂ} (hv : RootVal (unfOf e F M un) y v) (Φ : FibKey Xo ℂ y.x)
    (hΦ : Tied (S := ℂ) e y.s y.u Φ) :
    v ^ 4 = (N / (2 * Real.pi * Complex.I) ^ g) ^ 4 * (κ ℂ Φ.key : ℂ) := by
  obtain ⟨k, x, t, ht, rfl⟩ : ∃ (k : Fin F.n) (x : (M.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (un k x) y ∧
    v = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ) := hv
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ (un k x).x, Tied (S := ℂ) e (un k x).s (un k x).u Ψ :=
    @GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (un k x) hpq
  have e₁ : κ ℂ Φ.key = kch (S := ℂ) t ^ 4 * κ ℂ Ψ.key :=
    @GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra t (un k x) y Ψ Φ ht hΨ hΦ
  obtain ⟨a, ha, hy⟩ := hun k x
  have hb : (T k).co.symm x.1 ∈ (T k).co ⁻¹' (M.X k).dom := by
    show (T k).co ((T k).co.symm x.1) ∈ (M.X k).dom
    rw [(T k).co.apply_symm_apply]; exact x.2
  have d1 := ((T k).norm _ hb).1.ne_zero
  rw [hNk] at ha
  have a0 : a ≠ 0 := fun h0 => mul_ne_zero hN d1 (by rw [← ha, h0]; simp)
  have e₂ := GlobalTheory.T.theta_key_rule_value_at_theta_point κ h₁ h₃ E H Dw l Xo c σ g e F r M k (T k) _ hb a (un k x) Ψ a0 hy hΨ
  have e₃ : N ^ 4 * (κ ℂ Ψ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g) ^ 4 := by
    refine mul_right_cancel₀ (pow_ne_zero 4 d1) ?_
    rw [show a ^ 8 = (a ^ 2) ^ 4 by ring, ha] at e₂
    linear_combination e₂
  have hπ : ((2 * Real.pi * Complex.I : ℂ) ^ g) ^ 4 ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ Complex.two_pi_I_ne_zero)
  have e₄ : (κ ℂ Φ.key : ℂ) = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ) ^ 4 * (κ ℂ Ψ.key : ℂ) := by
    rw [e₁]
    rfl
  rw [e₄, div_pow, mul_left_comm, div_mul_eq_mul_div, e₃, div_self hπ, mul_one]

set_option maxHeartbeats 1000000 in

theorem nonempty_keySec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k, (U.X k).dom.Nonempty) → (∀ k la γ, (U.X k).χ la γ = 1) → FnAlgClosed Xo c → 2 ≤ N → 2 < Module.finrank ℚ E / 2 → Nonempty (KeySec Xo c) := by
  intro E _ _ _ H Dw l Xo c σ N U hσ hU _ _ hF hN _
  obtain ⟨hr, -, -, -, -, g, e, F, -⟩ := hU
  have hpq : 1 ≤ Dw.p + Dw.q := by omega
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F _ ξ₀ Gm φ
    hcc him hφ
  have T : ∀ k, ThetaData e F M k := fun k => (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g e F _ M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g e F _ M k (T k)
  have hok : FramesOK e F M un :=
    ⟨fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g e F _ M k (T k) (un k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g e F _ M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g e F _ M un hσ hM hξ hok
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) ξ₀ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 ξ₀ ≠ 0 := (map_ne_zero _).2 hne
    positivity
  obtain ⟨κ, k₁, k₂, -, k₃, -, k₄, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨v, hv⟩ := exists_chart_units k₁ k₂ k₄ e hpq h
  have hroot : ∀ C : FChart h, ∃ (a : c.F) (b : C.R), a ≠ 0 ∧
      ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) = a • (b : Om C.Z) ^ 4 := by
    intro C
    obtain ⟨Φ, u, hΦ, hu, huv⟩ := hv C
    letI : Algebra c.F ℂ := σ.toAlgebra
    haveI := C.sm
    haveI := GlobalTheory.GeomConn.isDomain_tensor C.R.val Subtype.val_injective (hF C.Z) ℂ
    choose z hz using fun ψ : C.R →ₐ[c.F] CAt σ => hL.bc _ _ ψ C.y
    have hex : ∀ ψ, ∃ w, RootVal (unfOf e F M un) (z ψ) w := fun ψ => by
      obtain ⟨k, x, t, ht⟩ := hU₀.2.2.1 (z ψ)
      exact ⟨_, k, x, t, ht, rfl⟩
    choose ρ hρ using hex
    obtain ⟨a, b, ha, hab⟩ := exists_eq_smul_pow (K := c.F) (A := C.R) (n := 4) (by norm_num) u
      (pow_ne_zero 4 (div_ne_zero hC (pow_ne_zero g Complex.two_pi_I_ne_zero))) ρ
      (fun m V s hV hs => GlobalTheory.T.continuousOn_keySection_complexValue E H Dw l Xo c σ g e F _ M T un hσ hM hξ hun hok C.R C.y m V s
        (fun p => z (s p)) (fun p => ρ (s p)) hV hs (fun p _ => hz _) fun p _ => hρ _)
      (fun ψ => by
        obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ (z ψ).x, Tied (S := ℂ) e (z ψ).s (z ψ).u Ψ :=
          @GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (z ψ) hpq
        exact (rule_eq_of_rootVal k₁ k₂ k₃ T hun hpq hC (fun k => by rw [(hMG k).2]) (hρ ψ) Ψ hΨ).trans
          (congrArg _ (hu ℂ _ _
            (@GlobalTheory.T.universal_triple_fibres_base_change_key_data E _ _ _ H Dw l Xo c g e _ ℂ _ _ _ _ σ.toAlgebra ψ C.y (z ψ) Φ Ψ (hz ψ) hΦ hΨ))))
    exact ⟨a, b, ha, by rw [← huv, hab]; rfl⟩
  have hgen : ∀ Z : Comp Xo c, ∃ (a : c.F) (b : Om Z), a ≠ 0 ∧ (v Z : Om Z) = a • b ^ 4 := by
    intro Z
    obtain ⟨C, ψ, z, t, h1, h2⟩ := hA h (Om Z) (genFr h Z)
    obtain rfl := GlobalTheory.Reg.SecGlue.chart_comp Z C ψ z t h1 h2
    obtain ⟨a, b, ha, hab⟩ := hroot C
    refine ⟨a, b / ((kch C.t : (Om C.Z)ˣ) : Om C.Z), ha, ?_⟩
    rw [div_pow, ← smul_div_assoc, ← hab, Units.val_mul, Units.val_pow_eq_pow_val,
      mul_div_cancel_left₀ _ (pow_ne_zero 4 (kch C.t).ne_zero)]
  choose a b ha hab using hgen
  have hb0 : ∀ Z, b Z ≠ 0 := fun Z h0 => (v Z).ne_zero (by rw [hab, h0]; simp)
  refine keySec_of_generic h b hb0 fun C => ?_
  obtain ⟨-, u, -, -, huv⟩ := hv C
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI := GlobalTheory.SupGeneric.isFractionRing_chart C
  have hint : ∀ (x : Om C.Z) (y : C.R), x ^ 4 = y → x ∈ C.R := fun x y hxy => by
    have hi : IsIntegral C.R (x ^ 4) := hxy ▸ isIntegral_algebraMap (R := C.R) (x := y)
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by norm_num : 0 < 4) hi
    exact hw ▸ w.2
  have hc : ∀ (x : c.F) (y : C.R), ((algebraMap c.F C.R x * y : C.R) : Om C.Z) = x • (y : Om C.Z) := fun x y => by
    rw [Algebra.smul_def]
    rfl
  have e₁ : (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z) ^ 4 = (a C.Z)⁻¹ • ((u : C.R) : Om C.Z) := by
    rw [huv, Units.val_mul, Units.val_pow_eq_pow_val, hab, mul_smul_comm, smul_smul,
      inv_mul_cancel₀ (ha _), one_smul, mul_pow]
  refine ⟨hint _ _ (e₁.trans (hc _ _).symm),
    hint _ (algebraMap c.F C.R (a C.Z) * ((u⁻¹ : (C.R)ˣ) : C.R)) ?_⟩
  rw [inv_pow, e₁, hc]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [smul_mul_smul_comm, inv_mul_cancel₀ (ha _), one_smul, ← Subalgebra.coe_mul, Units.mul_inv]
  rfl

end GlobalTheory.KeyFourth
