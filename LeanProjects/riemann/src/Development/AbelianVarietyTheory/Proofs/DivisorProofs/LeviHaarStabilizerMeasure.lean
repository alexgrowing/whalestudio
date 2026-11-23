import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureIwasawaQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionMultiplicative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviStabilizerUnipotentIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviUnipotentHaarFactorStatement

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.IwasawaAdapted

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
open GlobalTheory.ThK.UnipDom.Inverse in

theorem iwasawa_formula_adapted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ (μX : Measure (UA σ X.J)) (μ₁ : Measure (UA σ X₁.J)), μX.IsHaarMeasure → μ₁.IsHaarMeasure → ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab (X := X) B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) → ∃ (μN : Measure (unip σ X H)) (c : ℝ≥0∞), μN.IsHaarMeasure ∧ c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : UA σ X.J → ℝ≥0∞, Measurable φ → ∫⁻ g, φ g ∂μX = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ u, φ (u.1 * m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ∂μN ∂μ₁ ∂μ ∂μK := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH μX μ₁ hμX hμ₁ K μK μ hK hμK hμ m hm
  obtain rfl := hH.rank
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : SecondCountableTopology (AE F E) := e.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (AE F E)ˣ := Units.isEmbedding_embedProduct.t2Space
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_UA F E σ (n₁ + 2) X.J
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_UA F E σ n₁ X₁.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X₁.J) := ⟨rfl⟩
  haveI := hμ
  haveI := hμ₁
  haveI := hμX
  haveI := hμK
  haveI : SigmaFinite μ := inferInstance
  haveI : SigmaFinite μ₁ := inferInstance
  haveI : (μ.prod μ₁).IsHaarMeasure := inferInstance

  have hKc : IsCompact (K : Set (UA σ X.J)) := by
    have hKe : (K : Set (UA σ X.J)) = (GlobalTheory.StabHaar.stabK (σ := σ) B X : Set _) := by
      ext g; exact (hK g).trans (GlobalTheory.StabHaar.isStab_stabK B X g).symm
    obtain ⟨C, hC1, hC2⟩ := GlobalTheory.StabBounded.exists_compact_superset_stabK F E σ B (n₁ + 2) X r s hB hX
    rw [hKe]
    exact hC1.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X
      (GlobalTheory.LatHatClosed.isClosed_latHat F E _ X hX.lat)) hC2

  have hL : Submodule.span E ((reS X Y).L : Set (Fin (n₁ + 2) → E)) = ⊤ := hXY.lat.span_eq_top
  choose a b c hdec using fun j : Fin (n₁ + 2) =>
    GlobalTheory.IterBochner.exists_decomp B H (reS X Y) X₁ hH hL (Pi.single j 1)
  have hcont : Continuous fun p : (AE F E)ˣ × UA σ X₁.J => m p.1 p.2 :=
    GlobalTheory.IterBochner.continuous_of_isLevi (W := X) (W₁ := X₁) H a b c hdec m hm
  have huniq : ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (h h' : UA σ X.J), IsLevi (W₁ := X₁) H l g₀ h →
      IsLevi (W₁ := X₁) H l g₀ h' → h = h' := by
    intro l g₀ h h' eh eh'
    exact Subtype.ext (Units.ext ((GlobalTheory.IterBochner.mat_eq_leviMat H a b c hdec l g₀ h eh).trans
      (GlobalTheory.IterBochner.mat_eq_leviMat H a b c hdec l g₀ h' eh').symm))
  have hmul : ∀ l l' g₀ g₀', m (l * l') (g₀ * g₀') = m l g₀ * m l' g₀' := fun l l' g₀ g₀' =>
    huniq _ _ _ _ (hm _ _) (GlobalTheory.LeviHom.isLevi_mul H (hm l g₀) (hm l' g₀'))
  have h11 : m 1 1 = 1 := by
    have h := hmul 1 1 1 1
    rw [one_mul, one_mul] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  let j : ((AE F E)ˣ × UA σ X₁.J) →* UA σ X.J :=
    { toFun := fun x => m x.1 x.2, map_one' := h11, map_mul' := fun x y => hmul _ _ _ _ }
  let δ : ((AE F E)ˣ × UA σ X₁.J) →* ℝ≥0 := (powMonoidHom (n₁ + 1)).comp ((absE F E).comp (MonoidHom.fst _ _))
  have hδc : Continuous δ :=
    (continuous_pow (n₁ + 1)).comp (GlobalTheory.Doubling.continuous_absE.comp continuous_fst)
  have hδ : ∀ x, δ x = absE F E x.1 ^ (n₁ + 1) := fun x => rfl

  have hnorm : ∀ x : (AE F E)ˣ × UA σ X₁.J, ∀ u ∈ unip σ X H, j x * u * (j x)⁻¹ ∈ unip σ X H := by
    rintro ⟨l, g₀⟩ u hu
    show m l g₀ * u * (m l g₀)⁻¹ ∈ unip σ X H
    obtain ⟨hx, -, hι⟩ := hm l g₀
    have hn' := mem_unipSet hu
    have hx' : mat (m l g₀)⁻¹ *ᵥ incV F H.x = (l⁻¹).1 • incV F H.x := by
      have e := congrArg (fun v => (l⁻¹).1 • (mat (m l g₀)⁻¹ *ᵥ v)) hx
      simp only [mat_inv_mulVec, Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul] at e
      exact e.symm
    have hι' : mat (m l g₀)⁻¹ * incM F H.ι = incM F H.ι * mat g₀⁻¹ := by
      have e : mat (m l g₀)⁻¹ * incM F H.ι * mat g₀ = incM F H.ι := by
        rw [Matrix.mul_assoc, ← hι, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
      calc mat (m l g₀)⁻¹ * incM F H.ι = mat (m l g₀)⁻¹ * incM F H.ι * (mat g₀ * mat g₀⁻¹) := by
            rw [← mat_mul, mul_inv_cancel, mat_one, Matrix.mul_one]
        _ = incM F H.ι * mat g₀⁻¹ := by rw [← Matrix.mul_assoc, e]
    have hg : mat g₀ * mat g₀⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
    exact Subgroup.subset_closure
      (GlobalTheory.LeviNormUnip.conj_mem_unipSet (m l g₀) l.1 (l⁻¹).1 _ _ hx hx' (Units.inv_mul l) hι hι' hg u hn')

  have hc : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  set P : Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) E := GlobalTheory.IwEmb.frame H.x H.y H.ι with hP
  set R : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) E :=
    Matrix.of fun k i => Sum.elim (fun t => c i t) (fun t => ![a i, b i] t) k with hR
  have hPR : P * R = 1 := by
    ext i i'
    have e := congrFun (hdec i') i
    rw [Matrix.one_apply]
    rw [Pi.single_apply] at e
    rw [e]
    simp only [hP, hR, GlobalTheory.IwEmb.frame, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, GlobalTheory.LeviElem.cols2, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    ring
  have hRP : R * P = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv.symm).1 hPR
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hPf : P.map f = GlobalTheory.IwEmb.frame (incV F H.x) (incV F H.y) (incM F H.ι) := by
    ext i (k | k)
    · rfl
    · fin_cases k <;> rfl
  have hQP' : R.map f * GlobalTheory.IwEmb.frame (incV F H.x) (incV F H.y) (incM F H.ι) = 1 := by
    rw [← hPf, ← Matrix.map_mul, hRP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hU : unip σ X H = GlobalTheory.IwEmb.unipSub (cA σ) (incM F X.J) (incV F H.x) (incM F H.ι) :=
    Subgroup.closure_eq (GlobalTheory.IwEmb.unipSub (cA σ) (incM F X.J) (incV F H.x) (incM F H.ι))
  have hCE : IsClosed ((unip σ X H : Subgroup (UA σ X.J)) : Set (UA σ X.J)) ∧
      IsClosedEmbedding (fun p : unip σ X H × ((AE F E)ˣ × UA σ X₁.J) => (p.1 : UA σ X.J) * m p.2.1 p.2.2) := by
    rw [hU]
    exact GlobalTheory.IwEmb.closedEmb (cA σ) hc (incM F X.J) (incM F X₁.J) hQP' m hm
  obtain ⟨hNc, hemb⟩ := hCE
  haveI : LocallyCompactSpace (unip σ X H) := hNc.locallyCompactSpace
  let μN : Measure (unip σ X H) := Measure.haar

  have hconv : ∀ l : (AE F E)ˣ, ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((n₁ + 2 : ℕ) : ℝ))) =
      (((absE F E l ^ (n₁ + 1) : ℝ≥0) : ℝ≥0∞))⁻¹ := by
    intro l
    have hne : absE F E l ≠ 0 := by
      intro h0
      have h := (absE F E).map_mul l l⁻¹
      rw [mul_inv_cancel, map_one, h0, zero_mul] at h
      exact one_ne_zero h
    have hpos : (0 : ℝ) < (absE F E l : ℝ) := by
      rw [NNReal.coe_pos]; exact pos_iff_ne_zero.2 hne
    rw [show (1 - ((n₁ + 2 : ℕ) : ℝ)) = -((n₁ + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hpos.le,
      Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity), ← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal]
  obtain ⟨cc, hc0, hcT, hform⟩ := GlobalTheory.NAK.lintegral_eq_nak (UA σ X.J) ((AE F E)ˣ × UA σ X₁.J) (unip σ X H) K j δ
    μX μN μK (μ.prod μ₁) hμX inferInstance hμK inferInstance hKc hcont hδc hnorm hemb
    (fun x f hf => by
      rw [hδ x]
      have h2 := GlobalTheory.T.levi_unipotent_haar_factor F E σ B (n₁ + 2) n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH m hm μN inferInstance x.1 x.2 f hf
      rw [hconv] at h2
      exact h2)
    (fun g => by
      obtain ⟨u, hu, l, g₀, k, hk, rfl⟩ := GlobalTheory.T.levi_stabilizer_unipotent_integral F E σ B (n₁ + 2) n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH K hK m hm g
      exact ⟨u, hu, (l, g₀), k, hk, rfl⟩)
  refine ⟨μN, cc, inferInstance, hc0, hcT, fun φ hφ => ?_⟩
  rw [hform φ hφ]
  congr 1
  refine lintegral_congr fun k => ?_
  have hmeas : Measurable fun p : ((AE F E)ˣ × UA σ X₁.J) × unip σ X H =>
      φ (p.2.1 * j p.1 * k.1) * ((δ p.1 : ℝ≥0) : ℝ≥0∞)⁻¹ := by
    refine (hφ.comp (Continuous.measurable ?_)).mul (Continuous.measurable ?_).inv
    · exact ((continuous_subtype_val.comp continuous_snd).mul (hcont.comp continuous_fst)).mul continuous_const
    · exact ENNReal.continuous_coe.comp (hδc.comp continuous_fst)
  rw [lintegral_prod _ hmeas.lintegral_prod_right'.aemeasurable]
  refine lintegral_congr fun l => lintegral_congr fun g₀ => lintegral_congr fun u => ?_
  show φ (u.1 * m l g₀ * k.1) * ((δ (l, g₀) : ℝ≥0) : ℝ≥0∞)⁻¹ = _
  rw [hδ, hconv]

end GlobalTheory.IwasawaAdapted
