import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergInnerPreserving
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatrixCoefficientCompactSupportFinStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

open MeasureTheory ComplexConjugate
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LagLocForm

section
variable {F : Type} [Field F] [NumberField F] {v : Pl F}

theorem schr_adj (ψ₀ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ₀) {κ : Type} [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure]
    (w : (κ → Fv F v) × (κ → Fv F v)) (f g : (κ → Fv F v) → ℂ) :
    ∫ y, schr ψ₀ w f y * conj (g y) ∂μ = ∫ y, f y * conj (schr ψ₀ (-w) g y) ∂μ := by
  have h1 : ∀ s, conj (ψ₀ s) = ψ₀ (-s) := by
    intro s
    have h := GlobalTheory.norm_addChar_nonarch ψ₀ hψ s
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h]
    simp
  rw [← integral_add_right_eq_self (fun y => f y * conj (schr ψ₀ (-w) g y)) w.1]
  congr 1
  funext y
  simp only [schr, Prod.fst_neg, Prod.snd_neg, map_mul, h1, add_neg_cancel_right]
  have h2 : ⅟(2 : Fv F v) * 2 = 1 := invOf_mul_self 2
  have e : -((y + w.1) ⬝ᵥ -w.2 + ⅟(2 : Fv F v) * (-w.1 ⬝ᵥ -w.2)) = y ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) := by
    simp only [add_dotProduct, dotProduct_neg, neg_dotProduct, neg_neg]
    linear_combination (-(w.1 ⬝ᵥ w.2)) * h2
  rw [e]; ring

theorem ip_self_ne {κ : Type} [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure] (g : (κ → Fv F v) → ℂ) (hg : g ∈ SB (κ → Fv F v))
    (h0 : g ≠ 0) : ∫ y, g y * conj (g y) ∂μ ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  have e : (fun y => g y * conj (g y)) = fun y => ((Complex.normSq (g y) : ℝ) : ℂ) := by
    funext y; exact Complex.mul_conj (g y)
  rw [e, integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine ne_of_gt ?_
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x)
    (Complex.continuous_normSq.comp hg.1.continuous) (hg.2.comp_left (g := Complex.normSq) (map_zero _))
    (fun y => Complex.normSq_nonneg _) ?_
  simpa using hx

end

theorem lagr_local_form : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    (Λ Γ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (vac : (κ → Fv F v) → ℂ), Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    (∀ w ∈ Λ, ∀ w' ∈ Λ, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) →
    IsOpen (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) → IsCompact (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    (∀ w, w ∈ Γ ↔ ∀ γ ∈ Γ, ψ₀ (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) = 1) →
    vac ∈ SB (κ → Fv F v) → vac ≠ 0 → (∀ γ ∈ Γ, ∃ c : ℂ, schr ψ₀ γ vac = c • vac) → (∀ γ ∈ Γ ⊓ Λ, schr ψ₀ γ vac = vac) →
    ∃ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l (schr ψ₀ w φ) = l φ) ∧ l vac ≠ 0 := by
  intro F _ _ v ψ₀ κ _ Λ Γ vac hψ hcond hiso hΓo hΓc hdual hvSB hv0 heig hfix
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  let μ : Measure (κ → Fv F v) := Measure.addHaar
  let c : ((κ → Fv F v) → ℂ) → ((κ → Fv F v) × (κ → Fv F v)) → ℂ :=
    fun φ w => ∫ y, schr ψ₀ w φ y * conj (vac y) ∂μ
  have hc : ∀ (φ : (κ → Fv F v) → ℂ) (w : (κ → Fv F v) × (κ → Fv F v)), c φ w = ∫ y, schr ψ₀ w φ y * conj (vac y) ∂μ := fun _ _ => rfl
  have schr_zero : ∀ φ : (κ → Fv F v) → ℂ, schr ψ₀ 0 φ = φ := by
    intro φ; funext x; simp [schr]
  have schr_add : ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (φ₁ φ₂ : (κ → Fv F v) → ℂ), schr ψ₀ w (φ₁ + φ₂) = schr ψ₀ w φ₁ + schr ψ₀ w φ₂ := by
    intro w φ₁ φ₂; funext x; simp [schr, mul_add]
  have schr_smul : ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (a : ℂ) (φ : (κ → Fv F v) → ℂ), schr ψ₀ w (a • φ) = a • schr ψ₀ w φ := by
    intro w a φ; funext x; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
  have comp_iso : ∀ w ∈ Λ, ∀ w' ∈ Λ, ∀ φ : (κ → Fv F v) → ℂ, schr ψ₀ w (schr ψ₀ w' φ) = schr ψ₀ (w + w') φ := by
    intro w hw w' hw' φ
    rw [GlobalTheory.ThetaQuasiRat.schr_schr, hiso w hw w' hw', mul_zero, AddChar.map_zero_eq_one, one_smul]

  have hconst : ∀ φ : (κ → Fv F v) → ℂ, ∀ l ∈ Λ, ∀ γ ∈ Γ, γ ∈ Λ → c φ (l + γ) = c φ l := by
    intro φ l hl γ hγ hγΛ
    rw [hc, hc, add_comm, ← comp_iso γ hγΛ l hl, schr_adj ψ₀ hψ μ γ (schr ψ₀ l φ) vac,
      hfix (-γ) (AddSubgroup.mem_inf.2 ⟨Γ.neg_mem hγ, Λ.neg_mem hγΛ⟩)]
  let H : AddSubgroup Λ := Γ.addSubgroupOf Λ
  let ct : ((κ → Fv F v) → ℂ) → Λ ⧸ H → ℂ := fun φ =>
    Quotient.lift (s := QuotientAddGroup.leftRel H) (fun l : Λ => c φ l) (by
      intro a b hab
      have hab : -a + b ∈ H := QuotientAddGroup.leftRel_apply.1 hab
      rw [AddSubgroup.mem_addSubgroupOf] at hab
      have e : (b : (κ → Fv F v) × (κ → Fv F v)) = a + ((-a + b : Λ) : (κ → Fv F v) × (κ → Fv F v)) := by
        simp
      show c φ a = c φ b
      rw [e, hconst φ a a.2 _ hab (-a + b).2])
  have hct : ∀ (φ : (κ → Fv F v) → ℂ) (l : Λ), ct φ (l : Λ ⧸ H) = c φ l := fun _ _ => rfl

  have hfin : ∀ φ ∈ SB (κ → Fv F v), (Function.support (ct φ)).Finite := by
    intro φ hφ
    obtain ⟨C, hCc, hC⟩ := GlobalTheory.T.schwartzBruhat_matrixCoefficient_compactSupport_finitePlace v ψ₀ κ μ hψ hcond φ hφ vac hvSB
    obtain ⟨t, ht⟩ := hCc.elim_finite_subcover (fun i : C => (fun z => z - (i : (κ → Fv F v) × (κ → Fv F v))) ⁻¹' Γ)
      (fun i => hΓo.preimage (continuous_sub_right _))
      (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, by simp [Set.mem_preimage, sub_self, zero_mem]⟩)
    refine Set.Finite.subset (t.finite_toSet.biUnion fun i _ =>
      (Set.Subsingleton.finite (s := (QuotientAddGroup.mk : Λ → Λ ⧸ H) ''
        {l : Λ | (l : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ}) ?_)) ?_
    · rintro _ ⟨l₁, h₁, rfl⟩ _ ⟨l₂, h₂, rfl⟩
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have := Γ.sub_mem (show (l₂ : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ from h₂)
        (show (l₁ : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ from h₁)
      simpa [sub_sub_sub_cancel_right, neg_add_eq_sub] using this
    · intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H l =>
        rw [Function.mem_support, hct] at hq
        have hlC := hC _ hq
        obtain ⟨i, hi, hli⟩ := Set.mem_iUnion₂.1 (ht hlC)
        exact Set.mem_biUnion hi ⟨l, hli, rfl⟩
  have hint : ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v),
      Integrable (fun y => schr ψ₀ w φ y * conj (vac y)) μ := by
    intro w φ hφ
    have h1 := GlobalTheory.SchrSBFin.schr_mem_SB v ψ₀ hψ w φ hφ
    exact (h1.1.continuous.mul (Complex.continuous_conj.comp hvSB.1.continuous)).integrable_of_hasCompactSupport
      (hvSB.2.comp_left (g := conj) (map_zero _)).mul_left
  have ct_add : ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v), ct (φ₁ + φ₂) = ct φ₁ + ct φ₂ := by
    intro φ₁ h₁ φ₂ h₂
    funext q
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      simp only [hct, Pi.add_apply, hc, schr_add, add_mul]
      exact integral_add (hint _ _ h₁) (hint _ _ h₂)
  have ct_smul : ∀ (a : ℂ) (φ : (κ → Fv F v) → ℂ), ct (a • φ) = a • ct φ := by
    intro a φ
    funext q
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      simp only [hct, Pi.smul_apply, smul_eq_mul, hc, schr_smul, mul_assoc]
      exact integral_const_mul a _
  let l₀ : SB (κ → Fv F v) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∑ᶠ q, ct φ q
      map_add' := fun φ₁ φ₂ => by
        show ∑ᶠ q, ct ((φ₁ : (κ → Fv F v) → ℂ) + φ₂) q = ∑ᶠ q, ct φ₁ q + ∑ᶠ q, ct φ₂ q
        rw [ct_add _ φ₁.2 _ φ₂.2]
        exact finsum_add_distrib (hfin _ φ₁.2) (hfin _ φ₂.2)
      map_smul' := fun a φ => by
        show ∑ᶠ q, ct (a • (φ : (κ → Fv F v) → ℂ)) q = (RingHom.id ℂ) a • ∑ᶠ q, ct φ q
        rw [ct_smul, RingHom.id_apply, smul_eq_mul, mul_finsum]
        rfl }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  have hl' : ∀ φ (hφ : φ ∈ SB (κ → Fv F v)), l φ = ∑ᶠ q, ct φ q := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  refine ⟨l, fun w hw φ hφ => ?_, ?_⟩
  · rw [hl' _ (GlobalTheory.SchrSBFin.schr_mem_SB v ψ₀ hψ w φ hφ), hl' φ hφ]
    have e : ct (schr ψ₀ w φ) = fun q => ct φ (q + ((⟨w, hw⟩ : Λ) : Λ ⧸ H)) := by
      funext q
      induction q using QuotientAddGroup.induction_on with
      | H m =>
        rw [← QuotientAddGroup.mk_add, hct, hct, hc, hc, comp_iso m m.2 w hw]
        rfl
    rw [e]
    exact finsum_comp_equiv (Equiv.addRight _)
  · have hX0 : c vac 0 ≠ 0 := by
      rw [hc, schr_zero]; exact ip_self_ne μ vac hvSB hv0
    have hd : ∀ w, c vac w ≠ 0 → w ∈ Γ := by
      intro w hw
      rw [hdual]
      intro γ hγ
      obtain ⟨a, ha⟩ := heig γ hγ
      have hinv : a • schr ψ₀ (-γ) vac = vac := by
        rw [← schr_smul, ← ha, GlobalTheory.ThetaQuasiRat.schr_schr, neg_add_cancel, schr_zero]
        have : (-γ).1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ (-γ).2 = 0 := by
          simp only [Prod.fst_neg, Prod.snd_neg, neg_dotProduct, dotProduct_neg]; ring
        rw [this, mul_zero, AddChar.map_zero_eq_one, one_smul]
      have ha0 : a ≠ 0 := by
        rintro rfl; apply hv0; rw [← hinv, zero_smul]
      have hneg : schr ψ₀ (-γ) vac = a⁻¹ • vac := by
        rw [← hinv, smul_smul, inv_mul_cancel₀ ha0, one_smul, hinv]
      have key : ∀ w : (κ → Fv F v) × (κ → Fv F v),
          ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a * c vac w = conj a⁻¹ * c vac w := by
        intro w
        have e1 : schr ψ₀ γ (schr ψ₀ w vac) = (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) • schr ψ₀ w vac := by
          have h1 := GlobalTheory.ThetaQuasiRat.schr_schr ψ₀ γ w vac
          have h2 := GlobalTheory.ThetaQuasiRat.schr_schr ψ₀ w γ vac
          rw [ha, schr_smul, add_comm w γ] at h2
          rw [h1, mul_smul, h2, smul_smul, ← AddChar.map_add_eq_mul]
          have h3 : ⅟(2 : Fv F v) * 2 = 1 := invOf_mul_self 2
          have e4 : ⅟(2 : Fv F v) * (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) =
              (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) := by
            linear_combination (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * h3
          rw [e4]
        have e3 : ∫ y, (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) * (schr ψ₀ w vac y * conj (vac y)) ∂μ =
            ∫ y, conj a⁻¹ * (schr ψ₀ w vac y * conj (vac y)) ∂μ := by
          calc ∫ y, (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) * (schr ψ₀ w vac y * conj (vac y)) ∂μ
              = ∫ y, schr ψ₀ γ (schr ψ₀ w vac) y * conj (vac y) ∂μ := by
                congr 1; funext y; rw [e1, Pi.smul_apply, smul_eq_mul]; ring
            _ = ∫ y, schr ψ₀ w vac y * conj (schr ψ₀ (-γ) vac y) ∂μ := schr_adj ψ₀ hψ μ γ _ vac
            _ = ∫ y, conj a⁻¹ * (schr ψ₀ w vac y * conj (vac y)) ∂μ := by
                congr 1; funext y; rw [hneg, Pi.smul_apply, smul_eq_mul, map_mul]; ring
        rw [integral_const_mul, integral_const_mul] at e3
        rw [hc]; exact e3
      have haa : a = conj a⁻¹ := by
        have k0 := key 0
        simp only [Prod.snd_zero, Prod.fst_zero, dotProduct_zero, zero_dotProduct, sub_zero,
          AddChar.map_zero_eq_one, one_mul] at k0
        exact mul_right_cancel₀ hX0 k0
      have hk := key w
      rw [← haa] at hk
      have hψω : ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) = 1 := by
        have := mul_right_cancel₀ hw hk
        exact mul_right_cancel₀ ha0 (by rw [this, one_mul])
      rw [show w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2 = -(γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) by ring, AddChar.map_neg_eq_inv, hψω, inv_one]
    rw [hl' vac hvSB, finsum_eq_single _ (0 : Λ ⧸ H)]
    · show ct vac ((0 : Λ) : Λ ⧸ H) ≠ 0
      rw [hct]; simpa using hX0
    · intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H m =>
        by_contra hm
        rw [hct] at hm
        exact hq ((QuotientAddGroup.eq_zero_iff m).2 (AddSubgroup.mem_addSubgroupOf.2 (hd m hm)))

end GlobalTheory.LagLocForm
