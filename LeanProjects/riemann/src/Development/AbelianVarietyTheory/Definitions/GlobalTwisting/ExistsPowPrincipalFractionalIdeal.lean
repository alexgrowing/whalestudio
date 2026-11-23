import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalRingCardinality.DataForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareEvenThetaConjugateLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalRealBasisComplexCoordinates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegersMemInverseHalfDifferent

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.Glob

section Image

variable {LL : Type} [Field LL] [NumberField LL] (ι : LL →+* ℂ)

abbrev imM : IntermediateField ℚ ℂ := ι.toRatAlgHom.fieldRange

def imEquiv : LL ≃ₐ[ℚ] imM ι := AlgEquiv.ofInjectiveField ι.toRatAlgHom

@[simp] theorem coe_imEquiv (x : LL) : ((imEquiv ι x : imM ι) : ℂ) = ι x := rfl

instance imM_numberField : NumberField (imM ι) where
  to_finiteDimensional := LinearEquiv.finiteDimensional (imEquiv ι).toLinearEquiv

def rhoOf (s : LL →+* ℂ) : imM ι →ₐ[ℚ] ℂ := s.toRatAlgHom.comp (imEquiv ι).symm.toAlgHom

@[simp] theorem rhoOf_imEquiv (s : LL →+* ℂ) (x : LL) : rhoOf ι s (imEquiv ι x) = s x := by
  simp [rhoOf]

def rhoEquiv : (LL →+* ℂ) ≃ (imM ι →ₐ[ℚ] ℂ) where
  toFun := rhoOf ι
  invFun ρ := (ρ.comp (imEquiv ι).toAlgHom).toRingHom
  left_inv s := by ext x; simp
  right_inv ρ := by
    ext x
    obtain ⟨y, rfl⟩ := (imEquiv ι).surjective x
    simp

@[simp] theorem rhoEquiv_apply (s : LL →+* ℂ) : rhoEquiv ι s = rhoOf ι s := rfl

theorem sum_rhoOf (f : (imM ι →ₐ[ℚ] ℂ) → ℝ) : ∑ s : LL →+* ℂ, f (rhoOf ι s) = ∑ ρ, f ρ :=
  (rhoEquiv ι).sum_comp f

theorem card_emb : Fintype.card (LL →+* ℂ) = Module.finrank ℚ (imM ι) := by
  rw [NumberField.Embeddings.card LL ℂ]
  exact (imEquiv ι).toLinearEquiv.finrank_eq

end Image

section Curve

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {M : IntermediateField ℚ ℂ}

theorem lamConj_cases (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ (cc' : Ideal (𝓞 D.host.K)) (δ' : ℂ), Crv D cc' δ' ∧
      (lamConj M ρ (lamOf D cc δ) = lamOf D cc' δ' ∨
        (lamConj M ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom = lamOf D cc' δ') := by
  obtain ⟨hfix, hbar, -⟩ := GlobalTheory.ThetaConj.useBar_holds D cc δ h M ρ hM
  rcases hfix with hfix | hfix
  · obtain ⟨cc', δ', hc', -, e⟩ :=
      GlobalTheory.ConjCurve.galCurve_holds D cc δ h M ρ hfix hM.2.1 hM.2.2 1 one_pos
    exact ⟨cc', δ', hc', Or.inl e⟩
  · obtain ⟨cc', δ', hc', -, e⟩ :=
      GlobalTheory.ConjCurve.galCurve_holds D cc δ h M (rhoBar M ρ) hfix hM.2.1 hM.2.2 1 one_pos
    refine ⟨cc', δ', hc', Or.inr ?_⟩
    rw [← e]
    exact (congrArg Tor.abelian₂ hbar).symm

theorem isLat_lamConj (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) :
    GlobalTheory.ThetaConj.IsLat (lamConj M ρ (lamOf D cc δ)) := by
  obtain ⟨cc', δ', h', e | e⟩ := lamConj_cases h hM ρ
  · rw [e]; exact GlobalTheory.ThetaConj.isLat_lamOf h'
  · rw [← GlobalTheory.ThetaConj.conj_conj_lat (lamConj M ρ (lamOf D cc δ)), e]
    exact (GlobalTheory.ThetaConj.isLat_lamOf h').conj

theorem area_lamConj_pos (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) :
    0 < area (lamConj M ρ (lamOf D cc δ)) := by
  obtain ⟨cc', δ', h', e | e⟩ := lamConj_cases h hM ρ
  · rw [e]; exact GlobalTheory.ConjJet.area_pos D (GlobalTheory.InducedType.induced_type D).1 cc' δ' h'
  · rw [← GlobalTheory.ThetaConj.area_conj, e]
    exact GlobalTheory.ConjJet.area_pos D (GlobalTheory.InducedType.induced_type D).1 cc' δ' h'

theorem isThetaZero_unique_lattice (h : Crv D cc δ) {t t' : ℂ} (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t') : t - t' ∈ lamOf D cc δ := by
  rw [GlobalTheory.ThetaConj.twoTorsionCMPoint_iff] at ht ht'
  obtain ⟨k, hk⟩ := GlobalTheory.ThetaConj.weylMatrix_mul_apply D
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  refine GlobalTheory.ThetaConj.two_torsion_unique (GlobalTheory.ThetaConj.isLat_lamOf h) (w0 D) k hk ht.1 ht.2.1 ht.2.2
    ht'.1 ht'.2.1 ht'.2.2 ?_
  rw [← ha]
  exact (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.2.2 a

theorem isThetaZero_unique (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) {t t' : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t') :
    t - t' ∈ lamConj M ρ (lamOf D cc δ) := by
  obtain ⟨cc', δ', h', e | e⟩ := lamConj_cases h hM ρ
  · rw [e] at ht ht' ⊢; exact isThetaZero_unique_lattice h' ht ht'
  · have h1 := GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht
    have h2 := GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht'
    rw [e] at h1 h2
    have := isThetaZero_unique_lattice h' h1 h2
    rw [← e, GlobalTheory.ThetaConj.mem_conj] at this
    simpa using this

theorem exists_isThetaZero (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t :=
  (GlobalTheory.TwoTorsionPt.exists_point D cc δ h).2 M ρ hM.2.1 hM.2.2

theorem thetaZero_eq_of_isThetaZero (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) {t t' : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t') :
    GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t = GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t' := by
  have := GlobalTheory.ThetaConj.evenTheta_add_lattice_mem (isLat_lamConj h hM ρ) t' (isThetaZero_unique h hM ρ ht ht')
  rwa [add_sub_cancel] at this

theorem normSq1_eq_nrm1Sq (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : GL3Theta.normSq1 Λ G = nrm1Sq Λ G := by
  unfold GL3Theta.normSq1 nrm1Sq
  have : ∀ z : ℂ, -Real.pi * (GL3Theta.hf1 Λ z z).re = -Real.pi * ‖z‖ ^ 2 / area Λ := fun z => by
    unfold GL3Theta.hf1
    rw [Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    ring
  simp only [this]

theorem normSq1_nonneg (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : 0 ≤ GL3Theta.normSq1 Λ G := by
  unfold GL3Theta.normSq1
  simp only [MeasureTheory.average]
  exact MeasureTheory.integral_nonneg fun z => by positivity

theorem normSq_thetaZero_pos (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) {t : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) :
    0 < GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t) := by
  refine lt_of_le_of_ne (normSq1_nonneg _ _) (Ne.symm ?_)
  rw [normSq1_eq_nrm1Sq]
  have hl := isLat_lamConj h hM ρ
  obtain ⟨cc', δ', h', e | e⟩ := lamConj_cases h hM ρ
  · rw [e] at ht ⊢
    exact GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc' δ' t h' ht
  · have h1 := GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht
    rw [← GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq _ hl t]
    rw [e] at h1 ⊢
    exact GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc' δ' _ h' h1

end Curve

section Line

variable {D : D7} {M : IntermediateField ℚ ℂ} [NumberField M]

def intT (hM : ∀ τ x, embT D τ x ∈ M) (τ : D.what₂.Tau) (b : 𝓞 D.host.E) : 𝓞 M :=
  RingOfIntegers.mapRingHom ((embT D τ).codRestrict M (hM τ)) b

theorem ellT_ne_bot (hM : ∀ τ x, embT D τ x ∈ M) (τ : D.what₂.Tau) : ellT D M τ ≠ ⊥ := by
  first
  | exact @_root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot
  | exact _root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot
  | (apply _root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot <;> assumption)
  | (intros; apply _root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot ..)

theorem ne_zero_of_span_eq (hM : ∀ τ x, embT D τ x ∈ M) {τ : D.what₂.Tau} {a : M}
    (ha : Submodule.span (𝓞 M) {a} = ellT D M τ) : a ≠ 0 := by
  rintro rfl
  exact ellT_ne_bot hM τ (by rw [← ha, Submodule.span_singleton_eq_bot])

omit [NumberField M] in

theorem exp_neg_logMet {Λ : AddSubgroup ℂ} {ρ : M →ₐ[ℚ] ℂ} (hΛ : 0 < area (lamConj M ρ Λ)) {a : M}
    (ha : a ≠ 0) : Real.exp (-logMet M Λ ρ a) = area (lamConj M ρ Λ) / (Real.pi * ‖ρ a‖ ^ 2) := by
  have h1 : 0 < ‖ρ a‖ := norm_pos_iff.2 ((map_ne_zero ρ).2 ha)
  have := Real.pi_pos
  unfold logMet
  rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]

omit [NumberField M] in

theorem logMet_mul {Λ : AddSubgroup ℂ} {ρ : M →ₐ[ℚ] ℂ} (hΛ : 0 < area (lamConj M ρ Λ)) {c a : M}
    (hc : c ≠ 0) (ha : a ≠ 0) :
    logMet M Λ ρ (c * a) = 2 * Real.log ‖ρ c‖ + logMet M Λ ρ a := by
  have h1 : 0 < ‖ρ a‖ := norm_pos_iff.2 ((map_ne_zero ρ).2 ha)
  have h2 : 0 < ‖ρ c‖ := norm_pos_iff.2 ((map_ne_zero ρ).2 hc)
  have := Real.pi_pos
  unfold logMet
  rw [map_mul, norm_mul, show Real.pi * (‖ρ c‖ * ‖ρ a‖) ^ 2 / area (lamConj M ρ Λ) =
    ‖ρ c‖ ^ 2 * (Real.pi * ‖ρ a‖ ^ 2 / area (lamConj M ρ Λ)) by ring,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  norm_num

theorem index_span_mul (c : 𝓞 M) {a : M} (ha : a ≠ 0) :
    ((Submodule.span (𝓞 M) {c • a}).toAddSubgroup.addSubgroupOf
      (Submodule.span (𝓞 M) {a}).toAddSubgroup).index = Ideal.absNorm (Ideal.span {c}) := by
  let f : 𝓞 M →ₗ[𝓞 M] M := LinearMap.toSpanSingleton (𝓞 M) M a
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact LinearMap.ker_toSpanSingleton (𝓞 M) ha
  have h1 : (Submodule.span (𝓞 M) {a}).toAddSubgroup = (⊤ : AddSubgroup (𝓞 M)).map f.toAddMonoidHom := by
    ext x
    simp [f, Submodule.mem_span_singleton]
  have h2 : (Submodule.span (𝓞 M) {c • a}).toAddSubgroup =
      (Ideal.span {c} : Ideal (𝓞 M)).toAddSubgroup.map f.toAddMonoidHom := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, AddSubgroup.mem_map,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r * c, ⟨r, rfl⟩, by simp [f, mul_smul]⟩
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, by simp [f, mul_smul]⟩
  change AddSubgroup.relIndex _ _ = _
  rw [h1, h2, AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_top_right]
  rfl

theorem sum_log_norm (c : 𝓞 M) (hc : c ≠ 0) :
    ∑ ρ : M →ₐ[ℚ] ℂ, Real.log ‖ρ (c : M)‖ = Real.log (Ideal.absNorm (Ideal.span {c}) : ℕ) := by
  have hc' : (c : M) ≠ 0 := by simpa using hc
  rw [← Real.log_prod (fun ρ _ => norm_ne_zero_iff.2 ((map_ne_zero ρ).2 hc')), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ (c : M), Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

theorem meanLogOm_eq_of_gen (hM : ∀ τ x, embT D τ x ∈ M) {Λ : AddSubgroup ℂ}
    (hΛ : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ Λ)) {τ : D.what₂.Tau} {a : M}
    (ha : Submodule.span (𝓞 M) {a} = ellT D M τ) :
    meanLogOm D Λ M τ = -(∑ ρ : M →ₐ[ℚ] ℂ, logMet M Λ ρ a) / (Module.finrank ℚ M : ℝ) := by
  have ha0 := ne_zero_of_span_eq hM ha
  have hs := Classical.epsilon_spec (p := fun s : M => s ≠ 0 ∧ s ∈ ellT D M τ)
    ⟨a, ha0, ha ▸ Submodule.mem_span_singleton_self a⟩
  unfold meanLogOm
  simp only
  generalize Classical.epsilon (fun s : M => s ≠ 0 ∧ s ∈ ellT D M τ) = s at hs ⊢
  obtain ⟨hs0, hs⟩ := hs
  rw [← ha] at hs ⊢
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
  have hc : c ≠ 0 := by rintro rfl; simp at hs0
  have hc' : (c : M) ≠ 0 := by simpa using hc
  rw [index_span_mul c ha0, ← sum_log_norm c hc]
  have : ∀ ρ : M →ₐ[ℚ] ℂ, logMet M Λ ρ (c • a) = 2 * Real.log ‖ρ (c : M)‖ + logMet M Λ ρ a :=
    fun ρ => logMet_mul (hΛ ρ) hc' ha0
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Line

section Comparison₂

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

def th0NormSq (M : IntermediateField ℚ ℂ) (Λ : AddSubgroup ℂ) (ρ : M →ₐ[ℚ] ℂ) : ℝ :=
  GL3Theta.normSq1 (lamConj M ρ Λ)
    (GL3Theta.th0 (lamConj M ρ Λ) (Classical.epsilon (GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ Λ))))

structure ExtraTie {LL : Type} [Field LL] [NumberField LL] (ι : LL →+* ℂ)
    (G : GlobalExtra LL D.what₂.Tau) (a : D.what₂.Tau → imM ι) : Prop where

  crv : Crv D cc δ

  data : DataIn D (tor0 D cc δ) (imM ι)

  gen : ∀ τ, Submodule.span (𝓞 (imM ι)) {a τ} = ellT D (imM ι) τ

  om : ∀ τ (s : LL →+* ℂ),
    G.Om τ s = Real.exp (-logMet (imM ι) (lamOf D cc δ) (rhoOf ι s) (a τ))

  th : ∀ (s : LL →+* ℂ) (t : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (imM ι) (rhoOf ι s) (lamOf D cc δ)) t →
    G.thOne s ^ 2 = GL3Theta.normSq1 (lamConj (imM ι) (rhoOf ι s) (lamOf D cc δ))
      (GL3Theta.th0 (lamConj (imM ι) (rhoOf ι s) (lamOf D cc δ)) t)

abbrev coefM : IntermediateField ℚ ℂ := imM D.what₂.embLL

def PerTie : Prop :=
  Crv D cc δ ∧ DataIn D (tor0 D cc δ) (coefM D) ∧
  (∀ τ : D.what₂.Tau, ∃ a : coefM D, Submodule.span (𝓞 (coefM D)) {a} = ellT D (coefM D) τ ∧
    ∀ s : D.what₂.LL →+* ℂ, D.gx.Om τ s =
      Real.exp (-logMet (coefM D) (lamOf D cc δ) (rhoOf D.what₂.embLL s) a)) ∧
  ∀ (s : D.what₂.LL →+* ℂ) (t : ℂ),
    GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (coefM D) (rhoOf D.what₂.embLL s) (lamOf D cc δ)) t →
    D.gx.thOne s ^ 2 = GL3Theta.normSq1 (lamConj (coefM D) (rhoOf D.what₂.embLL s) (lamOf D cc δ))
      (GL3Theta.th0 (lamConj (coefM D) (rhoOf D.what₂.embLL s) (lamOf D cc δ)) t)

theorem perTie_iff : PerTie D cc δ ↔ ∃ a, ExtraTie D cc δ D.what₂.embLL D.gx a := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    choose a ha using h3
    exact ⟨a, h1, h2, fun τ => (ha τ).1, fun τ => (ha τ).2, h4⟩
  · rintro ⟨a, h⟩
    exact ⟨h.crv, h.data, fun τ => ⟨a τ, h.gen τ, h.om τ⟩, h.th⟩

variable {D cc δ}

theorem th0NormSq_eq {M : IntermediateField ℚ ℂ} (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M)
    (ρ : M →ₐ[ℚ] ℂ) {t : ℂ} (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) :
    th0NormSq D M (lamOf D cc δ) ρ =
      GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t) := by
  unfold th0NormSq
  rw [thetaZero_eq_of_isThetaZero h hM ρ (Classical.epsilon_spec (exists_isThetaZero h hM ρ)) ht]

theorem th0NormSq_pos {M : IntermediateField ℚ ℂ} (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M)
    (ρ : M →ₐ[ℚ] ℂ) : 0 < th0NormSq D M (lamOf D cc δ) ρ :=
  normSq_thetaZero_pos h hM ρ (Classical.epsilon_spec (exists_isThetaZero h hM ρ))

variable {LL : Type} [Field LL] [NumberField LL] {ι : LL →+* ℂ}

def gxOf (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) (imM ι)) (a : D.what₂.Tau → imM ι) :
    GlobalExtra LL D.what₂.Tau where
  Om τ s := Real.exp (-logMet (imM ι) (lamOf D cc δ) (rhoOf ι s) (a τ))
  Om_pos _ _ := Real.exp_pos _
  thOne s := Real.sqrt (th0NormSq D (imM ι) (lamOf D cc δ) (rhoOf ι s))
  thOne_pos s := Real.sqrt_pos.2 (th0NormSq_pos h hM _)

theorem extraTie_gxOf (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) (imM ι)) {a : D.what₂.Tau → imM ι}
    (ha : ∀ τ, Submodule.span (𝓞 (imM ι)) {a τ} = ellT D (imM ι) τ) :
    ExtraTie D cc δ ι (gxOf h hM a) a :=
  ⟨h, hM, ha, fun _ _ => rfl, fun s t ht => by
    rw [← th0NormSq_eq h hM _ ht]
    exact Real.sq_sqrt (th0NormSq_pos h hM _).le⟩

def withGx (D : D7) (G : GlobalExtra D.what₂.LL D.what₂.Tau) : D7 := { D with gx := G }

theorem perTie_withGx_iff (G : GlobalExtra D.what₂.LL D.what₂.Tau) :
    PerTie (withGx D G) cc δ ↔ ∃ a, ExtraTie D cc δ D.what₂.embLL G a := by
  refine (perTie_iff (withGx D G) cc δ).trans ?_
  exact exists_congr fun a => ⟨fun h => ⟨h.crv, h.data, h.gen, h.om, h.th⟩,
    fun h => ⟨h.crv, h.data, h.gen, h.om, h.th⟩⟩

theorem exists_extraTie (h : Crv D cc δ) (M : IntermediateField ℚ ℂ) [NumberField M]
    (hM : DataIn D (tor0 D cc δ) M) (ha : ∀ τ, ∃ a : M, Submodule.span (𝓞 M) {a} = ellT D M τ) :
    ∃ (G : GlobalExtra M D.what₂.Tau) (a : D.what₂.Tau → imM (M.val : M →+* ℂ)),
      ExtraTie D cc δ (M.val : M →+* ℂ) G a := by
  have key : ∀ (M' : IntermediateField ℚ ℂ) [NumberField M'], M' = M →
      DataIn D (tor0 D cc δ) M' ∧ ∀ τ, ∃ a : M', Submodule.span (𝓞 M') {a} = ellT D M' τ := by
    rintro M' _ rfl
    exact ⟨hM, ha⟩
  obtain ⟨h1, h2⟩ := key (imM (M.val : M →+* ℂ)) M.fieldRange_val
  choose a ha' using h2
  exact ⟨_, a, extraTie_gxOf h h1 ha'⟩

namespace ExtraTie

variable {G : GlobalExtra LL D.what₂.Tau} {a : D.what₂.Tau → imM ι} (T : ExtraTie D cc δ ι G a)
include T

theorem ne_zero (τ : D.what₂.Tau) : a τ ≠ 0 := ne_zero_of_span_eq T.data.1 (T.gen τ)

theorem om_eq (τ : D.what₂.Tau) (s : LL →+* ℂ) :
    G.Om τ s = area (lamConj (imM ι) (rhoOf ι s) (lamOf D cc δ)) /
      (Real.pi * ‖rhoOf ι s (a τ)‖ ^ 2) := by
  rw [T.om, exp_neg_logMet (area_lamConj_pos T.crv T.data _) (T.ne_zero τ)]

theorem log_om (τ : D.what₂.Tau) (s : LL →+* ℂ) :
    Real.log (G.Om τ s) = -logMet (imM ι) (lamOf D cc δ) (rhoOf ι s) (a τ) := by
  rw [T.om, Real.log_exp]

theorem th_sq (s : LL →+* ℂ) :
    G.thOne s ^ 2 = th0NormSq D (imM ι) (lamOf D cc δ) (rhoOf ι s) :=
  T.th s _ (Classical.epsilon_spec (exists_isThetaZero T.crv T.data _))

theorem logOmMean_eq (τ : D.what₂.Tau) :
    G.logOmMean τ = meanLogOm D (lamOf D cc δ) (imM ι) τ := by
  rw [meanLogOm_eq_of_gen T.data.1 (area_lamConj_pos T.crv T.data) (T.gen τ), GlobalExtra.logOmMean,
    card_emb ι, ← sum_rhoOf ι, ← Finset.sum_neg_distrib]
  simp only [T.log_om]

end ExtraTie

namespace PerTie

variable (T : PerTie D cc δ)
include T

theorem crv : Crv D cc δ := T.1

theorem data : DataIn D (tor0 D cc δ) (coefM D) := T.2.1

theorem logOmMean_eq (τ : D.what₂.Tau) :
    D.gx.logOmMean τ = meanLogOm D (lamOf D cc δ) (coefM D) τ := by
  obtain ⟨a, h⟩ := (perTie_iff D cc δ).1 T
  exact h.logOmMean_eq τ

theorem th_sq (s : D.what₂.LL →+* ℂ) :
    D.gx.thOne s ^ 2 = th0NormSq D (coefM D) (lamOf D cc δ) (rhoOf D.what₂.embLL s) := by
  obtain ⟨a, h⟩ := (perTie_iff D cc δ).1 T
  exact h.th_sq s

end PerTie

example (T : PerTie D cc δ) :
    ¬ PerTie (withGx D { D.gx with
      thOne := fun s => 2 * D.gx.thOne s
      thOne_pos := fun s => mul_pos two_pos (D.gx.thOne_pos s) }) cc δ := by
  rw [perTie_withGx_iff]
  rintro ⟨a, h⟩
  have h1 := h.th_sq D.what₂.embLL
  rw [← T.th_sq] at h1
  have := D.gx.thOne_pos D.what₂.embLL
  simp only at h1
  nlinarith

example {G G' : GlobalExtra LL D.what₂.Tau} {a a' : D.what₂.Tau → imM ι} (T : ExtraTie D cc δ ι G a)
    (T' : ExtraTie D cc δ ι G' a') (τ : D.what₂.Tau) : G.logOmMean τ = G'.logOmMean τ := by
  rw [T.logOmMean_eq, T'.logOmMean_eq]

example (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) (imM ι)) (a : D.what₂.Tau → imM ι)
    (τ : D.what₂.Tau) (ha : a τ ≠ 0) (s : LL →+* ℂ) :
    (gxOf h hM (fun τ => 2 * a τ)).Om τ s = (gxOf h hM a).Om τ s / 4 := by
  change Real.exp _ = Real.exp _ / 4
  rw [exp_neg_logMet (area_lamConj_pos h hM _) ha,
    exp_neg_logMet (area_lamConj_pos h hM _) (mul_ne_zero two_ne_zero ha), map_mul, map_ofNat, norm_mul]
  simp only [Complex.norm_ofNat]
  ring

example : ¬ PerTie D ⊥ δ := fun T => T.crv.1.1 rfl

end Comparison₂

section Free

variable {D : D7}

theorem sum_dual_family {r : ℕ} {a a' : Fin r → D.host.E}
    (h : ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k)
    (τ σ : D.what₂.Tau) :
    ∑ k, embT D τ (D.host.conj (a' k)) * embT D σ (a k) = if τ = σ then 1 else 0 := by
  rw [← sub_eq_zero]
  refine GlobalTheory.OrthoCoord.embT_indep
    (fun τ => ∑ k, embT D τ (D.host.conj (a' k)) * embT D σ (a k) - if τ = σ then 1 else 0) (fun t => ?_) τ
  have h1 := congrArg (embT D σ) (h t)
  rw [map_sum] at h1
  have h2 : ∀ k, embT D σ ((Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k) =
      ∑ τ, embT D τ (D.host.conj (a' k)) * embT D σ (a k) * embT D τ t := fun k => by
    rw [Algebra.smul_def, map_mul]
    have e1 := GlobalTheory.InducedType.restrict_K D σ (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k)))
    have e2 := GlobalTheory.InducedType.sum_eq_trace D (t * D.host.conj (a' k))
    erw [e1, ← e2]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul]; ring
  simp only [h2] at h1
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm, ← h1, sub_self]

theorem mem_ellT_iff {M : IntermediateField ℚ ℂ} [NumberField M] (hM : ∀ τ x, embT D τ x ∈ M)
    (τ : D.what₂.Tau) (x : M) :
    x ∈ ellT D M τ ↔ ∀ y ∈ D.host.AA0, IsIntegral ℤ ((x : ℂ) * embT D τ (D.host.conj y)) := by
  unfold ellT
  rw [Submodule.mem_comap]
  constructor
  · intro hx y hy
    have key : ∀ v ∈ mmM D M, IsIntegral ℤ (∑ σ, (v σ : ℂ) * embT D σ (D.host.conj y)) := by
      intro v hv
      unfold mmM at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        simp only [TaylorLogMetric.liftM, dif_pos (hM _ _), ← map_mul]
        have e2 := GlobalTheory.InducedType.sum_eq_trace D (a * D.host.conj y)
        erw [e2]
        obtain ⟨c, hc⟩ := (factMMUnimodular D.R D.host a).1 ha y hy
        have hi : IsIntegral ℤ (Algebra.trace D.host.K D.host.E (a * D.host.conj y)) := by
          rw [← hc]; exact c.isIntegral_coe
        exact map_isIntegral_int (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) hi
      | zero => simpa using isIntegral_zero
      | add x y _ _ hx hy =>
        simpa only [Pi.add_apply, IntermediateField.coe_add, add_mul, Finset.sum_add_distrib] using hx.add hy
      | smul c x _ hx =>
        have hc : IsIntegral ℤ (((c : M) : ℂ)) := map_isIntegral_int (M.val : M →+* ℂ) c.isIntegral_coe
        convert hc.mul hx using 1
        · rfl
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← mul_assoc]
        rfl
    have := key _ hx
    rwa [Finset.sum_eq_single τ (fun σ _ hσ => by simp [hσ]) (by simp), LinearMap.coe_single,
      Pi.single_eq_same] at this
  · intro hx
    obtain ⟨r, a, a', ha, ha', h⟩ := GlobalTheory.exists_trace_dual_family_halfDifferent D
    let c : Fin r → 𝓞 M := fun k => ⟨x * ⟨_, hM τ (D.host.conj (a' k))⟩,
      (isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective).1 (hx _ (ha' k))⟩
    have : ∑ k, c k • (fun σ => TaylorLogMetric.liftM M (embT D σ (a k))) ∈ mmM D M :=
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a k, ha k, rfl⟩)
    convert this using 1
    funext σ
    apply Subtype.ext
    have e : ∀ k, (((c k • (fun σ => TaylorLogMetric.liftM M (embT D σ (a k)))) σ : M) : ℂ) =
        (x : ℂ) * (embT D τ (D.host.conj (a' k)) * embT D σ (a k)) := fun k => by
      simp only [TaylorLogMetric.liftM, dif_pos (hM _ _), Pi.smul_apply]
      rw [← mul_assoc]
      rfl
    rw [Finset.sum_apply, IntermediateField.coe_sum]
    simp only [e]
    rw [← Finset.mul_sum, sum_dual_family h]
    by_cases hσ : τ = σ
    · subst hσ; simp
    · simp [hσ, Ne.symm hσ]

theorem exists_pow_principal_fractionalIdeal (D : D7) : ∃ (h : ℕ) (α : D.host.E), 0 < h ∧ α ≠ 0 ∧
    ((D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) ^ h = Submodule.span (𝓞 D.host.E) {α} := by
  have h0 : D.host.AA0 ≠ 0 := fun h => by
    have := GlobalTheory.AdelicApprox.one_mem_inverse_halfDifferent D
    rw [h] at this
    simp at this
  have h1 := pow_card_eq_one (G := ClassGroup (𝓞 D.host.E))
    (x := ClassGroup.mk D.host.E (Units.mk0 _ h0))
  rw [← map_pow, ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨α, hα⟩ := h1
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, FractionalIdeal.coe_pow] at hα
  refine ⟨_, α, Fintype.card_pos, ?_, hα⟩
  rintro rfl
  have := Submodule.pow_mem_pow _ (GlobalTheory.AdelicApprox.one_mem_inverse_halfDifferent D) (Fintype.card (ClassGroup (𝓞 D.host.E)))
  rw [hα] at this
  simp at this

theorem span_inv_eq_ellT {M : IntermediateField ℚ ℂ} [NumberField M] (hM : ∀ τ x, embT D τ x ∈ M)
    {h : ℕ} {α : D.host.E} (hh : 0 < h) (hα : α ≠ 0)
    (hA : ((D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) ^ h = Submodule.span (𝓞 D.host.E) {α})
    (τ : D.what₂.Tau) (γ : M) (hγ : (γ : ℂ) ^ h = embT D τ (D.host.conj α)) :
    Submodule.span (𝓞 M) {γ⁻¹} = ellT D M τ := by
  let ψ : D.host.E →+* ℂ := (embT D τ).comp (D.host.conj : D.host.E →+* D.host.E)
  have hψ : ∀ y, embT D τ (D.host.conj y) = ψ y := fun _ => rfl
  rw [hψ] at hγ
  have hγ0 : (γ : ℂ) ≠ 0 := fun h0 => by
    rw [h0, zero_pow hh.ne'] at hγ
    exact (map_ne_zero ψ).2 hα hγ.symm
  have hγ0' : γ ≠ 0 := fun h0 => hγ0 (by rw [h0]; rfl)
  ext x
  rw [mem_ellT_iff hM, Submodule.mem_span_singleton]
  simp only [hψ]
  constructor
  · rintro ⟨c, rfl⟩ y hy
    have hc : IsIntegral ℤ (((c : M) : ℂ)) := map_isIntegral_int (M.val : M →+* ℂ) c.isIntegral_coe
    have h1 := Submodule.pow_mem_pow _ (show y ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) from hy) h
    rw [hA, Submodule.mem_span_singleton] at h1
    obtain ⟨r, hr⟩ := h1
    have h2 : IsIntegral ℤ (ψ y / γ) := by
      refine IsIntegral.of_pow hh ?_
      rw [div_pow, ← map_pow, ← hr, hγ, Algebra.smul_def, map_mul,
        mul_div_cancel_right₀ _ ((map_ne_zero ψ).2 hα)]
      exact map_isIntegral_int ψ r.isIntegral_coe
    convert hc.mul h2 using 1
    · rfl
    change ((c : M) : ℂ) * ((γ⁻¹ : M) : ℂ) * ψ y = _
    rw [IntermediateField.coe_inv]
    ring
  · intro hx
    have key : ∀ (n : ℕ), ∀ z ∈ ((D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) ^ n,
        IsIntegral ℤ ((x : ℂ) ^ n * ψ z) := by
      intro n z hz
      induction hz using Submodule.pow_induction_on_left' with
      | algebraMap r => simpa using map_isIntegral_int ψ r.isIntegral_coe
      | add _ _ _ _ _ h1 h2 => simpa only [map_add, mul_add] using h1.add h2
      | mem_mul m hm i z _ hz =>
        convert (hx m hm).mul hz using 1
        · rfl
        rw [map_mul, pow_succ]; ring
    have h1 := key h α (hA ▸ Submodule.mem_span_singleton_self α)
    rw [← hγ, ← mul_pow] at h1
    refine ⟨⟨x * γ, (isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective).1
      (IsIntegral.of_pow hh h1)⟩, ?_⟩
    change x * γ * γ⁻¹ = x
    exact mul_inv_cancel_right₀ hγ0' x

theorem exists_field_gen {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ)
    (M₀ : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M₀] :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), M₀ ≤ M ∧ DataIn D (tor0 D cc δ) M ∧
      ∀ τ, ∃ a : M, Submodule.span (𝓞 M) {a} = ellT D M τ := by
  obtain ⟨n, α, hn, hα, hA⟩ := exists_pow_principal_fractionalIdeal D
  choose γ hγ using fun τ : D.what₂.Tau =>
    IsAlgClosed.exists_pow_nat_eq (embT D τ (D.host.conj α)) hn
  obtain ⟨⟨hT, hg2, hg3⟩, -⟩ :=
    (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D (GlobalTheory.InducedType.induced_type D).1).2 cc δ h
  let S : Set ℂ := insert (g2 (lamOf D cc δ)) (insert (g3 (lamOf D cc δ)) (Set.range γ))
  have hS : ∀ x ∈ S, IsIntegral ℚ x := by
    rintro x (rfl | rfl | ⟨τ, rfl⟩)
    · exact (mem_algebraicClosure_iff.1 hg2).isIntegral
    · exact (mem_algebraicClosure_iff.1 hg3).isIntegral
    · refine IsIntegral.of_pow hn ?_
      rw [hγ]
      exact (mem_algebraicClosure_iff.1 (hT τ _)).isIntegral
  haveI : Finite S := (((Set.finite_range γ).insert _).insert _).to_subtype
  haveI h1 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin hS
  haveI h2 : FiniteDimensional ℚ (⨆ τ, imM (embT D τ) : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  let M : IntermediateField ℚ ℂ := M₀ ⊔ (IntermediateField.adjoin ℚ S ⊔ ⨆ τ, imM (embT D τ))
  haveI : FiniteDimensional ℚ M := IntermediateField.finiteDimensional_sup _ _
  haveI hN : NumberField M := {}
  have hSM : ∀ x ∈ S, x ∈ M := fun x hx =>
    (le_sup_of_le_right le_sup_left : IntermediateField.adjoin ℚ S ≤ M)
      (IntermediateField.subset_adjoin ℚ S hx)
  have hTM : ∀ τ x, embT D τ x ∈ M := fun τ x =>
    (le_sup_of_le_right (le_sup_of_le_right (le_iSup (fun τ => imM (embT D τ)) τ)) : imM (embT D τ) ≤ M)
      ⟨x, rfl⟩
  refine ⟨M, hN, le_sup_left, ⟨hTM, hSM _ (Or.inl rfl), hSM _ (Or.inr (Or.inl rfl))⟩, fun τ => ?_⟩
  exact ⟨_, span_inv_eq_ellT hTM hn hα hA τ ⟨γ τ, hSM _ (Or.inr (Or.inr ⟨τ, rfl⟩))⟩ (hγ τ)⟩

theorem exists_extraTie_of_crv {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ)
    (M₀ : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M₀] :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), M₀ ≤ M ∧
      ∃ (G : GlobalExtra M D.what₂.Tau) (a : D.what₂.Tau → imM (M.val : M →+* ℂ)),
        ExtraTie D cc δ (M.val : M →+* ℂ) G a := by
  obtain ⟨M, hN, h0, hM, ha⟩ := exists_field_gen h M₀
  exact ⟨M, hN, h0, exists_extraTie h M hM ha⟩

example (D : D7) : ∃ (δ : ℂ) (LL : Type) (_ : Field LL) (_ : NumberField LL) (ι : LL →+* ℂ)
    (G : GlobalExtra LL D.what₂.Tau) (a : D.what₂.Tau → imM ι), ExtraTie D ⊤ δ ι G a := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (lamOf D ⊤ 1)) (n := 12) (by norm_num)
  have h : Crv D ⊤ δ := ⟨⟨top_ne_bot, by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _⟩, hδ⟩
  obtain ⟨M, hN, -, G, a, T⟩ := exists_extraTie_of_crv h ⊥
  exact ⟨δ, M, inferInstance, hN, _, G, a, T⟩

end Free

end GlobalTheory.Glob
