import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalMirabolicMovingRowToLast
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParsevalContinuousPeriodicAdelicRationalQuotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetLIntegralAverageAbelianQuotientStatement

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.MirTower

section Polar

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem memLp_two_of_lintegral {μ : Measure X} {f : X → ℂ} (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤) : MemLp f 2 μ := by
  refine ⟨hf, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simpa using h.lt_top

theorem integral_mul_conj_eq {μ : Measure X} {f f' : X → ℂ} (hf : MemLp f 2 μ) (hf' : MemLp f' 2 μ) :
    Integrable (fun x => f x * conj (f' x)) μ ∧ ∫ x, f x * conj (f' x) ∂μ =
      (((∫⁻ x, ‖f x + 1 * f' x‖ₑ ^ 2 ∂μ).toReal : ℂ) - (∫⁻ x, ‖f x + (-1) * f' x‖ₑ ^ 2 ∂μ).toReal +
        Complex.I * ((∫⁻ x, ‖f x + Complex.I * f' x‖ₑ ^ 2 ∂μ).toReal -
          (∫⁻ x, ‖f x + (-Complex.I) * f' x‖ₑ ^ 2 ∂μ).toReal)) / 4 := by
  have hm : ∀ c : ℂ, MemLp (fun x => f x + c * f' x) 2 μ := fun c => hf.add (hf'.const_mul c)
  have hi : ∀ c : ℂ, Integrable (fun x => ((‖f x + c * f' x‖ ^ 2 : ℝ) : ℂ)) μ := fun c =>
    ((memLp_two_iff_integrable_sq_norm (hm c).1).1 (hm c)).ofReal
  have he : ∀ c : ℂ, ((∫⁻ x, ‖f x + c * f' x‖ₑ ^ 2 ∂μ).toReal : ℂ) = ∫ x, ((‖f x + c * f' x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
    intro c
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x + c * f' x‖ ^ 2)
      (Filter.Eventually.of_forall fun w => by positivity) ((hm c).1.norm.pow 2)]
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hp : (fun x => f x * conj (f' x)) = fun x =>
      (((‖f x + 1 * f' x‖ ^ 2 : ℝ) : ℂ) - (‖f x + (-1) * f' x‖ ^ 2 : ℝ) +
        Complex.I * ((‖f x + Complex.I * f' x‖ ^ 2 : ℝ) - (‖f x + (-Complex.I) * f' x‖ ^ 2 : ℝ))) / 4 := by
    funext x
    simp only [Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp <;> ring
  rw [hp]
  refine ⟨(((hi 1).sub (hi (-1))).add (((hi _).sub (hi _)).const_mul _)).div_const _, ?_⟩
  rw [integral_div, integral_add, integral_const_mul, integral_sub (hi _) (hi _), integral_sub (hi _) (hi _)]
  · simp only [he]
  · exact (hi 1).sub (hi (-1))
  · exact ((hi _).sub (hi _)).const_mul _

theorem integral_mul_conj_eq_of_lintegral {μ : Measure X} {ν : Measure Y} {f f' : X → ℂ} {h h' : Y → ℂ}
    (hf : Measurable f) (hf' : Measurable f') (hh : Measurable h) (hh' : Measurable h')
    {v : X → ℝ≥0} {w : Y → ℝ≥0} (hv : Measurable v) (hw : Measurable w)
    (H : ∀ c d : ℂ, ∫⁻ x, ‖c * f x + d * f' x‖ₑ ^ 2 * v x ∂μ = ∫⁻ y, ‖c * h y + d * h' y‖ₑ ^ 2 * w y ∂ν)
    (h1 : ∫⁻ x, ‖f x‖ₑ ^ 2 * v x ∂μ ≠ ⊤) (h2 : ∫⁻ x, ‖f' x‖ₑ ^ 2 * v x ∂μ ≠ ⊤) :
    Integrable (fun x => f x * conj (f' x) * (v x : ℝ)) μ ∧ Integrable (fun y => h y * conj (h' y) * (w y : ℝ)) ν ∧
      ∫ x, f x * conj (f' x) * (v x : ℝ) ∂μ = ∫ y, h y * conj (h' y) * (w y : ℝ) ∂ν := by
  have e1 : ∀ φ : X → ℂ, Measurable φ →
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂(μ.withDensity fun x => v x) = ∫⁻ x, ‖φ x‖ₑ ^ 2 * v x ∂μ := fun φ hφ => by
    rw [lintegral_withDensity_eq_lintegral_mul _ hv.coe_nnreal_ennreal (hφ.enorm.pow_const 2)]
    simp only [Pi.mul_apply, mul_comm]
  have e2 : ∀ φ : Y → ℂ, Measurable φ →
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂(ν.withDensity fun x => w x) = ∫⁻ x, ‖φ x‖ₑ ^ 2 * w x ∂ν := fun φ hφ => by
    rw [lintegral_withDensity_eq_lintegral_mul _ hw.coe_nnreal_ennreal (hφ.enorm.pow_const 2)]
    simp only [Pi.mul_apply, mul_comm]
  have H1 := H 1 0
  have H2 := H 0 1
  simp only [one_mul, zero_mul, add_zero, zero_add] at H1 H2
  obtain ⟨a1, a2⟩ := integral_mul_conj_eq (μ := μ.withDensity fun x => v x)
    (memLp_two_of_lintegral hf.aestronglyMeasurable (by rwa [e1 f hf]))
    (memLp_two_of_lintegral hf'.aestronglyMeasurable (by rwa [e1 f' hf']))
  obtain ⟨b1, b2⟩ := integral_mul_conj_eq (μ := ν.withDensity fun x => w x)
    (memLp_two_of_lintegral hh.aestronglyMeasurable (by rwa [e2 h hh, ← H1]))
    (memLp_two_of_lintegral hh'.aestronglyMeasurable (by rwa [e2 h' hh', ← H2]))
  have H3 : ∀ d : ℂ, ∫⁻ x, ‖f x + d * f' x‖ₑ ^ 2 ∂(μ.withDensity fun x => v x) =
      ∫⁻ y, ‖h y + d * h' y‖ₑ ^ 2 ∂(ν.withDensity fun x => w x) := fun d => by
    rw [e1 (fun x => f x + d * f' x) (hf.add (hf'.const_mul d)), e2 (fun y => h y + d * h' y) (hh.add (hh'.const_mul d))]
    simpa only [one_mul] using H 1 d
  simp only [H3] at a2
  rw [← b2, integral_withDensity_eq_integral_smul hv, integral_withDensity_eq_integral_smul hw] at a2
  rw [integrable_withDensity_iff_integrable_smul hv] at a1
  rw [integrable_withDensity_iff_integrable_smul hw] at b1
  simp only [NNReal.smul_def, Complex.real_smul, mul_comm ((_ : ℝ) : ℂ)] at a1 b1 a2
  exact ⟨a1, b1, a2⟩

end Polar

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem secondCountable_GA : SecondCountableTopology (GA E a) := by
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem dot_algebraMap {ι : Type} [Fintype ι] (ξ c : ι → E) :
    dot ξ (fun t => algebraMap E (Ad E) (c t)) = algebraMap E (Ad E) (∑ t, ξ t * c t) := by
  simp only [dot, map_sum, map_mul]

theorem good_left_mirU (hψ : StdPsi ψ) {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) {γ : GL (Fin a) E}
    (hγ : γ ∈ mirU E a m) (g : GA E a) : f (ratGL E a γ * g) = f g := by
  obtain ⟨u, hu, g₀, hg₀, rfl, h1, -⟩ := exists_peel (Nat.le_succ m) hγ
  rw [map_mul, mul_assoc, invariant_colGen (ratGL E a) f (fun k hk y g => by
    rw [ratGL_blkU, hf.law k hk, dot_algebraMap, hψ.rat, one_mul]) hu]
  refine hf.left g₀ (fun i k h => ?_) g
  by_cases hk : m < (k : ℕ)
  · exact h1 i k hk
  · exact hg₀ i k (by omega) (by change (k : ℕ) ≤ i; omega)

theorem good_comb {m : ℕ} {f f' : GA E a → ℂ} (hf : Good ψ m f) (hf' : Good ψ m f') (c d : ℂ) :
    Good ψ m (fun g => c * f g + d * f' g) where
  cont := (continuous_const.mul hf.cont).add (continuous_const.mul hf'.cont)
  left γ hγ g := by rw [hf.left γ hγ, hf'.left γ hγ]
  law k hk y g := by rw [hf.law k hk, hf'.law k hk]; ring
  van r h0 hr g := by
    have p1 := per_blk (r := r) (m := m) (f := fun g => c * f g) (continuous_const.mul hf.cont)
      (fun x g => by rw [hf.left _ (isMir_blkU x)]) g
    have p2 := per_blk (r := r) (m := m) (f := fun g => d * f' g) (continuous_const.mul hf'.cont)
      (fun x g => by rw [hf'.left _ (isMir_blkU x)]) g
    have := GlobalTheory.T.quotientAverage_add_of_periodic _ (ratV E (UnipotentBlockColumnIndex a r m)) (isCoLat_ratV E _) _ _ p1 p2
    rw [avg_const_mul, avg_const_mul, hf.van r h0 hr, hf'.van r h0 hr] at this
    simpa using this

theorem good_smul {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) (c : ℂ) : Good ψ m (fun g => c * f g) := by
  simpa using good_comb hf hf c 0

theorem sum_eLast_mul {m : ℕ} (hm : m + 1 < a) (φ : Fin a → E) :
    ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * φ s.1.1 = φ ⟨m, by omega⟩ := by
  rw [Finset.sum_eq_single (⟨(⟨m, by omega⟩, ⟨m + 1, hm⟩), by simp⟩ : UnipotentBlockColumnIndex a (m + 1) (m + 1))]
  · simp [eLast]
  · intro s _ hs
    rw [eLast, if_neg, zero_mul]
    intro e
    have := s.2
    exact hs (Subtype.ext (Prod.ext (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))))
  · simp

theorem exists_transversal {m : ℕ} (hm : m + 1 < a) :
    ∃ (γ : {ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E // ξ ≠ 0} → GL (Fin a) E)
      (e : ratMirU E a m × {ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E // ξ ≠ 0} ≃ ratMirU E a (m + 1)),
      (∀ ξ, IsMir (m + 1) (γ ξ) ∧ (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * (γ ξ).val s.1.1 t.1.1) = ξ.1) ∧
        ∀ p, (e p : GA E a) = p.1 * ratGL E a (γ p.2) := by
  choose γ hγ hrow using fun ξ : {ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E // ξ ≠ 0} => mir_exists_row E a m hm ξ.1 ξ.2
  have hγU : ∀ ξ, γ ξ ∈ mirU E a (m + 1) := fun ξ i k hi _ => hγ ξ i k (Or.inl hi)
  let i₀ : Fin a := ⟨m, by omega⟩
  have hrow' : ∀ ξ (t : UnipotentBlockColumnIndex a (m + 1) (m + 1)), (γ ξ).val i₀ t.1.1 = ξ.1 t := fun ξ t => by
    rw [← hrow ξ t, sum_eLast_mul hm (fun i => (γ ξ).val i t.1.1)]
  have hδ : ∀ δ ∈ mirU E a m, ∀ ξ (t : UnipotentBlockColumnIndex a (m + 1) (m + 1)), (δ * γ ξ).val i₀ t.1.1 = ξ.1 t := by
    intro δ hδ ξ t
    rw [Units.val_mul, mul_apply_congr (hγU ξ) (x' := 1) (fun l hl => hδ i₀ l le_rfl (by change (l : ℕ) ≤ m; omega)) t.2.1,
      Matrix.one_mul, hrow']
  let φ : ratMirU E a m × {ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E // ξ ≠ 0} → ratMirU E a (m + 1) := fun p =>
    ⟨p.1 * ratGL E a (γ p.2), mul_mem (Subgroup.map_mono (mirU_mono (Nat.le_succ m)) p.1.2) ⟨_, hγU _, rfl⟩⟩
  refine ⟨γ, Equiv.ofBijective φ ⟨?_, ?_⟩, fun ξ => ⟨hγ ξ, funext (hrow ξ)⟩, fun _ => rfl⟩
  · rintro ⟨⟨_, δ, hδ1, rfl⟩, ξ⟩ ⟨⟨_, δ', hδ2, rfl⟩, ξ'⟩ h
    have h1 : δ * γ ξ = δ' * γ ξ' :=
      GlobalTheory.ThetaUnfold.ratGL_injective (by simpa only [map_mul] using congrArg Subtype.val h)
    have h2 : ξ = ξ' := Subtype.ext (funext fun t => by rw [← hδ δ hδ1 ξ t, h1, hδ δ' hδ2])
    subst h2
    obtain rfl := mul_right_cancel h1
    rfl
  · rintro ⟨_, x, hx, rfl⟩
    let ξ₀ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E := fun t => x.val i₀ t.1.1
    have hl : ∀ l : Fin a, (l : ℕ) < m + 1 → ∃ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), t.1.1 = l := fun l hl =>
      ⟨⟨(l, ⟨m + 1, hm⟩), hl, le_rfl, le_rfl⟩, rfl⟩
    have h0 : ξ₀ ≠ 0 := fun h => by
      have := mul_apply_congr ((mirU E a (m + 1)).inv_mem hx) (x := x.val) (x' := 0) (i := i₀) (k := i₀) (fun l h' => by
        obtain ⟨t, rfl⟩ := hl l h'
        exact congrFun h t) (Nat.lt_succ_self m)
      simp at this
    have h1 : x * (γ ⟨ξ₀, h0⟩)⁻¹ ∈ mirU E a m := by
      intro i k hi hk
      by_cases him : m + 1 ≤ (i : ℕ)
      · exact (mirU E a (m + 1)).mul_mem hx ((mirU E a (m + 1)).inv_mem (hγU _)) i k him hk
      · obtain rfl : i = i₀ := Fin.ext (by change (i : ℕ) = m; omega)
        rw [Units.val_mul, mul_apply_congr ((mirU E a (m + 1)).inv_mem (hγU _)) (x' := (γ ⟨ξ₀, h0⟩).val) (fun l h' => by
          obtain ⟨t, rfl⟩ := hl l h'
          exact (hrow' ⟨ξ₀, h0⟩ t).symm) (Nat.lt_succ_of_le hk), Units.mul_inv]
    refine ⟨⟨⟨_, _, h1, rfl⟩, ⟨ξ₀, h0⟩⟩, Subtype.ext ?_⟩
    change ratGL E a _ * ratGL E a _ = _
    rw [← map_mul, inv_mul_cancel_right]

section Step

variable [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] (μ : Measure (GA E a)) [SFinite μ] [μ.IsMulLeftInvariant]

theorem lintegral_step (hψ : StdPsi ψ) {m : ℕ} (hm : m + 1 < a) {𝓕 𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratMirU E a (m + 1)) 𝓕 μ) (h𝓕' : IsFundamentalDomain (ratMirU E a m) 𝓕' μ)
    (w : GA E a → ℝ≥0∞) (hw : Measurable w) (hwΓ : ∀ γ ∈ mirU E a (m + 1), ∀ g, w (ratGL E a γ * g) = w g)
    (hwU : ∀ k, m < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, w (blkU y * g) = w g)
    {f : GA E a → ℂ} (hf : Good ψ (m + 1) f) :
    ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ = ∫⁻ g in 𝓕', ‖colT ψ (m + 1) f g‖ₑ ^ 2 * w g ∂μ := by
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E)) := inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Ad E))
  haveI : LocallyCompactSpace (GA E a) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI := secondCountable_GA (E := E) (a := a)
  haveI : DiscreteTopology (ratMirU E a (m + 1)) := discrete_of_le_range (Subgroup.map_le_range _ _)
  haveI : Countable (ratMirU E a (m + 1)) := GlobalTheory.countable_of_discrete_subgroup _
  letI : MeasurableSpace (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) := borel _
  haveI : BorelSpace (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) := ⟨rfl⟩
  have hL := isCoLat_ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))
  haveI := hL.1
  haveI : Countable (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) := GlobalTheory.countable_of_discrete_addSubgroup _
  obtain ⟨ν, D, hν, hD, hνD⟩ := exists_fundamentalDomain_mass_one _ _ hL
  have hT := GlobalTheory.CuspRep.Generic.good_colT hψ hm hf
  have hnorm : ∀ k, m + 1 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, ‖f (blkU y * g)‖ₑ = ‖f g‖ₑ := fun k hk y g => by
    rw [hf.law k hk, enorm_mul, ← ofReal_norm (ψ _), hψ.norm, ENNReal.ofReal_one, one_mul]
  have havg := GlobalTheory.T.setLIntegral_average_abelian_quotient_alt (GA E a) (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) μ (ratMirU E a (m + 1)) (lateU (Ad E) a (m + 1))
    (isClosed_lateU _) (by rintro _ ⟨γ, hγ, rfl⟩ u hu; exact conj_mem_lateU (map_mem_mirU _ hγ) hu)
    (by
      obtain ⟨K, hK, h⟩ := exists_compact_lateU (E := E) (a := a) (m + 1)
      refine ⟨K, hK, fun u hu => ?_⟩
      obtain ⟨γ, h1, h2, h3⟩ := h u hu
      exact ⟨_, ⟨γ, mirU_mono (Nat.zero_le _) h1, rfl⟩, h2, h3⟩)
    blkU blkU_add (continuous_posU (isNil_blk a (m + 1) (m + 1))).measurable (blkU_mem_lateU le_rfl) ν (ratV E _)
    (by rintro _ ⟨c, rfl⟩; exact ⟨blkU c, blkU_mem_mirU _ c, ratGL_blkU c⟩) D hD hνD 𝓕 h𝓕
    (fun g => ‖f g‖ₑ ^ 2 * w g) ((hf.cont.measurable.enorm.pow_const 2).mul hw)
    (by rintro _ ⟨γ, hγ, rfl⟩ g; simp only [good_left_mirU hψ hf hγ, hwΓ γ hγ])
    (fun u hu => by
      obtain ⟨v, hv, y, rfl⟩ := exists_eq_colGen_mul_blkU hu
      refine ⟨y, fun g => ?_⟩
      rw [mul_assoc]
      exact invariant_colGen (MonoidHom.id _) (fun g => ‖f g‖ₑ ^ 2 * w g) (fun k hk z g => by
        simp only [MonoidHom.id_apply, hnorm k hk, hwU k (by omega)]) hv _)
  obtain ⟨γ, e, hγ, he⟩ := exists_transversal (E := E) hm
  rw [havg, ← GlobalTheory.ThetaUnfold.lintegral_unfold μ _ _ (fun ξ => ratGL E a (γ ξ)) e he h𝓕 h𝓕'
    (fun g => ‖colT ψ (m + 1) f g‖ₑ ^ 2 * w g)
    (by rintro _ ⟨δ, hδ, rfl⟩ g; simp only [good_left_mirU hψ hT hδ, hwΓ δ (mirU_mono (Nat.le_succ m) hδ)])
    ((hT.cont.measurable.enorm.pow_const 2).mul hw).aemeasurable]
  refine lintegral_congr fun g => ?_
  have hper : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g)) :=
    per_blk hf.cont (fun c g => hf.left _ (isMir_blkU c) g) g
  have h0 : coefF ψ (m + 1) 0 f g = 0 := by
    have e0 : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E, ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := fun x => by
      simp [dot]
    simp only [coefF, e0, one_mul]
    exact hf.van (m + 1) (Nat.succ_pos m) le_rfl g
  have hc : ∀ ξ, colT ψ (m + 1) f (ratGL E a (γ ξ) * g) = coefF ψ (m + 1) ξ.1 f g := fun ξ => by
    rw [colT, coefF_ratGL_mul E a ψ hψ m f hf.cont hf.left _ (hγ ξ).1, (hγ ξ).2]
  have hwγ : ∀ ξ, w (ratGL E a (γ ξ) * g) = w g := fun ξ => hwΓ _ (fun i k hi _ => (hγ ξ).1 i k (Or.inl hi)) g
  simp only [hwU (m + 1) (Nat.lt_succ_self m), hc, hwγ]
  rw [lintegral_mul_const _ (hper.1.measurable.enorm.pow_const 2), ENNReal.tsum_mul_right,
    ← GlobalTheory.T.parseval_continuous_periodic_adelicRationalQuotient E _ ψ hψ _ hper ν D hν hD hνD]
  congr 1
  refine (tsum_subtype_eq_of_support_subset (f := fun ξ => ‖coefF ψ (m + 1) ξ f g‖ₑ ^ 2) (s := {ξ | ξ ≠ 0}) ?_).symm
  rintro ξ hξ rfl
  simp [h0] at hξ

theorem lintegral_tower (hψ : StdPsi ψ) {m : ℕ} (hm : m < a ∨ m = 0) {𝓕 𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratMirU E a m) 𝓕 μ) (h𝓕' : IsFundamentalDomain (ratMirU E a 0) 𝓕' μ)
    (w : GA E a → ℝ≥0∞) (hw : Measurable w) (hwΓ : ∀ γ ∈ mirU E a m, ∀ g, w (ratGL E a γ * g) = w g)
    (hwU : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, w (blkU y * g) = w g)
    {f : GA E a → ℂ} (hf : Good ψ m f) :
    ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ = ∫⁻ g in 𝓕', ‖whit ψ m f g‖ₑ ^ 2 * w g ∂μ := by
  haveI := secondCountable_GA (E := E) (a := a)
  haveI : ∀ n, DiscreteTopology (ratMirU E a n) := fun n => discrete_of_le_range (Subgroup.map_le_range _ _)
  induction m generalizing f 𝓕 with
  | zero =>
    haveI : Countable (ratMirU E a 0) := GlobalTheory.countable_of_discrete_subgroup _
    haveI : SMulInvariantMeasure (ratMirU E a 0) (GA E a) μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : GA E a) s⟩
    refine h𝓕.setLIntegral_eq h𝓕' _ ?_
    rintro ⟨_, γ, hγ, rfl⟩ g
    change ‖f (ratGL E a γ * g)‖ₑ ^ 2 * w (ratGL E a γ * g) = _
    rw [good_left_mirU hψ hf hγ, hwΓ γ hγ]
  | succ m ih =>
    have h1 : m + 1 < a := by omega
    obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratMirU E a m)
    rw [lintegral_step μ hψ h1 h𝓕 (hD μ) w hw hwΓ (fun k hk => hwU k (by omega)) hf, whit_succ]
    exact ih (Or.inl (by omega)) (hD μ) (fun γ hγ => hwΓ γ (mirU_mono (Nat.le_succ m) hγ))
      (GlobalTheory.CuspRep.Generic.good_colT hψ h1 hf)

theorem integral_tower (hψ : StdPsi ψ) {m : ℕ} (hm : m < a ∨ m = 0) {𝓕 𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratMirU E a m) 𝓕 μ) (h𝓕' : IsFundamentalDomain (ratMirU E a 0) 𝓕' μ)
    (w : GA E a → ℝ≥0) (hw : Measurable w) (hwΓ : ∀ γ ∈ mirU E a m, ∀ g, w (ratGL E a γ * g) = w g)
    (hwU : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, w (blkU y * g) = w g)
    {f f' : GA E a → ℂ} (hf : Good ψ m f) (hf' : Good ψ m f')
    (h1 : ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ ≠ ⊤) (h2 : ∫⁻ g in 𝓕, ‖f' g‖ₑ ^ 2 * w g ∂μ ≠ ⊤) :
    IntegrableOn (fun g => f g * conj (f' g) * (w g : ℝ)) 𝓕 μ ∧
      IntegrableOn (fun g => whit ψ m f g * conj (whit ψ m f' g) * (w g : ℝ)) 𝓕' μ ∧
      ∫ g in 𝓕, f g * conj (f' g) * (w g : ℝ) ∂μ = ∫ g in 𝓕', whit ψ m f g * conj (whit ψ m f' g) * (w g : ℝ) ∂μ := by
  refine integral_mul_conj_eq_of_lintegral hf.cont.measurable hf'.cont.measurable
    (GlobalTheory.CuspRep.Generic.whit_good hψ m hm hf).1.cont.measurable
    (GlobalTheory.CuspRep.Generic.whit_good hψ m hm hf').1.cont.measurable hw hw (fun c d => ?_) h1 h2
  rw [lintegral_tower μ hψ hm h𝓕 h𝓕' (fun g => w g) hw.coe_nnreal_ennreal (fun γ hγ g => by rw [hwΓ γ hγ])
      (fun k hk y g => by rw [hwU k hk]) (good_comb hf hf' c d),
    GlobalTheory.CuspRep.Generic.whit_add hψ m hm (good_smul hf c) (good_smul hf' d),
    GlobalTheory.CuspRep.Generic.whit_smul, GlobalTheory.CuspRep.Generic.whit_smul]

end Step

end GlobalTheory.MirTower
