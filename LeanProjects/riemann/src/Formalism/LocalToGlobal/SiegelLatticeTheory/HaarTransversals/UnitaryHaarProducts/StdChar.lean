import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter

namespace Formalism.L2.SG.Pf.StdChar

variable (F : Type) [Field F] [NumberField F]

def psiA (x : Ainf F) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

theorem psiA_add (x y : Ainf F) : psiA F (x + y) = psiA F x * psiA F y := by
  have h : ∀ w : InfinitePlace F, (x + y) w = x w + y w := fun w => rfl
  simp only [psiA, h, map_add, Complex.add_re, Finset.sum_add_distrib]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem psiA_zero : psiA F 0 = 1 := by
  have h : ∀ w : InfinitePlace F, (0 : Ainf F) w = 0 := fun w => rfl
  simp [psiA, h]

theorem norm_exp_real (t : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
  first
    | (rw [Complex.norm_exp]; simp)
    | simp [Complex.norm_exp]
    | (rw [(show (2 * Real.pi * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring)]
       exact Complex.norm_exp_ofReal_mul_I _)

theorem continuous_psiA : Continuous (psiA F) := by
  have hp : ∀ w : InfinitePlace F, Continuous (fun x : Ainf F => x w) := fun w => continuous_apply w
  have hc : ∀ w : InfinitePlace F, Continuous (InfinitePlace.Completion.extensionEmbedding w) := by
    intro w
    first
      | exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
      | exact UniformSpace.Completion.continuous_extension
  have hs : Continuous (fun x : Ainf F =>
      (∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ)) :=
    continuous_finset_sum _ (fun w _ => Complex.continuous_re.comp ((hc w).comp (hp w)))
  unfold psiA
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hs))

def trR : F →+ ℝ :=
  AddMonoidHom.mk' (fun a => ∑ w : InfinitePlace F, (w.embedding a).re) (by
    intro a b
    simp only [map_add, Complex.add_re, Finset.sum_add_distrib])

theorem trR_int [IsTotallyReal F] (d : 𝓞 F) : ∃ n : ℤ, trR F (algebraMap (𝓞 F) F d) = n := by
  have hsurj : Function.Surjective (InfinitePlace.mk : (F →+* ℂ) → InfinitePlace F) :=
    fun w => ⟨w.embedding, InfinitePlace.mk_embedding w⟩
  have hreal : ∀ φ : F →+* ℂ, ComplexEmbedding.IsReal φ := fun φ =>
    InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
  have hinj : Function.Injective (InfinitePlace.mk : (F →+* ℂ) → InfinitePlace F) := by
    intro φ ψ h
    rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
    · exact h'
    · exact (ComplexEmbedding.isReal_iff.mp (hreal φ)).symm.trans h'
  have hsum : ∀ a : F, trR F a = ∑ φ : F →+* ℂ, (φ a).re := by
    intro a
    show (∑ w : InfinitePlace F, (w.embedding a).re) = _
    symm
    refine Fintype.sum_bijective _ ⟨hinj, hsurj⟩ _ _ (fun φ => ?_)
    rw [InfinitePlace.embedding_mk_eq_of_isReal (hreal φ)]
  have htr : ∀ a : F, trR F a = ((Algebra.trace ℚ F a : ℚ) : ℝ) := by
    intro a
    rw [hsum, ← Complex.re_sum]
    have h' : (∑ φ : F →+* ℂ, φ a) = ∑ σ : F →ₐ[ℚ] ℂ, σ a :=
      Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun φ => rfl)
    rw [h']
    first
      | rw [← trace_eq_sum_embeddings (E := ℂ) (x := a)]
      | rw [← Algebra.trace_eq_sum_embeddings (E := ℂ) (x := a)]
    first
      | rw [eq_ratCast (algebraMap ℚ ℂ), Complex.ratCast_re]
      | simp
  have hint : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F d)) := by
    apply Algebra.isIntegral_trace
    first
      | exact RingOfIntegers.isIntegral_coe d
      | exact d.2
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨n, ?_⟩
  rw [htr, ← hn]
  simp

theorem exists_psiF [IsTotallyReal F] : ∃ f : Af F →+ AddCircle (1 : ℝ),
    (∀ z ∈ Formalism.UG.intAd F, f z = 0) ∧ ∀ a : F, f (algebraMap F (Af F) a) = ((trR F a : ℝ) : AddCircle (1 : ℝ)) := by
  let U : AddSubgroup (Af F) := (Formalism.UG.intAd F).toAddSubgroup
  let j : F →+ Af F ⧸ U := (QuotientAddGroup.mk' U).comp (algebraMap F (Af F)).toAddMonoidHom
  let h : F →+ AddCircle (1 : ℝ) := (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (trR F)
  have hker : j.ker ≤ h.ker := by
    intro a ha
    rw [AddMonoidHom.mem_ker] at ha ⊢
    have hmem : algebraMap F (Af F) a ∈ Formalism.UG.intAd F :=
      (QuotientAddGroup.eq_zero_iff (algebraMap F (Af F) a)).mp ha
    have hmem' : ∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (Af F) a) v ∈ v.adicCompletionIntegers F := hmem
    have hval : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F a ≤ 1 := by
      intro v
      have h1 : (a : v.adicCompletion F) ∈ v.adicCompletionIntegers F := hmem' v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
      exact h1
    obtain ⟨d, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) (x := a) hval
    obtain ⟨n, hn⟩ := trR_int F d
    show ((trR F (algebraMap (𝓞 F) F d) : ℝ) : AddCircle (1 : ℝ)) = 0
    rw [hn]
    first
      | exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.intCast_mem_zmultiples_one n)
      | (rw [AddCircle.coe_eq_zero_iff]; exact ⟨n, by simp⟩)
  have hj : Function.Injective (QuotientAddGroup.kerLift j) := QuotientAddGroup.kerLift_injective j
  have hB : Module.Baer ℤ (AddCircle (1 : ℝ)) := by
    first
      | exact Module.Baer.of_divisible _
      | exact @Module.Baer.of_divisible _ _ (QuotientAddGroup.divisibleBy _)
  obtain ⟨g, hg⟩ := hB.extension_property (QuotientAddGroup.kerLift j).toIntLinearMap hj
    (QuotientAddGroup.lift j.ker h hker).toIntLinearMap
  refine ⟨g.toAddMonoidHom.comp (QuotientAddGroup.mk' U), ?_, ?_⟩
  · intro z hz
    have hz0 : (QuotientAddGroup.mk' U) z = 0 := (QuotientAddGroup.eq_zero_iff z).mpr hz
    show g.toAddMonoidHom ((QuotientAddGroup.mk' U) z) = 0
    rw [hz0, map_zero]
  · intro a
    exact LinearMap.congr_fun hg (QuotientAddGroup.mk a)

end Formalism.L2.SG.Pf.StdChar

namespace Formalism.L2.SG.Pf.StdChar

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def psiFin (z : Af F) : ℂ := ((AddCircle.toCircle (-((exists_psiF F).choose z)) : Circle) : ℂ)

theorem psiFin_add (z w : Af F) : psiFin F (z + w) = psiFin F z * psiFin F w := by
  unfold psiFin
  rw [map_add, neg_add, AddCircle.toCircle_add]
  first | rfl | simp

theorem psiFin_int (z : Af F) (hz : z ∈ Formalism.UG.intAd F) : psiFin F z = 1 := by
  have h0 := (exists_psiF F).choose_spec.1 z hz
  first
    | simp [psiFin, h0, AddCircle.toCircle_zero]
    | simp [psiFin, h0]

theorem psiFin_zero : psiFin F 0 = 1 := psiFin_int F 0 (Formalism.UG.intAd F).zero_mem

theorem psiFin_alg (a : F) :
    psiFin F (algebraMap F (Af F) a) = Complex.exp (-(2 * Real.pi * Complex.I * ((trR F a : ℝ) : ℂ))) := by
  have h := (exists_psiF F).choose_spec.2 a
  unfold psiFin
  rw [h, ← AddCircle.coe_neg, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem norm_psiFin (z : Af F) : ‖psiFin F z‖ = 1 := by
  unfold psiFin
  first
    | exact Circle.norm_coe _
    | exact Circle.abs_coe _
    | exact mem_sphere_zero_iff_norm.mp (AddCircle.toCircle _).2
    | simp [Circle.norm_coe]

theorem continuous_psiFin : Continuous (psiFin F) := by
  have hU : IsOpen ((Formalism.UG.intAd F : Set (Af F))) := by
    first
      | exact RestrictedProduct.isOpen_forall_mem (fun v => IsDedekindDomain.HeightOneSpectrum.isOpen_adicCompletionIntegers F v)
      | exact RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_integer _)
  have hf : Continuous ((exists_psiF F).choose) := by
    refine continuous_of_continuousAt_zero _ ?_
    rw [ContinuousAt, map_zero]
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [hU.mem_nhds (Formalism.UG.intAd F).zero_mem] with z hz
    exact (exists_psiF F).choose_spec.1 z hz
  have hc : Continuous (fun z : Af F => AddCircle.toCircle (-((exists_psiF F).choose z))) :=
    AddCircle.continuous_toCircle.comp hf.neg
  unfold psiFin
  first
    | exact continuous_subtype_val.comp hc
    | exact Circle.continuous_coe.comp hc
    | fun_prop

def psiStd : AddChar (AF F) ℂ where
  toFun x := psiA F x.1 * psiFin F x.2
  map_zero_eq_one' := by
    show psiA F 0 * psiFin F 0 = 1
    rw [psiA_zero, psiFin_zero, one_mul]
  map_add_eq_mul' x y := by
    show psiA F (x.1 + y.1) * psiFin F (x.2 + y.2) = psiA F x.1 * psiFin F x.2 * (psiA F y.1 * psiFin F y.2)
    rw [psiA_add, psiFin_add]
    ring

theorem psiStd_apply (x : AF F) : psiStd F x = psiA F x.1 * psiFin F x.2 := rfl

theorem ext_alg (w : InfinitePlace F) (a : F) :
    InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) a) w) = w.embedding a := by
  first
    | exact InfinitePlace.Completion.extensionEmbedding_coe w a
    | simp [InfinitePlace.Completion.extensionEmbedding_coe]
    | rfl

theorem psiStd_isChar : IsCharAF F (psiStd F) := by
  have hfun : (⇑(psiStd F) : AF F → ℂ) = fun x => psiA F x.1 * psiFin F x.2 := funext (psiStd_apply F)
  have hnA : ∀ y, ‖psiA F y‖ = 1 := fun y => by unfold psiA; exact norm_exp_real _
  have h3 : ∀ a : F, psiA F (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((trR F a : ℝ) : ℂ)) := by
    intro a
    simp only [psiA, ext_alg]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact ((continuous_psiA F).comp continuous_fst).mul ((continuous_psiFin F).comp continuous_snd)
  · intro x
    rw [psiStd_apply, norm_mul, hnA, norm_psiFin, one_mul]
  · intro a
    rw [psiStd_apply]
    have h1 : (algebraMap F (AF F) a).1 = algebraMap F (Ainf F) a := rfl
    have h2 : (algebraMap F (AF F) a).2 = algebraMap F (Af F) a := rfl
    rw [h1, h2, psiFin_alg, h3, ← Complex.exp_add]
    simp
  · set q : ℚ := 1 / (2 * (Fintype.card (InfinitePlace F) : ℚ)) with hqdef
    refine ⟨pairA F (algebraMap F (Ainf F) ((q : ℚ) : F)) 0, ?_⟩
    show psiA F (algebraMap F (Ainf F) ((q : ℚ) : F)) * psiFin F 0 ≠ 1
    rw [psiFin_zero, mul_one, h3]
    have hN : (Fintype.card (InfinitePlace F) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hq : trR F ((q : ℚ) : F) = 1 / 2 := by
      show (∑ w : InfinitePlace F, (w.embedding ((q : ℚ) : F)).re) = 1 / 2
      simp only [map_ratCast, Complex.ratCast_re, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hqdef]
      push_cast
      field_simp
    rw [hq]
    have he : (2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = Real.pi * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_pi_mul_I]
    norm_num

end Formalism.L2.SG.Pf.StdChar

namespace Formalism.L2.SG.Pf

theorem standard_character_exists : Formalism.L2.SG.Pf.MeasCore.StdCharExists := by
  intro F _ _ hF
  haveI := hF
  refine ⟨StdChar.psiStd F, StdChar.psiStd_isChar F, fun x => ?_⟩
  show StdChar.psiA F x * StdChar.psiFin F 0 = _
  rw [StdChar.psiFin_zero, mul_one]
  rfl

end Formalism.L2.SG.Pf
