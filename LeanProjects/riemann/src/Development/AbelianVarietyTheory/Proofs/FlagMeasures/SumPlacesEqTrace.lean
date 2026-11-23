import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanEqTopOfSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants GlobalTheory.SgAlg GlobalTheory.SgGlob
open Formalism.MainNotions.S (IsHaarOn)
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.Inhab

section Char

variable {F : Type} [Field F] [NumberField F]

theorem trace_int_iff (a : F) : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔
    ∀ d ∈ differentIdeal ℤ (𝓞 F), ∃ r : 𝓞 F, (r : F) = a * d := by
  have h1 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
  have hD := FractionalIdeal.dual_ne_zero ℤ ℚ h1
  have hd : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔
      a ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.mem_dual h1]
    constructor
    · intro h x hx
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
      obtain ⟨k, hk⟩ := h b
      exact ⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩
    · intro h r
      obtain ⟨k, hk⟩ := h (algebraMap _ F r) ((FractionalIdeal.mem_one_iff _).mpr ⟨r, rfl⟩)
      exact ⟨k, by rw [Algebra.traceForm_apply] at hk; simpa using hk.symm⟩
  rw [hd, ← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)),
    FractionalIdeal.mem_inv_iff (inv_ne_zero hD), ← coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]
  constructor
  · intro h d hd
    exact (FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hd))
  · intro h y hy
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    exact (FractionalIdeal.mem_one_iff _).mpr (h d hd)

theorem integral_iff (x : F) : (∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) x v ∈ v.adicCompletionIntegers F) ↔
    ∃ r : 𝓞 F, (r : F) = x := by
  constructor
  · intro h
    have hx := (GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral F _).2 h
    rwa [GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal F),
      FractionalIdeal.mem_one_iff] at hx
  · rintro ⟨r, rfl⟩ v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

theorem fin_conductor (χ : Af F → ℂ) (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y)
    (hrat : ∀ a : F, χ (algebraMap F (Af F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (-a) : ℚ) : ℂ))) (z : Af F) :
    (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔
      ∀ d ∈ differentIdeal ℤ (𝓞 F), ∀ v : HeightOneSpectrum (𝓞 F), (z * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F := by
  have hone : ∀ a : F, χ (algebraMap F (Af F) a) = 1 ↔ ∃ k : ℤ, Algebra.trace ℚ F a = k := by
    intro a
    rw [hrat, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero, map_neg] at hn
      have : -Algebra.trace ℚ F a = (n : ℚ) := by exact_mod_cast hn
      push_cast
      linarith
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      rw [map_neg, hk]
      push_cast
      ring
  have hO : ∀ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) (r : F) v ∈ v.adicCompletionIntegers F :=
    fun r => (integral_iff _).2 ⟨r, rfl⟩
  have hint : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ t = 1 := fun t ht =>
    GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ y = 1}) (isClosed_eq hc continuous_const)
      (fun r => (hone _).2 (by simpa using (trace_int_iff (1 : F)).2 (fun d _ => ⟨d, (one_mul _).symm⟩) r)) t ht
  obtain ⟨a, s, hs, hz⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos z
  rw [one_smul] at hz
  have hmul : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = χ (algebraMap F (Af F) a * t) := by
    intro t ht
    rw [hz, add_mul, hadd, hint (s * t) (fun v => mul_mem (hs v) (ht v)), mul_one]
  have h1 : (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔
      ∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k := by
    constructor
    · intro h r
      rw [← hone, map_mul, ← hmul _ (hO r)]
      exact h _ (hO r)
    · intro h t ht
      rw [hmul t ht]
      exact GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ (algebraMap F (Af F) a * y) = 1})
        (isClosed_eq (hc.comp (continuous_const.mul continuous_id)) continuous_const)
        (fun r => by
          show χ _ = 1
          rw [← map_mul, hone]
          exact h r) t ht
  rw [h1, trace_int_iff]
  refine forall₂_congr fun d _ => ?_
  rw [← integral_iff, hz, add_mul, map_mul]
  refine forall_congr' fun v => ?_
  have h2 : (s * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F := mul_mem (hs v) (hO d v)
  exact ⟨fun h => add_mem h h2, fun h => (add_mem_cancel_right h2).1 h⟩

theorem single_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : singleV F v y v = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem single_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    singleV F v y w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem single_mul (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (t : Af F) :
    singleV F v y * t = singleV F v (y * t v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change singleV F v y w * t w = singleV F v (y * t v) w
  by_cases hw : w = v
  · subst hw; rw [single_same, single_same]
  · rw [single_ne v _ hw, single_ne v _ hw, zero_mul]

theorem single_int (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    (∀ w, singleV F v y w ∈ w.adicCompletionIntegers F) ↔ y ∈ v.adicCompletionIntegers F := by
  refine ⟨fun h => single_same v y ▸ h v, fun h w => ?_⟩
  by_cases hw : w = v
  · subst hw; rwa [single_same]
  · rw [single_ne v _ hw]; exact zero_mem _

theorem stdAt_of_psiInf {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ)
    (hinf : ∀ a : F, psiInf F ψ (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F a : ℚ) : ℂ))) (v : HeightOneSpectrum (𝓞 F)) :
    StdAt v (psiV F ψ v) := by
  intro x
  have key := fin_conductor (fun y => ψ (pairA F 0 y))
    (h.1.comp (Continuous.prodMk continuous_const continuous_id))
    (fun a b => by
      rw [← AddChar.map_add_eq_mul]
      exact congrArg ψ (Prod.ext (add_zero _).symm rfl))
    (fun a => by rw [GlobalTheory.StdRat.char_fin_rat ψ h, hinf]) (singleV F v x)
  simp only [single_mul, single_int] at key
  refine Iff.trans ⟨fun h' t ht => h' _ (ht v), fun h' y hy => ?_⟩ key
  have := h' (singleV F v y) ((single_int v y).2 hy)
  rwa [single_same] at this

theorem sum_places_eq_trace [IsTotallyReal F] (x : F) :
    (((∑ w : InfinitePlace F, (w.embedding x).re : ℝ)) : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h, ← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun τ => τ x) _ fun τ => rfl]
  have hr : ∀ τ : F →+* ℂ, (InfinitePlace.mk τ).embedding = τ := fun τ =>
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))
  push_cast
  refine Fintype.sum_bijective (fun w : InfinitePlace F => w.embedding) ⟨fun a b hab => ?_, fun τ => ⟨_, hr τ⟩⟩ _ _
    fun w => ?_
  · rw [← InfinitePlace.mk_embedding a, ← InfinitePlace.mk_embedding b]
    exact congrArg InfinitePlace.mk hab
  · have := InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)
    exact Complex.conj_eq_iff_re.1 (RingHom.congr_fun this x)

theorem exists_isStdChar (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : ∃ ψ, IsStdChar F ψ := by
  let L : Ainf F →+ ℂ := AddMonoidHom.mk'
    (fun x => ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))
    fun a b => by
      rw [← Complex.ofReal_add, ← Finset.sum_add_distrib]
      refine congrArg _ (Finset.sum_congr rfl fun w _ => ?_)
      rw [← Complex.add_re, ← map_add]
      rfl
  have hL : Continuous L := Complex.continuous_ofReal.comp (continuous_finset_sum _ fun w _ =>
    Complex.continuous_re.comp
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)))
  have hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := fun x => by
    rw [← sum_places_eq_trace]
    refine congrArg Complex.ofReal (Finset.sum_congr rfl fun w _ => congrArg Complex.re ?_)
    exact InfinitePlace.Completion.extensionEmbedding_coe w _
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.StdAdelicChar.exists_char_of_trace F L hL hT
  have h3 : ∀ x, psiInf F ψ⁻¹ x = Complex.exp (2 * Real.pi * Complex.I * L x) := fun x => by
    have e : psiInf F ψ⁻¹ x = psiInf F ψ (-x) := by
      rw [psiInf, psiInf, AddChar.inv_apply]
      exact congrArg ψ (Prod.ext rfl neg_zero)
    rw [e, h2, map_neg]
    congr 1
    push_cast
    ring
  have h4 := GlobalTheory.StdAdelicChar.isCharAF_inv h1
  exact ⟨ψ⁻¹, h4, h3, stdAt_of_psiInf h4 fun a => by rw [h3, hT]⟩

end Char

section Haar

theorem isHaarMeasure_comap {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace X] {φ : G → X}
    (hφ : MeasurableEmbedding φ) (μ : Measure X) [SigmaFinite μ] (h0 : μ ≠ 0) (hc : μ (Set.range φ)ᶜ = 0)
    (hT : ∀ g, ∃ T : X → X, Measurable T ∧ Function.Injective T ∧ μ.map T = μ ∧ ∀ u, T (φ u) = φ (g * u)) :
    (μ.comap φ).IsHaarMeasure ∧ (μ.comap φ).map φ = μ := by
  have h2 : (μ.comap φ).map φ = μ := by
    rw [hφ.map_comap]
    exact Measure.restrict_eq_self_of_ae_mem hc
  refine ⟨?_, h2⟩
  haveI : SigmaFinite (μ.comap φ) := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : (μ.comap φ).IsMulLeftInvariant := ⟨fun g => by
    obtain ⟨T, hm, hi, hμ, hg⟩ := hT g
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, hφ.comap_apply, hφ.comap_apply]
    conv_rhs => rw [← hμ, Measure.map_apply hm (hφ.measurableSet_image.2 hs)]
    congr 1
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨g * w, hw, (hg w).symm⟩
    · rintro ⟨v, hv, hx⟩
      exact ⟨g⁻¹ * v, by simpa using hv, hi (by rw [hg, mul_inv_cancel_left, hx])⟩⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have e := Measure.haarMeasure_unique (μ.comap φ) K
  set ν := μ.comap φ
  have hν : ν ≠ 0 := fun h => h0 (by rw [← h2, h, Measure.map_zero])
  rw [e]
  refine Measure.IsHaarMeasure.smul _ (fun hc => hν (by rw [e, hc, zero_smul])) fun hc => hν ?_
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets ν]
  refine measure_iUnion_null fun n => ?_
  have h1 := measure_spanningSets_lt_top ν n
  have h2 : ν (spanningSets ν n) = ⊤ * Measure.haarMeasure K (spanningSets ν n) := by
    have := congrArg (fun ρ : Measure G => ρ (spanningSets ν n)) e
    simpa [hc] using this
  by_cases h3 : Measure.haarMeasure K (spanningSets ν n) = 0
  · rw [h2, h3, mul_zero]
  · rw [h2, ENNReal.top_mul h3] at h1
    exact absurd h1 (lt_irrefl _)

open Formalism.BasicNotions in

theorem exists_model (k r : ℕ) : ∃ (P Q : ℕ) (C : Matrix (Fin P ⊕ Fin Q) (Fin (2 * r + k + 1)) ℂ)
    (D : Matrix (Fin (2 * r + k + 1)) (Fin P ⊕ Fin Q) ℂ) (φ : UpqT P Q → Mt k r),
    Cᴴ * Formalism.UG.Jpq P Q * C = Hpk k r ∧ C * D = 1 ∧ D * C = 1 ∧ (∀ g, Matrix.of (φ g) = D * UpqT.mat g * C) ∧
    MeasurableEmbedding φ ∧ (∀ x, x ∈ Set.range φ ↔ Matrix.of x ∈ UH (Hpk k r)) ∧
    ∀ g, Measurable (lmulM (Matrix.of (φ g))) ∧ Function.Injective (lmulM (Matrix.of (φ g))) ∧
      ∀ u, lmulM (Matrix.of (φ g)) (φ u) = φ (g * u) := by
  obtain ⟨hH, hH2, -⟩ := hpkFacts k r
  obtain ⟨P, Q, hs⟩ := Formalism.UG.Final.SigExists _ (Hpk k r) hH (Matrix.isUnit_det_of_left_inverse hH2)
  obtain ⟨-, ⟨C, hC⟩, hinv⟩ := GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ hs
  obtain ⟨D, hCD, hDC⟩ := hinv C hC
  have hD : Dᴴ * Hpk k r * D = Formalism.UG.Jpq P Q := by
    rw [← hC]
    calc Dᴴ * (Cᴴ * Formalism.UG.Jpq P Q * C) * D = (C * D)ᴴ * Formalism.UG.Jpq P Q * (C * D) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hCD]; simp
  obtain ⟨-, -, -, -, hB, hcl⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  let h : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ ≃ₜ Mt k r :=
    { toFun := fun x => D * x * C
      invFun := fun y => C * Matrix.of y * D
      left_inv := fun x => GlobalTheory.Mem.InfGroup.conj_conj hCD x
      right_inv := fun y => GlobalTheory.Mem.InfGroup.conj_conj hDC (Matrix.of y)
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  have hm : ∀ g u : UpqT P Q, D * UpqT.mat g * C * (D * UpqT.mat u * C) = D * UpqT.mat (g * u) * C :=
    fun g u => GlobalTheory.Mem.InfGroup.conj_mul hCD _ _
  refine ⟨P, Q, C, D, h ∘ UpqT.mat, hC, hCD, hDC, fun _ => rfl,
    (h.isClosedEmbedding.comp hcl).measurableEmbedding, fun x => ⟨?_, fun hx => ?_⟩, fun g => ⟨?_, ?_, hm g⟩⟩
  · rintro ⟨g, rfl⟩
    exact GlobalTheory.Mem.InfGroup.conj_unitary hCD hC (GlobalTheory.UpqTopology.mat_unitary g)
  · have : h.symm x ∈ Set.range (UpqT.mat (P := P) (Q := Q)) := by
      rw [GlobalTheory.UpqTopology.range_mat]
      exact GlobalTheory.Mem.InfGroup.conj_unitary hDC hD hx
    obtain ⟨g, hg⟩ := this
    exact ⟨g, by rw [Function.comp_apply, hg, h.apply_symm_apply]⟩
  · have : Continuous fun x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => D * UpqT.mat g * C * x :=
      continuous_const.matrix_mul continuous_id
    exact Continuous.measurable (f := lmulM (k := k) (r := r) (D * UpqT.mat g * C)) this
  · refine Function.LeftInverse.injective (g := lmulM (D * UpqT.mat g⁻¹ * C)) fun x => ?_
    show D * UpqT.mat g⁻¹ * C * (D * UpqT.mat g * C * Matrix.of x) = Matrix.of x
    rw [← Matrix.mul_assoc _ _ (Matrix.of x), hm, inv_mul_cancel, GlobalTheory.Mem.VolExists.mat_one, Matrix.mul_one, hDC,
      Matrix.one_mul]

theorem exists_isHaarOn (k r : ℕ) : ∃ μ : Measure (Mt k r), IsHaarOn (UH (Hpk k r)) μ := by
  obtain ⟨P, Q, C, D, φ, -, -, -, -, hφ, hr, hl⟩ := exists_model k r
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  let ν : Measure (Formalism.BasicNotions.UpqT P Q) := Measure.haar
  refine ⟨ν.map φ, hφ.sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · rw [Ne, Measure.map_eq_zero_iff hφ.measurable.aemeasurable]
    exact NeZero.ne ν
  · rw [hφ.map_apply]
    convert measure_empty (μ := ν)
    ext g
    simpa using (hr _).1 ⟨g, rfl⟩
  · obtain ⟨g, hg⟩ := (hr (Matrix.of.symm s)).2 hs
    obtain rfl : Matrix.of (φ g) = s := congrArg Matrix.of hg
    rw [Measure.map_map (hl g).1 hφ.measurable]
    conv_rhs => rw [← map_mul_left_eq_self ν g, Measure.map_map hφ.measurable (measurable_const_mul g)]
    exact congrArg (fun f => ν.map f) (funext (hl g).2.2)

end Haar

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice in

theorem exists_isVolM (σ : E →ₐ[F] E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E))
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μw : InfinitePlace E → Measure (Mt k r)) (hcm : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hΛ : GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ) (hA : IsModelAt J A)
    (hμw : ∀ w, IsHaarOn (UH (Hpk k r)) (μw w)) : ∃ μ, IsVolM σ J Λ A μw μ := by
  obtain ⟨P, Q, C, D, φ, hC, hCD, hDC, hφe, hφ, hr, hl⟩ := exists_model k r
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E σ hcm
  choose θ hθ1 hθ2 using fun w : InfinitePlace E => hθ w.embedding
  have hfam : GlobalTheory.Mem.Vol.IsCMFam fun w : InfinitePlace E => w.embedding := by
    unfold GlobalTheory.Mem.Vol.IsCMFam
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  have hAu : ∀ w, IsUnit (A w).det := fun w => by
    refine isUnit_iff_ne_zero.2 fun h => hJ.2 ?_
    have h1 := congrArg Matrix.det (hA w)
    rw [Matrix.det_mul, h, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
    exact w.embedding.injective (h1.symm.trans (map_zero _).symm)
  obtain ⟨e', he', hc, hc', hs⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ _ _ θ hcm hfam hθ1
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.exists_equiv he' hc hc' (sigR (Ainf F) σ)
    (fun x i => by rw [← he', ← he', hs]) (JR (Ainf F) J) (fun _ => P) (fun _ => Q) (fun w => C * A w)
    (fun w => (A w)⁻¹ * D)
    (fun w => by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hAu w), hCD])
    (fun w => by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc D, hDC, Matrix.one_mul, Matrix.nonsing_inv_mul _ (hAu w)])
    (fun w => by
      have : (C * A w)ᴴ * Formalism.UG.Jpq P Q * (C * A w) = (A w)ᴴ * (Cᴴ * Formalism.UG.Jpq P Q * C) * A w := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [this, hC, hA w]
      ext a b
      exact ((hθ1 w).1 (J a b)).symm)
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E σ _ J
  obtain ⟨K, hK, hKo, hKc⟩ := GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab F E σ _ J Λ hΛ.1
    (GlobalTheory.SgSpan.span_eq_top_of_selfDual E _ _ J Λ
      (fun x => x.isIntegral_coe.map (σ : E →+* E).toIntAlgHom) hΛ)
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ _ J
  haveI : IsTopologicalGroup (HA (AF F) σ J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI : ∀ w, ((μw w).comap φ).IsHaarMeasure := fun w => by
    obtain ⟨h1, h2, h3, h4⟩ := hμw w
    refine (isHaarMeasure_comap hφ (μw w) h2 ?_ fun g =>
      ⟨_, (hl g).1, (hl g).2.1, h4 _ ((hr _).1 ⟨g, rfl⟩), (hl g).2.2⟩).1
    rw [← h3]
    exact congrArg _ (Set.ext fun x => not_congr (hr x))
  let e1' : HA (Ainf F) σ J ≃ₜ* (InfinitePlace E → UpqT P Q) := e1
  let e : HA (AF F) σ J ≃ₜ* (InfinitePlace E → UpqT P Q) × HA (Af F) σ J :=
    e0.trans
      { e1'.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1'.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1'.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1' (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := GlobalTheory.Mem.VolExists.exists_haar_prod (fun w => (μw w).comap φ) e K hKo hKc
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' B hB => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  have key := hμB (fun w => φ ⁻¹' B w) fun w => hφ.measurable (hB w)
  have hcj : ∀ w, (μw w).comap φ (φ ⁻¹' B w) = μw w (B w) := fun w => by
    rw [hφ.comap_apply, Set.image_preimage_eq_inter_range]
    refine measure_inter_conull ?_
    rw [← (hμw w).2.2.1]
    exact congrArg _ (Set.ext fun x => not_congr (hr x))
  rw [Finset.prod_congr rfl fun w _ => hcj w] at key
  rw [← key]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, hee, Set.mem_preimage]
  rw [hK, (he0 h).1]
  refine and_congr_right fun _ => forall_congr' fun w => ?_
  have h1 : UpqT.mat (e1' (e0 h).1 w) * (C * A w) = C * A w * infMat σ J (θ' w) h := by
    refine (he1 (e0 h).1 w).trans (congrArg (fun X => C * A w * Matrix.map X (θ' w)) (he0 h).2)
  have h2 : Matrix.of (φ (e1' (e0 h).1 w)) * A w = A w * infMat σ J (θ' w) h := by
    rw [hφe, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_assoc, ← Matrix.mul_assoc D, hDC, Matrix.one_mul]
  constructor
  · rintro ⟨b, hb, hbe⟩
    have h5 := congrArg (· * (A w)⁻¹) (hbe.trans h2.symm)
    simp only [Matrix.mul_nonsing_inv_cancel_right _ _ (hAu w)] at h5
    exact Matrix.of.injective h5 ▸ hb
  · intro hb
    exact ⟨_, hb, h2⟩

theorem exists_globData (σ : E →ₐ[F] E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E))
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μw : InfinitePlace E → Measure (Mt k r)) (hcm : IsCMExt F E σ)
    (hu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E)) (hJ : IsHermND σ J)
    (hΛ : GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ) (hA : IsModelAt J A)
    (hμw : ∀ w, IsHaarOn (UH (Hpk k r)) (μw w)) : ∃ V₀, V₀ ≠ 0 ∧ V₀ ≠ ⊤ ∧ GlobData σ J Λ A μw V₀ := by
  obtain ⟨μ, hμ⟩ := exists_isVolM σ J Λ A μw hcm hJ hΛ hA hμw
  obtain ⟨⟨D, hD⟩, h⟩ := GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary F E σ _ J μ hμ.1
  exact ⟨μ D, (h D D hD hD).2, (GlobalTheory.Mem.VolFin.finVol F E σ hcm _ J hJ μ hμ.1 D hD).ne,
    hcm, hu, hJ, hΛ, hA, hμw, μ, D, hμ, hD, rfl⟩

end General

section Concrete

def hInt (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℤ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0

theorem hInt_map (k r : ℕ) : (hInt k r).map (Int.castRingHom ℂ) = Hpk k r := by
  ext i j
  simp only [hInt, Hpk, Matrix.map_apply]
  split_ifs <;> simp

theorem hInt_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) : hInt k r j i = hInt k r i j := by
  have h := congrFun (congrFun (hpkFacts k r).1 i) j
  rw [← hInt_map] at h
  simpa using h

theorem hInt_sq (k r : ℕ) : hInt k r * hInt k r = 1 := by
  have h := (hpkFacts k r).2.1
  rw [← hInt_map, ← Matrix.map_mul, ← Matrix.map_one (Int.castRingHom ℂ) (map_zero _) (map_one _)] at h
  exact Matrix.map_injective (RingHom.injective_int _) h

variable (E : Type) [Field E] [NumberField E]

def hStd (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E := (hInt k r).map (Int.castRingHom E)

def intLat (n : ℕ) : Submodule (𝓞 E) (Fin n → E) := Submodule.pi Set.univ fun _ => 1

theorem hStd_sq (k r : ℕ) : hStd E k r * hStd E k r = 1 := by
  rw [hStd, ← Matrix.map_mul, hInt_sq, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_intLat {n : ℕ} (v : Fin n → E) : v ∈ intLat E n ↔ ∀ i, v i ∈ (algebraMap (𝓞 E) E).range := by
  simp [intLat, Submodule.mem_pi, Submodule.mem_one]

theorem hStd_mulVec {k r : ℕ} {v : Fin (2 * r + k + 1) → E} (h : v ∈ intLat E _) :
    hStd E k r *ᵥ v ∈ intLat E _ := by
  rw [mem_intLat] at h ⊢
  intro i
  show ∑ j, ((hInt k r i j : ℤ) : E) * v j ∈ _
  exact sum_mem fun j _ => mul_mem (intCast_mem _ _) (h j)

theorem selfDual_intLat (σ : E →+* E) (k r : ℕ) : GlobalTheory.SgGlob.SelfDual σ (hStd E k r) (intLat E _) := by
  refine ⟨Submodule.fg_pi fun _ => ?_, fun v => ⟨fun hv w hw => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _
  · show ∑ i, σ (w i) * (hStd E k r *ᵥ v) i ∈ _
    refine sum_mem fun i _ => mul_mem ?_ ((mem_intLat E _).1 (hStd_mulVec E hv) i)
    obtain ⟨x, hx⟩ := (mem_intLat E _).1 hw i
    exact ⟨⟨σ (w i), hx ▸ x.isIntegral_coe.map σ.toIntAlgHom⟩, rfl⟩
  · have h1 : hStd E k r *ᵥ v ∈ intLat E _ := by
      rw [mem_intLat]
      intro i
      have h2 : (Pi.single i 1 : Fin (2 * r + k + 1) → E) ∈ intLat E _ := by
        rw [mem_intLat]
        intro j
        rw [Pi.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      have h3 : (fun j => σ ((Pi.single i 1 : Fin (2 * r + k + 1) → E) j)) = Pi.single i 1 := by
        funext j
        simp only [Pi.single_apply]
        split_ifs <;> simp
      have h4 := h _ h2
      rwa [form, h3, single_one_dotProduct] at h4
    have h5 := hStd_mulVec E (k := k) (r := r) h1
    rwa [Matrix.mulVec_mulVec, hStd_sq, Matrix.one_mulVec] at h5

theorem isModelAt_one (k r : ℕ) : IsModelAt (hStd E k r) fun _ => 1 := fun w => by
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, ← hInt_map]
  ext i j
  simp [hStd]

theorem isHermND_hStd {F : Type} [Field F] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) : IsHermND σ (hStd E k r) :=
  ⟨fun i j => by simp [hStd, hInt_symm k r i j], (Matrix.isUnit_det_of_left_inverse (hStd_sq E k r)).ne_zero⟩

theorem exists_globData_std {F : Type} [Field F] [NumberField F] [Algebra F E] (σ : E →ₐ[F] E)
    (hcm : IsCMExt F E σ) (hu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E)) (k r : ℕ) :
    ∃ (μ : Measure (Mt k r)) (V₀ : ℝ≥0∞), V₀ ≠ 0 ∧ V₀ ≠ ⊤ ∧
      GlobData σ (hStd E k r) (intLat E _) (fun _ => 1) (fun _ => μ) V₀ := by
  obtain ⟨μ, hμ⟩ := exists_isHaarOn k r
  exact ⟨μ, exists_globData σ _ _ _ _ hcm hu (isHermND_hStd E σ k r) (selfDual_intLat E _ k r)
    (isModelAt_one E k r) fun _ => hμ⟩

end Concrete

theorem inhabitants :
    (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) →
      ∀ (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
        (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E))
        (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
        (μw : InfinitePlace E → Measure (Mt k r)),
        IsHermND σ J → GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ → IsModelAt J A →
        (∀ w, IsHaarOn (UH (Hpk k r)) (μw w)) → ∃ V₀, V₀ ≠ 0 ∧ V₀ ≠ ⊤ ∧ GlobData σ J Λ A μw V₀) ∧
    (∃ (_ : IsCMField (CyclotomicField 21 ℚ)), ∀ k r : ℕ, ∃ (μ : Measure (Mt k r)) (V₀ : ℝ≥0∞), V₀ ≠ 0 ∧ V₀ ≠ ⊤ ∧
      GlobData (F := maximalRealSubfield (CyclotomicField 21 ℚ))
        (IsCMField.complexConj (CyclotomicField 21 ℚ) : CyclotomicField 21 ℚ →ₐ[_] CyclotomicField 21 ℚ)
        (hStd (CyclotomicField 21 ℚ) k r) (intLat _ _) (fun _ => 1) (fun _ => μ) V₀) ∧
    ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∃ ψ, IsStdChar F ψ :=
  ⟨fun _ _ _ _ _ _ _ σ hcm hu _ _ J Λ A μw => exists_globData σ J Λ A μw hcm hu,
    ⟨inferInstance, exists_globData_std _ _
      ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
        fun τ x => IsCMField.complexEmbedding_complexConj _ τ x⟩
      GlobalTheory.HostModel.unramified_E21_over_maximalRealSubfield.formallyUnramified⟩,
    fun F _ _ _ => exists_isStdChar F⟩

end GlobalTheory.SnMass.Inhab
