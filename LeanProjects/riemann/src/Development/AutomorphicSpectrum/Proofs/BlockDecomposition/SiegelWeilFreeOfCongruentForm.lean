import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.SW.SWIsom

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [MeasurableSpace X]
  [TopologicalSpace X]

theorem fibre_transport {μ : Measure V} {ν : Measure X} {f f' : V → Y} {ι : X → Y} {U : Set V}
    {B : Set X} {fib : X → Measure V} (e : V ≃ₜ V) (hf : ∀ x, f' x = f (e x)) (hU : e ⁻¹' U = U)
    {a : ℝ≥0} (hμ : μ.map e = a • μ) (hfib : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f' ι U ν B (fun b => a • (fib b).map e.symm) := by
  set em := e.toMeasurableEquiv with hem
  set es := e.symm.toMeasurableEquiv with hes
  have hUs : ∀ x, e.symm x ∈ U ↔ x ∈ U := fun x => by
    have := Set.ext_iff.1 hU (e.symm x)
    simpa using this.symm
  have hmap : ∀ b, (fib b).map e.symm = (fib b).map es := fun _ => rfl
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs hts => ?_⟩
  · rw [Measure.smul_apply, hmap, MeasurableEquiv.map_apply]
    have : es ⁻¹' (f' ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι b} ∩ U)ᶜ := by
      ext x
      have h1 : f' (e.symm x) = f x := by rw [hf, e.apply_symm_apply]
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
      change ¬ (f' (e.symm x) = ι b ∧ e.symm x ∈ U) ↔ ¬ (f x = ι b ∧ x ∈ U)
      rw [h1, hUs]
    rw [this, hfib.1 b, smul_zero]
  · have hU' : em ⁻¹' U = U := hU
    have key : ∫⁻ x in U, φ (es x) ∂(μ.map em) = ∫⁻ x in U, φ x ∂μ := by
      calc ∫⁻ x in U, φ (es x) ∂(μ.map em) = ∫⁻ x, φ (es x) ∂((μ.restrict (em ⁻¹' U)).map em) := by
            rw [MeasurableEquiv.restrict_map]
        _ = ∫⁻ x, φ (es (em x)) ∂(μ.restrict (em ⁻¹' U)) := lintegral_map_equiv _ _
        _ = ∫⁻ x in U, φ x ∂μ := by
            rw [hU']
            refine lintegral_congr fun x => ?_
            simp [hem, hes]
    have hμ' : μ.map em = a • μ := hμ
    have e1 : ∀ b, ∫⁻ x, φ x ∂(a • (fib b).map e.symm) = (a : ℝ≥0∞) * ∫⁻ x, φ (es x) ∂(fib b) := by
      intro b
      rw [hmap, lintegral_smul_measure, lintegral_map_equiv, ENNReal.smul_def, smul_eq_mul]
    simp only [e1]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
      ← hfib.2.1 (fun x => φ (es x)) (hφ.comp es.measurable), ← key, hμ', Measure.restrict_smul,
      lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  · have hts' : tsupport (φ ∘ e.symm) ⊆ U := by
      rw [tsupport, Function.support_comp_eq_preimage, ← e.symm.preimage_closure]
      intro x hx
      exact (hUs x).1 (hts hx)
    obtain ⟨h1, h2⟩ := hfib.2.2 (φ ∘ e.symm) (hc.comp e.symm.continuous) (hcs.comp_homeomorph e.symm) hts'
    refine ⟨fun b hb => ?_, ?_⟩
    · exact ((integrable_map_equiv es φ).2 (h1 b hb)).smul_measure ENNReal.coe_ne_top
    · have e2 : (fun b => ∫ x, φ x ∂(a • (fib b).map e.symm)) =
          fun b => (a : ℝ) • ∫ x, (φ ∘ e.symm) x ∂(fib b) := by
        funext b
        rw [hmap, integral_smul_nnreal_measure, integral_map_equiv]
        rfl
      rw [e2]
      exact h2.const_smul (a : ℝ)

omit [BorelSpace V] in

theorem fibre_scale {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
    {B : Set X} {fib : X → Measure V} (a k r : ℝ≥0) (hr : r * k = a)
    (hfib : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (a • μ) f ι U (k • ν) B (fun b => r • fib b) := by
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs hts => ?_⟩
  · rw [Measure.smul_apply, hfib.1 b, smul_zero]
  · have e1 : ∀ b, ∫⁻ x, φ x ∂(r • fib b) = (r : ℝ≥0∞) * ∫⁻ x, φ x ∂(fib b) := by
      intro b
      rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    simp only [e1]
    rw [Measure.restrict_smul, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← hfib.2.1 φ hφ, ENNReal.smul_def,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← hr]
    push_cast
    ring_nf
  · obtain ⟨h1, h2⟩ := hfib.2.2 φ hc hcs hts
    refine ⟨fun b hb => (h1 b hb).smul_measure ENNReal.coe_ne_top, ?_⟩
    have e2 : (fun b => ∫ x, φ x ∂(r • fib b)) = fun b => (r : ℝ) • ∫ x, φ x ∂(fib b) := by
      funext b
      rw [integral_smul_nnreal_measure]
      rfl
    rw [e2]
    exact h2.const_smul (r : ℝ)

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in

theorem gramR_conj (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) X =
      gramR R σ J (actTup R (bc (inclR R) g) X) := by
  funext a b
  simp only [gramR, hR, actTup]
  rw [GlobalTheory.CompanionTheory.SW.HIsom.JR_conj R σ J g, hform_conj]

omit [Field F] [NumberField F] [NumberField E] [Algebra F E] in

theorem li_mulVec {A : Type} [CommRing A] {M n : ℕ} (G : GL (Fin M) A) {X : Fin n → Fin M → A}
    (hX : LinearIndependent A X) :
    LinearIndependent A fun a => (G : Matrix (Fin M) (Fin M) A).mulVec (X a) := by
  have hinj : Function.Injective (Matrix.mulVecLin (G : Matrix (Fin M) (Fin M) A)) := by
    intro x y hxy
    have h := congrArg (((G⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A).mulVec) hxy
    simpa [Matrix.mulVec_mulVec] using h
  exact hX.map' _ (LinearMap.ker_eq_bot.2 hinj)

omit [Field F] [NumberField F] [NumberField E] [Algebra F E] in
theorem li_mulVec_iff {A : Type} [CommRing A] {M n : ℕ} (G : GL (Fin M) A) (X : Fin n → Fin M → A) :
    LinearIndependent A (fun a => (G : Matrix (Fin M) (Fin M) A).mulVec (X a)) ↔ LinearIndependent A X := by
  refine ⟨fun h => ?_, li_mulVec G⟩
  have := li_mulVec G⁻¹ h
  simpa [Matrix.mulVec_mulVec] using this

def actHomeo (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R]
    [T2Space R] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) where
  toFun := actTup R g
  invFun := actTup R g⁻¹
  left_inv X := by rw [← actTup_mul, inv_mul_cancel, actTup_one]
  right_inv X := by rw [← actTup_mul, mul_inv_cancel, actTup_one]
  continuous_toFun := continuous_actTup σ hCM R g
  continuous_invFun := continuous_actTup σ hCM R g⁻¹

theorem local_transport (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : GL (Fin M) E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hR : IsLocR R) (n : ℕ)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (hm : IsGramFibFree R σ J n μ ν m)
    (a : ℝ≥0) (ha : μ.map (actTup R (bc (inclR R) g)) = a • μ) :
    ∃ m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E),
      IsGramFibFree R σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E))
        n μ ν m' ∧
      (∀ S, (m' S).map (actTup R (bc (inclR R) g)) = a • m S) ∧
      ∀ S (A : Set (Fin n → Fin M → R ⊗[F] E)),
        m' S (actTup R (bc (inclR R) g) ⁻¹' A) = a * m S A := by
  obtain ⟨r1, r2, r3, r4, -⟩ := hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R).2.2.2.2.2.2.2.1 n M
  set e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    actHomeo σ hCM R (bc (inclR R) g) with he
  have hee : (e : (Fin n → Fin M → R ⊗[F] E) → _) = actTup R (bc (inclR R) g) := rfl
  refine ⟨fun S => a • (m S).map e.symm, ?_, fun S => ?_, fun S A => ?_⟩
  · refine fibre_transport e (fun X => gramR_conj R σ J g X) ?_ ha hm
    ext X
    exact li_mulVec_iff _ X
  · rw [Measure.map_smul, ← hee, Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    simp
  · rw [Measure.smul_apply]
    have h1 : ((m S).map e.symm) (actTup R (bc (inclR R) g) ⁻¹' A) = m S A := by
      change ((m S).map e.symm.toMeasurableEquiv) _ = _
      rw [MeasurableEquiv.map_apply]
      congr 1
      ext X
      change actTup R (bc (inclR R) g) (e.symm X) ∈ A ↔ _
      rw [← hee, e.apply_symm_apply]
    rw [h1]
    rfl

theorem local_rescale (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) {d : ℕ} (b b' : Module.Basis (Fin d) F E) (lam : Measure R)
    (hlam : lam.IsAddHaarMeasure) (n : ℕ)
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hm : IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m) :
    ∃ r : ℝ≥0, r ≠ 0 ∧
      IsGramFibFree R σ J n (coordW R b' lam n M) (coordHerm R σ b' lam n) (fun S => r • m S) := by
  have h1 := haar_of_loc σ hCM R hR b lam hlam n M
  have h2 := haar_of_loc σ hCM R hR b' lam hlam n M
  obtain ⟨r1, r2, r3, r4, -⟩ := hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, t9, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := t8 n M
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R ⊗[F] E))
  haveI : LocallyCompactSpace (HermR R σ n) :=
    (t9 n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (HermR R σ n) :=
    (t9 n).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := h1.1
  haveI := h1.2
  haveI := h2.1
  haveI := h2.2
  set a := Measure.addHaarScalarFactor (coordW R b' lam n M) (coordW R b lam n M) with ha
  set k := Measure.addHaarScalarFactor (coordHerm R σ b' lam n) (coordHerm R σ b lam n) with hk
  have ea : coordW R b' lam n M = a • coordW R b lam n M := Measure.isAddLeftInvariant_eq_smul _ _
  have ek : coordHerm R σ b' lam n = k • coordHerm R σ b lam n := Measure.isAddLeftInvariant_eq_smul _ _
  have a0 : a ≠ 0 := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have k0 : k ≠ 0 := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  refine ⟨a / k, div_ne_zero a0 k0, ?_⟩
  rw [ea, ek]
  exact fibre_scale a k (a / k) (div_mul_cancel₀ a k0) hm

end Loc

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

omit [NumberField F] in

theorem repr_scaled (R : Type) [CommRing R] [Algebra F R] {d : ℕ} (b b' : Module.Basis (Fin d) F E) (c : F)
    (h : ∀ y k, b'.repr y k = c * b.repr y k) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b').repr y k =
      algebraMap F R c * (Algebra.TensorProduct.basis R b).repr y k := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, h,
      smul_eq_mul, map_mul]
    ring
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add]

theorem exists_clear (v : HeightOneSpectrum (𝓞 F)) (s : Finset F) :
    ∃ c : F, c ≠ 0 ∧ ∀ x ∈ s, algebraMap F (Fv F v) (c * x) ∈ v.adicCompletionIntegers F := by
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) s
  refine ⟨algebraMap (𝓞 F) F c, ?_, fun x hx => ?_⟩
  · simpa using nonZeroDivisors.ne_zero c.2
  · obtain ⟨y, hy⟩ := hc x hx
    have : algebraMap (𝓞 F) F c * x = algebraMap (𝓞 F) F y := by
      rw [hy, Algebra.smul_def]
    have h2 : Valued.v (algebraMap F (Fv F v) (algebraMap (𝓞 F) F y)) =
        v.valuation F (algebraMap (𝓞 F) F y) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [this, HeightOneSpectrum.mem_adicCompletionIntegers, h2]
    exact v.valuation_le_one y

theorem exists_scaled_basis {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {M : ℕ}
    (n : ℕ) (g : GL (Fin M) E) :
    ∃ b' : Module.Basis (Fin d) F E, ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v → X ∈ latV b' v := by
  classical
  set h : Matrix (Fin M) (Fin M) E := ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) with hh
  obtain ⟨c, hc, hcs⟩ := exists_clear v
    ((Finset.univ : Finset (Fin M × Fin M × Fin d × Fin d)).image fun p =>
      b.repr (b p.2.2.1 * h p.1 p.2.1) p.2.2.2)
  refine ⟨b.unitsSMul fun _ => (Units.mk0 c hc)⁻¹, fun X hX a i l => ?_⟩
  have hrep : ∀ (y : E) (k : Fin d), (b.unitsSMul fun _ => (Units.mk0 c hc)⁻¹).repr y k = c * b.repr y k := by
    intro y k
    rw [Module.Basis.repr_unitsSMul]
    simp [Units.smul_def]
  rw [repr_scaled _ b _ c hrep]
  have hinv : X = actTup (Fv F v) (bc (inclR (Fv F v)) g⁻¹)
      (actTup (Fv F v) (bc (inclR (Fv F v)) g) X) := (GlobalTheory.CompanionTheory.SW.LatRat.actTup_inv _ g X).symm
  set Y := actTup (Fv F v) (bc (inclR (Fv F v)) g) X with hY
  have hXa : X a i = ∑ j, Y a j * inclR (Fv F v) (h i j) := by
    rw [hinv]
    simp only [actTup, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hXa, map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  rw [GlobalTheory.CompanionTheory.SW.LatRat.repr_mul, Finset.mul_sum]
  refine sum_mem fun k _ => ?_
  rw [mul_left_comm, ← map_mul]
  refine mul_mem (hX a j k) (hcs _ ?_)
  exact Finset.mem_image.2 ⟨(i, j, k, l), Finset.mem_univ _, rfl⟩

end Lat

section Theta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in

theorem ratAct_li_iff {M n : ℕ} (g : GL (Fin M) E) (X : Fin n → Fin M → E) :
    LinearIndependent E (ratAct (g : Matrix (Fin M) (Fin M) E) X) ↔ LinearIndependent E X :=
  li_mulVec_iff g X

omit [NumberField F] [NumberField E] in

def framesEquiv (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) :
    framesE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) T ≃
      framesE σ J T where
  toFun X := ⟨ratAct (g : Matrix (Fin M) (Fin M) E) X.1,
    (ratAct_li_iff g _).2 X.2.1, by rw [gramE_ratAct]; exact X.2.2⟩
  invFun Y := ⟨ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1,
    (ratAct_li_iff g⁻¹ _).2 Y.2.1, by
      rw [← gramE_ratAct, ratAct_mul, Units.mul_inv, ratAct_one]; exact Y.2.2⟩
  left_inv X := by
    apply Subtype.ext
    change ratAct _ (ratAct _ X.1) = X.1
    rw [ratAct_mul, Units.inv_mul, ratAct_one]
  right_inv Y := by
    apply Subtype.ext
    change ratAct _ (ratAct _ Y.1) = Y.1
    rw [ratAct_mul, Units.mul_inv, ratAct_one]

theorem theta_map_frames (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (g : GL (Fin M) E)
    [LocallyCompactSpace (AF F)] [SecondCountableTopology (AF F)] [T2Space (AF F)]
    (He : HA (AF F) σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) ≃ᵐ
      HA (AF F) σ J)
    (hmat : ∀ u, HA.mat (AF F) σ J (He u) =
      bc (inclR (AF F)) g * HA.mat (AF F) σ _ u * (bc (inclR (AF F)) g)⁻¹)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (T : Matrix (Fin n) (Fin n) E) :
    (thetaMeas σ _ (μ.map He.symm) (He ⁻¹' 𝓕)
      (framesE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) T)).map
        (actTup (AF F) (bc (inclR (AF F)) g)) =
      thetaMeas σ J μ 𝓕 (framesE σ J T) := by
  have hJ' := isHermND_conj σ hCM J hJ g
  obtain ⟨tg, -, -, -, bs, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  obtain ⟨tg', -, -, -, bs', hact'⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M _ hJ' (AF F)
  haveI := tg
  haveI := tg'
  haveI := bs
  haveI := bs'
  haveI : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)).2.2.2.2.2.2.2.1 n M
  set G : GL (Fin M) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG
  have hmG := measurable_actTup (n := n) σ hCM (AF F) G
  have hmf : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ Y := fun Y =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have hmf' : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Measurable fun h : HA (AF F) σ _ => actW (AF F) σ _ h⁻¹ Y := fun Y =>
    ((hact' n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have hmass : (μ.map He.symm) (He ⁻¹' 𝓕) = μ 𝓕 := by
    rw [He.symm.map_apply]
    congr 1
    ext x
    simp
  have hrest : ((μ.map He.symm).restrict (He ⁻¹' 𝓕)).map He = μ.restrict 𝓕 := by
    rw [← He.restrict_map, Measure.map_map He.measurable He.symm.measurable]
    simp
  unfold thetaMeas
  rw [Measure.map_smul, hmass]
  congr 1
  rw [Measure.map_sum hmG.aemeasurable, ← sum_reindex (framesEquiv σ J g T)]
  congr 1
  funext X
  rw [Measure.map_map hmG (hmf' _)]
  have hcomp : (actTup (AF F) G ∘ fun h => actW (AF F) σ _ h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) =
      (fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) ((framesEquiv σ J g T X : _) : Fin n → Fin M → E))) ∘ He := by
    funext h
    have := act_conj (AF F) σ G He hmat h (ratTup (AF F) (X : Fin n → Fin M → E))
    simp only [Function.comp]
    rw [this, ← ratTup_ratAct]
    rfl
  rw [hcomp, ← Measure.map_map (hmf _) He.measurable, hrest]

end Theta

theorem swFree_of_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * g → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J' T hT → SWFree σ J T hT := by
  intro F E _ _ _ _ _ σ hCM M J hJ g J' hJ'eq n T hT hSW
  subst hJ'eq
  have hJ' := isHermND_conj σ hCM J hJ g
  intro d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨e, hmat, hrat⟩ := GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry F E σ hCM M J hJ g _ rfl (AF F)
  obtain ⟨tg, -, -, -, bs, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  obtain ⟨tg', -, -, -, bs', -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M _ hJ' (AF F)
  haveI := tg
  haveI := tg'
  haveI := bs
  haveI := bs'
  haveI : μ.IsHaarMeasure := hμ
  let He := e.toHomeomorph.toMeasurableEquiv
  have hμ' : IsHaarH F E σ M _ (μ.map He.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  have hmm : (μ.map He.symm).map He = μ := by
    rw [Measure.map_map He.measurable He.symm.measurable]
    simp
  have hq : Measure.QuasiMeasurePreserving e (μ.map He.symm) μ :=
    (MeasurePreserving.mk He.measurable hmm).quasiMeasurePreserving
  have h𝓕' : IsFDH F E σ M _ (μ.map He.symm) (He ⁻¹' 𝓕) :=
    isFD_pull σ e.toMulEquiv hrat hq h𝓕
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := haar_of_loc σ hCM (Ainf F) hLi b laminf hinf.1 n M
  have hWv := fun v => haar_of_loc σ hCM (Fv F v) (hLv v) b (lam v) (hlam v).1 n M
  obtain ⟨cinf, c, hUP, hci, hcv⟩ := GlobalTheory.T.haar_modulus_gl_action_product_formula F E σ hCM n M g
  obtain ⟨minf', hminf', hmapi, -⟩ :=
    local_transport σ hCM J g (Ainf F) hLi n _ _ minf hminf cinf (hci _ hWi.1)
  choose m' hm' hmapv hpre using fun v =>
    local_transport σ hCM J g (Fv F v) (hLv v) n _ _ (m v) (hm v) (c v) (hcv v _ (hWv v).1)
  have hEul := hSW d b laminf lam hinf hlam (μ.map He.symm) (He ⁻¹' 𝓕) hμ' h𝓕' minf' m' hminf' hm'
  have hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤ := by
    intro v
    obtain ⟨b', hb'⟩ := exists_scaled_basis (n := n) b v g
    obtain ⟨ri, -, hri⟩ := local_rescale σ hCM _ (Ainf F) hLi b b' laminf hinf.1 n minf' hminf'
    choose r hr0 hrw using fun w =>
      local_rescale σ hCM _ (Fv F w) (hLv w) b b' (lam w) (hlam w).1 n (m' w) (hm' w)
    have h1 := (hSW d b' laminf lam hinf hlam (μ.map He.symm) (He ⁻¹' 𝓕) hμ' h𝓕' _ _ hri hrw).1 v
    have hc0 : c v ≠ 0 := by
      intro h0
      have h2 := hcv v _ (hWv v).1
      rw [h0, zero_smul] at h2
      have h3 := (Measure.map_eq_zero_iff
        (measurable_of_loc σ hCM (Fv F v) (hLv v) (bc (inclR (Fv F v)) g)).aemeasurable).1 h2
      haveI := (hWv v).1
      exact NeZero.ne (coordW (Fv F v) b (lam v) n M) h3
    have h2 : (c v : ℝ≥0∞) * m v (hermOf (Fv F v) σ T hT) (latV b v) ≤
        m' v (hermOf (Fv F v) σ T hT) (latV b' v) := by
      rw [← hpre v _ (latV b v)]
      exact measure_mono fun X hX => hb' X hX
    have h3 : m' v (hermOf (Fv F v) σ T hT) (latV b' v) < ⊤ := by
      by_contra h
      rw [not_lt, top_le_iff] at h
      rw [Measure.smul_apply, h] at h1
      have h4 : r v • (⊤ : ℝ≥0∞) = ⊤ := by
        rw [ENNReal.smul_def, smul_eq_mul]
        exact ENNReal.mul_top (by simpa using hr0 v)
      rw [h4] at h1
      exact lt_irrefl _ h1
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.mul_top (by simpa using hc0)] at h2
    exact absurd (lt_of_le_of_lt h2 h3) (lt_irrefl _)
  have hproj : ∀ X : Fin n → Fin M → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) g) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) g) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) g) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) g) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact map_actTup (fstA F) g X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) g) X) =
          actTup (Af F) (bc (inclR (Af F)) g) (projFin X) := by
        funext a i
        exact map_actTup (sndA F) g X a i
      rw [h1]
      funext a i
      exact map_actTup (evalV F v) g (projFin X) a i
  have key := GlobalTheory.T.euler_product_measure_transport F E σ hCM d b n M _ (minf' (hermOf (Ainf F) σ T hT))
    (minf (hermOf (Ainf F) σ T hT)) (fun v => m' v (hermOf (Fv F v) σ T hT))
    (fun v => m v (hermOf (Fv F v) σ T hT)) (actTup (AF F) (bc (inclR (AF F)) g))
    (actTup (Ainf F) (bc (inclR (Ainf F)) g)) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) g))
    (measurable_actTup σ hCM (AF F) _) (measurable_of_loc σ hCM (Ainf F) hLi _)
    (fun v => measurable_of_loc σ hCM (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hCM d b n M).2.1 g) cinf c hUP
    (hmapi _) (fun v => hmapv v _) hfin hEul
  have hth := theta_map_frames (n := n) σ hCM J hJ g He hmat μ 𝓕 T
  rw [hth] at key
  exact key

end GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso
