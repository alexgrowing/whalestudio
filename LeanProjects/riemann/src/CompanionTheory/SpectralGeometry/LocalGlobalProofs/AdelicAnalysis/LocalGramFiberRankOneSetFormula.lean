import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresTransitivityStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FibreRatio

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem conj_invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_conj_ne (h : IsCMExt F E σ) : ∃ e : E, σ e ≠ e := by
  by_contra hσ
  push_neg at hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

theorem exists_imag (h : IsCMExt F E σ) :
    ∃ w : E, σ w = -w ∧ ∀ e : E, ∃ a c : F, a • (1 : E) + c • w = e := by
  obtain ⟨e, he⟩ := exists_conj_ne h
  refine ⟨e - σ e, by rw [map_sub, conj_invol h]; ring, ?_⟩
  set w := e - σ e with hw
  have hw' : σ w = -w := by rw [hw, map_sub, conj_invol h]; ring
  have hw0 : w ≠ 0 := fun h0 => he (sub_eq_zero.mp h0).symm
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hli : LinearIndependent F ![(1 : E), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : s • (1 : E) - t • w = 0 := by
      have := congrArg σ hst
      have e1 : ∀ (a : F) (x : E), σ (a • x) = a • σ x := fun a x => by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.smul_def]
      rw [map_add, e1, e1, map_one, hw', map_zero, smul_neg] at this
      rw [sub_eq_add_neg]
      exact this
    have h3 : (2 * s) • (1 : E) = 0 := by
      have : (2 * s) • (1 : E) = (s • (1 : E) + t • w) + (s • (1 : E) - t • w) := by
        rw [two_mul, add_smul]; abel
      rw [this, hst, h1, add_zero]
    have hs : s = 0 := by
      have := (smul_eq_zero.mp h3).resolve_right one_ne_zero
      exact (mul_eq_zero.mp this).resolve_left h2
    have ht : t = 0 := by
      rw [hs, zero_smul, zero_add] at hst
      exact (smul_eq_zero.mp hst).resolve_right hw0
    exact ⟨hs, ht⟩
  have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [h.2.2.1])
  intro x
  have hx : x ∈ Submodule.span F (Set.range ![(1 : E), w]) := by rw [htop]; trivial
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton] at hx
  rw [Set.pair_comm, Submodule.mem_span_pair] at hx
  exact hx

variable (R : Type) [Field R] [Algebra F R]

theorem sigR_tmul (r : R) (e : E) : sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by
  simp [sigR]

theorem fixed_tmul (h : IsCMExt F E σ) (y : R ⊗[F] E) (hy : sigR R σ y = y) :
    ∃ r : R, y = r ⊗ₜ[F] (1 : E) := by
  obtain ⟨w, hw, hspan⟩ := exists_imag h
  have hdec : ∀ y : R ⊗[F] E, ∃ r t : R, y = r ⊗ₜ[F] (1 : E) + t ⊗ₜ[F] w := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul r e =>
      obtain ⟨a, c, rfl⟩ := hspan e
      refine ⟨a • r, c • r, ?_⟩
      rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨r, t, rfl⟩ := hx
      obtain ⟨r', t', rfl⟩ := hy
      refine ⟨r + r', t + t', ?_⟩
      rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel
  obtain ⟨r, t, rfl⟩ := hdec y
  refine ⟨r, ?_⟩
  have h1 : sigR R σ (t ⊗ₜ[F] w) = -(t ⊗ₜ[F] w) := by
    rw [sigR_tmul, hw, TensorProduct.tmul_neg]
  have h0 : sigR R σ (r ⊗ₜ[F] (1 : E)) = r ⊗ₜ[F] (1 : E) := by
    rw [sigR_tmul, map_one]
  rw [map_add, h0, h1] at hy
  have h2 : (2 : F) • (t ⊗ₜ[F] w) = 0 := by
    have : t ⊗ₜ[F] w = -(t ⊗ₜ[F] w) := (add_left_cancel hy).symm
    rw [two_smul]
    nth_rw 1 [this]
    abel
  have h3 : t ⊗ₜ[F] w = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [h3, add_zero]

theorem half_trace_tmul (h : IsCMExt F E σ) (r : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r := by
  have h1 : r ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) r := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  have h2 : (algebraMap F R 2) = 2 := map_ofNat _ 2
  rw [h1, Algebra.trace_algebraMap, Module.finrank_baseChange, h.2.2.1]
  have h3 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← h2, ← map_mul]; simp
  rw [two_nsmul, ← two_mul, ← mul_assoc, h3, one_mul]

variable {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem sigR_hR_self (h : IsCMExt F E σ) (hJ : IsHermND σ J) (x : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x x) = hR R σ J x x := by
  have hinv : ∀ y : R ⊗[F] E, sigR R σ (sigR R σ y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => rw [sigR_tmul, sigR_tmul, conj_invol h]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hJR : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    simp only [JR, Matrix.map_apply, inclR]
    show sigR R σ ((1 : R) ⊗ₜ[F] J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [sigR_tmul, hJ.1]
  show sigR R σ (hform (sigR R σ) (JR R J) x x) = hform (sigR R σ) (JR R J) x x
  simp only [hform, map_sum, map_mul, hinv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJR]
  ring

def qS (σ : E →ₐ[F] E) (S : HermR R σ 1) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)

theorem qS_hermScal (h : IsCMExt F E σ) (r : R) : qS R σ (hermScal R σ r) = r :=
  half_trace_tmul R h r

theorem hermScal_qS (h : IsCMExt F E σ) (S : HermR R σ 1) : hermScal R σ (qS R σ S) = S := by
  have hfix : sigR R σ ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) =
      (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 := S.2 0 0
  obtain ⟨r, hr⟩ := fixed_tmul R h _ hfix
  have hq : qS R σ S = r := by
    unfold qS
    rw [hr]
    exact half_trace_tmul R h r
  apply Subtype.ext
  funext a c
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain rfl : c = 0 := Subsingleton.elim _ _
  rw [hq, hr]
  rfl

theorem gram_entry (h : IsCMExt F E σ) (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    gramR R σ J X 0 0 =
      (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)) ⊗ₜ[F] (1 : E) := by
  obtain ⟨r, hr⟩ := fixed_tmul R h (gramR R σ J X 0 0) (sigR_hR_self R h hJ (X 0))
  rw [hr, half_trace_tmul R h r]

theorem isUnit_tmul {r : R} (hr : r ≠ 0) : IsUnit (r ⊗ₜ[F] (1 : E)) := by
  have h1 : r ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) r := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h1]
  exact (isUnit_iff_ne_zero.mpr hr).map _

end Alg

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
variable (R : Type) [Field R] [Algebra F R] [TopologicalSpace R]

theorem continuous_hermScal [IsTopologicalRing R] : Continuous (hermScal R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  have h1 : Continuous fun r : R => r ⊗ₜ[F] (1 : E) := by
    have : (fun r : R => r ⊗ₜ[F] (1 : E)) = (Algebra.linearMap R (R ⊗[F] E) : R → R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.algebraMap_apply]
    rw [this]
    exact IsModuleTopology.continuous_of_linearMap _
  refine Continuous.subtype_mk ?_ _
  exact continuous_matrix fun _ _ => h1

theorem continuous_qS (htr : Continuous (Algebra.trace R (R ⊗[F] E))) [IsTopologicalRing R] :
    Continuous (qS R σ) := by
  unfold qS
  refine continuous_const.mul (htr.comp ?_)
  exact (continuous_subtype_val.matrix_elem 0 0)

variable [MeasurableSpace R] [BorelSpace R]

theorem coordHerm_qS (h : IsCMExt F E σ) [IsTopologicalRing R] [SecondCountableTopology R]
    (htr : Continuous (Algebra.trace R (R ⊗[F] E)))
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) [SigmaFinite lam] {V : Set R}
    (hV : MeasurableSet V) : coordHerm R σ b lam 1 {S | qS R σ S ∈ V} = lam V := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  haveI : IsEmpty {p : Fin 1 × Fin 1 // p.1 < p.2} :=
    ⟨fun p => by
      have h1 := p.2
      have h2 : p.1.1 = p.1.2 := Subsingleton.elim _ _
      rw [h2] at h1
      exact lt_irrefl _ h1⟩
  set f : HermR R σ 1 → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) :=
    fun S => ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin 1 × Fin 1 // p.1 < p.2} => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))
    with hf
  set g : (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) → HermR R σ 1 :=
    fun x => hermScal R σ (x.1 0) with hg
  have hgm : Measurable g :=
    (continuous_hermScal R).measurable.comp ((measurable_pi_apply 0).comp measurable_fst)
  have hgf : ∀ S, g (f S) = S := fun S => hermScal_qS R h S
  have hfg : ∀ x, f (g x) = x := by
    intro x
    refine Prod.ext ?_ (funext fun p => isEmptyElim p)
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact qS_hermScal R h (x.1 0)
  have himg : ∀ s : Set (HermR R σ 1), f '' s = g ⁻¹' s := by
    intro s
    ext x
    constructor
    · rintro ⟨S, hS, rfl⟩
      simpa [hgf S] using hS
    · intro hx
      exact ⟨g x, hx, hfg x⟩
  have hinj : Function.Injective f := Function.LeftInverse.injective hgf
  have hP : MeasurableSet {S | qS R σ S ∈ V} := (continuous_qS R htr).measurable hV
  have hset : f '' {S | qS R σ S ∈ V} = (Set.pi Set.univ fun _ : Fin 1 => V) ×ˢ Set.univ := by
    rw [himg]
    ext x
    have e : qS R σ (g x) = x.1 0 := qS_hermScal R h (x.1 0)
    simp [e]
  show Measure.comap f _ _ = _
  rw [Measure.comap_apply f hinj (fun s hs => by rw [himg]; exact hgm hs) _ hP, hset,
    Measure.pi_of_empty (fun _ : {p : Fin 1 × Fin 1 // p.1 < p.2} => coordK R b lam),
    Measure.prod_prod, Measure.pi_pi]
  simp

end Meas

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem mass_eq_lintegral (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {μ : Measure (Fin 1 → Fin M → R ⊗[F] E)} {ν : Measure (HermR R σ 1)}
    {m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E)} (hfib : IsGramFib R σ J 1 μ ν m)
    {A : Set (Fin 1 → Fin M → R ⊗[F] E)} (hA : MeasurableSet A) {V : Set R} (h0 : (0 : R) ∉ V)
    (hQ : MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V})
    (hP : MeasurableSet {S | qS R σ S ∈ V}) :
    μ (A ∩ {X | algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V}) =
      ∫⁻ S in {S | qS R σ S ∈ V}, m S A ∂ν := by
  obtain ⟨hf1, hf2, -⟩ := hfib
  set Q : Set (Fin 1 → Fin M → R ⊗[F] E) :=
    {X | algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V} with hQdef
  set W : Set (Fin 1 → Fin M → R ⊗[F] E) := {X | IsUnit (gramR R σ J X).det} with hW
  have hAQ : MeasurableSet (A ∩ Q) := hA.inter hQ
  have hQW : Q ⊆ W := by
    intro X hX
    have hne : algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ≠ 0 :=
      fun e => h0 (e ▸ hX)
    show IsUnit (gramR R σ J X).det
    rw [Matrix.det_fin_one, gram_entry R h hJ X]
    exact isUnit_tmul R hne
  have key := hf2 ((A ∩ Q).indicator 1) (measurable_one.indicator hAQ)
  rw [lintegral_indicator_one₀ hAQ.nullMeasurableSet, Measure.restrict_apply hAQ,
    Set.inter_eq_left.mpr (Set.inter_subset_right.trans hQW)] at key
  rw [key, ← lintegral_indicator hP]
  refine lintegral_congr fun S => ?_
  rw [lintegral_indicator_one hAQ]
  set G : Set (Fin 1 → Fin M → R ⊗[F] E) := gramR R σ J ⁻¹' {(S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))} ∩ W
    with hG
  have hGc : m S Gᶜ = 0 := hf1 S
  have hGq : ∀ X ∈ G, algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) =
      qS R σ S := by
    intro X hX
    have : gramR R σ J X = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hX.1
    rw [this]
    rfl
  by_cases hS : qS R σ S ∈ V
  · rw [Set.indicator_of_mem (show S ∈ {S | qS R σ S ∈ V} from hS)]
    refine le_antisymm (measure_mono Set.inter_subset_left) ?_
    calc m S A = m S (A ∩ G) := (measure_inter_conull hGc).symm
      _ ≤ m S (A ∩ Q) := measure_mono fun X hX => ⟨hX.1, by
          show _ ∈ V
          rw [hGq X hX.2]; exact hS⟩
  · rw [Set.indicator_of_notMem (show S ∉ {S | qS R σ S ∈ V} from hS)]
    have hsub : A ∩ Q ⊆ Gᶜ := by
      intro X hX hXG
      have hXQ : algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V := hX.2
      rw [hGq X hXG] at hXQ
      exact hS hXQ
    exact measure_mono_null hsub hGc

theorem ratio_field (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hloc : IsLocR R) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m)
    (A : Set (Fin 1 → Fin M → R ⊗[F] E)) (hAc : IsCompact A) (hAo : IsOpen A)
    (s : R) (hs : s ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ 𝓝 s, ∀ V : Set R, MeasurableSet V → V ⊆ U →
      |(coordW R b lam 1 M (A ∩ {X | algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V})).toReal -
        (m (hermScal R σ s) A).toReal * (lam V).toReal| ≤ ε * (lam V).toReal := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, hT2, -, htr, -, hBor, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h R
  haveI := hT2
  haveI := hBor 1 M
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  have hHaar := GlobalTheory.T.coordinate_haar_measure F E σ h R d b lam hlam
  have hμ := hHaar.2.1 1 M
  have hν := hHaar.2.2 1
  have hAm : MeasurableSet A := hAo.measurableSet
  set φ : (Fin 1 → Fin M → R ⊗[F] E) → ℂ := A.indicator fun _ => 1 with hφ
  have hAclopen : IsClopen A := ⟨hAc.isClosed, hAo⟩
  have hφc : Continuous φ :=
    continuous_indicator (by simp [hAclopen.frontier_eq]) continuousOn_const
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _
  obtain ⟨⟨hg, -⟩, -⟩ := GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib φ hφc hφs
  have hfin : ∀ S, m S A < ⊤ := fun S => by
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib S).1
    exact hAc.measure_lt_top
  have hint : ∀ S, ∫ X, φ X ∂(m S) = (((m S A).toReal : ℝ) : ℂ) := fun S => by
    rw [hφ, integral_indicator_const _ hAm]
    simp [Measure.real]
  have hunit : hermScal R σ s ∈ {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} := by
    show IsUnit (Matrix.det _)
    rw [Matrix.det_fin_one]
    exact isUnit_tmul R hs
  have hne : ∀ᶠ t in 𝓝 s, t ≠ 0 := isOpen_ne.mem_nhds hs
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R
  have htend : Filter.Tendsto (hermScal R σ) (𝓝 s)
      (𝓝[{S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det}] (hermScal R σ s)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hcs.tendsto s, hne.mono fun t ht => ?_⟩
    show IsUnit (Matrix.det _)
    rw [Matrix.det_fin_one]
    exact isUnit_tmul R ht
  have hlim : Filter.Tendsto (fun t => (m (hermScal R σ t) A).toReal) (𝓝 s)
      (𝓝 (m (hermScal R σ s) A).toReal) := by
    have := (Complex.continuous_re.tendsto _).comp ((hg _ hunit).tendsto.comp htend)
    simpa [Function.comp_def, hint] using this
  obtain ⟨W, hW, hWfin⟩ := lam.finiteAt_nhds s
  set c := (m (hermScal R σ s) A).toReal with hc
  have hnear : ∀ᶠ t in 𝓝 s, |(m (hermScal R σ t) A).toReal - c| < ε := by
    have := (Metric.tendsto_nhds.mp hlim) ε hε
    simpa [Real.dist_eq] using this
  refine ⟨W ∩ {t | t ≠ 0 ∧ |(m (hermScal R σ t) A).toReal - c| < ε},
    Filter.inter_mem hW (hne.and hnear), fun V hV hVU => ?_⟩
  have hV0 : (0 : R) ∉ V := fun h0 => (hVU h0).2.1 rfl
  have hLfin : lam V ≠ ⊤ := ((measure_mono fun x hx => (hVU hx).1).trans_lt hWfin).ne
  have hP : MeasurableSet {S | qS R σ S ∈ V} := (continuous_qS R htr).measurable hV
  have hQ : MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V} := by
    have hcq : Continuous fun X : Fin 1 → Fin M → R ⊗[F] E =>
        algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) :=
      continuous_const.mul (htr.comp ((hgr 1 M J).matrix_elem 0 0))
    exact hcq.measurable hV
  have hνP : coordHerm R σ b lam 1 {S | qS R σ S ∈ V} = lam V := coordHerm_qS R h htr b lam hV
  have heq := mass_eq_lintegral R h hJ hfib hAm hV0 hQ hP
  set I := coordW R b lam 1 M (A ∩ {X | algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V}) with hI
  have hbd : ∀ S ∈ {S | qS R σ S ∈ V}, |(m S A).toReal - c| < ε := by
    intro S hS
    have := (hVU hS).2.2
    rwa [hermScal_qS R h S] at this
  have hup : I ≤ ENNReal.ofReal (c + ε) * lam V := by
    rw [heq, ← hνP, ← setLIntegral_const]
    refine setLIntegral_mono' hP fun S hS => ?_
    rw [← ENNReal.ofReal_toReal (hfin S).ne]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hbd S hS)).2])
  have hlo : ENNReal.ofReal (c - ε) * lam V ≤ I := by
    rw [heq, ← hνP, ← setLIntegral_const]
    refine setLIntegral_mono' hP fun S hS => ?_
    rw [← ENNReal.ofReal_toReal (hfin S).ne]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hbd S hS)).1])
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hL0 : 0 ≤ (lam V).toReal := ENNReal.toReal_nonneg
  have hIfin : I ≠ ⊤ := (hup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hLfin.lt_top)).ne
  have hup' : I.toReal ≤ (c + ε) * (lam V).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLfin) hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have hlo' : (c - ε) * (lam V).toReal ≤ I.toReal := by
    have := ENNReal.toReal_mono hIfin hlo
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0).trans this
  rw [abs_le]
  constructor <;> nlinarith

end Main

end GlobalTheory.CompanionTheory.SW.FibreRatio

namespace GlobalTheory.CompanionTheory.SW

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem fibre_mass_ratio : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → ∀ s : Fv F v, s ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 s, ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U → |(coordW (Fv F v) b lam 1 M (A ∩ {X | algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal - (m (hermScal (Fv F v) σ s) A).toReal * (lam V).toReal| ≤ ε * (lam V).toReal := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b v lam hlam m hfib A hAc hAo s hs ε hε
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact FibreRatio.ratio_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ hJ b lam hlam.1 m hfib A hAc hAo s hs ε hε

end GlobalTheory.CompanionTheory.SW
