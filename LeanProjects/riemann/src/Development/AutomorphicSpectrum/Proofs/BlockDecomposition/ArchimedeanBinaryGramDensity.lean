import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel

open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ArchFibre

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R]

def qR (σ : E →ₐ[F] E) (S : HermR R σ 1) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)

theorem qR_hermScal (h : IsCMExt F E σ) (r : R) : qR R σ (hermScal R σ r) = r :=
  HaarCoord.half_trace_tmul R h.2.2.1 r

theorem hermScal_qR (h : IsCMExt F E σ) (S : HermR R σ 1) : hermScal R σ (qR R σ S) = S := by
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts h
  obtain ⟨r, hr⟩ := HaarCoord.fixed_eq_tmul R hinv h.2.2.1 hδ hσδ
    ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) (S.2 0 0)
  have hq : qR R σ S = r := by
    unfold qR
    rw [hr]
    exact HaarCoord.half_trace_tmul R h.2.2.1 r
  apply Subtype.ext
  funext a c
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain rfl : c = 0 := Subsingleton.elim _ _
  rw [hq, hr]
  rfl

end Alg

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

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

theorem continuous_qR (htr : Continuous (Algebra.trace R (R ⊗[F] E))) [IsTopologicalRing R] :
    Continuous (qR R σ) := by
  unfold qR
  refine continuous_const.mul (htr.comp ?_)
  exact (continuous_subtype_val.matrix_elem 0 0)

variable [MeasurableSpace R] [BorelSpace R]

theorem coordHerm_qR (h : IsCMExt F E σ) [IsTopologicalRing R] [SecondCountableTopology R]
    (htr : Continuous (Algebra.trace R (R ⊗[F] E)))
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) [SigmaFinite lam] {V : Set R}
    (hV : MeasurableSet V) : coordHerm R σ b lam 1 {S | qR R σ S ∈ V} = lam V := by
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
  have hgf : ∀ S, g (f S) = S := fun S => hermScal_qR R h S
  have hfg : ∀ x, f (g x) = x := by
    intro x
    refine Prod.ext ?_ (funext fun p => isEmptyElim p)
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact qR_hermScal R h (x.1 0)
  have himg : ∀ s : Set (HermR R σ 1), f '' s = g ⁻¹' s := by
    intro s
    ext x
    constructor
    · rintro ⟨S, hS, rfl⟩
      simpa [hgf S] using hS
    · intro hx
      exact ⟨g x, hx, hfg x⟩
  have hinj : Function.Injective f := Function.LeftInverse.injective hgf
  have hP : MeasurableSet {S | qR R σ S ∈ V} := (continuous_qR R htr).measurable hV
  have hset : f '' {S | qR R σ S ∈ V} = (Set.pi Set.univ fun _ : Fin 1 => V) ×ˢ Set.univ := by
    rw [himg]
    ext x
    have e : qR R σ (g x) = x.1 0 := qR_hermScal R h (x.1 0)
    simp [e]
  show Measure.comap f _ _ = _
  rw [Measure.comap_apply f hinj (fun s hs => by rw [himg]; exact hgm hs) _ hP, hset,
    Measure.pi_of_empty (fun _ : {p : Fin 1 × Fin 1 // p.1 < p.2} => coordK R b lam),
    Measure.prod_prod, Measure.pi_pi]
  simp

theorem coordHerm_eq_map (h : IsCMExt F E σ) [IsTopologicalRing R] [SecondCountableTopology R]
    (htr : Continuous (Algebra.trace R (R ⊗[F] E)))
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) [SigmaFinite lam] :
    coordHerm R σ b lam 1 = Measure.map (hermScal R σ) lam := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  have hm : Measurable (hermScal R σ (F := F) (E := E)) := (continuous_hermScal R).measurable
  ext A hA
  rw [Measure.map_apply hm hA, ← coordHerm_qR R h htr b lam (hm hA)]
  congr 1
  ext S
  simp [hermScal_qR R h S]

theorem measurableEmbedding_hermScal (h : IsCMExt F E σ) [IsTopologicalRing R]
    (htr : Continuous (Algebra.trace R (R ⊗[F] E))) :
    MeasurableEmbedding (hermScal R σ (F := F) (E := E)) := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  let e : R ≃ᵐ HermR R σ 1 :=
    { toFun := hermScal R σ
      invFun := qR R σ
      left_inv := qR_hermScal R h
      right_inv := hermScal_qR R h
      measurable_toFun := (continuous_hermScal R).measurable
      measurable_invFun := (continuous_qR R htr).measurable }
  exact e.measurableEmbedding

end Meas

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem fibre_integral (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hloc : IsLocR R) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m)
    (φ : (Fin 1 → Fin M → R ⊗[F] E) → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ X, 0 ≤ φ X) (hφU : tsupport φ ⊆ {X | IsUnit (gramR R σ J X).det}) :
    Continuous (fun s : R => ∫ X, φ X ∂(m (hermScal R σ s))) ∧
    HasCompactSupport (fun s : R => ∫ X, φ X ∂(m (hermScal R σ s))) ∧
    (∀ s : R, ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (hermScal R σ s)) =
      ENNReal.ofReal (∫ X, φ X ∂(m (hermScal R σ s)))) ∧
    ENNReal.ofReal (∫ s, (∫ X, φ X ∂(m (hermScal R σ s))) ∂lam) =
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 M) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI := hlam
  obtain ⟨iTR, iLC, iSC, iT2, -, htr, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h R
  haveI := iB 1 M
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ h R 1
  haveI := jB
  obtain ⟨g, hg, hgram⟩ := hlift M J hJ
  have hunits : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := GlobalTheory.T.units_open_embedding_local_tensor F E σ h R hloc
  set B : Set (HermR R σ 1) := {S | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} with hBdef
  set U : Set (Fin 1 → Fin M → R ⊗[F] E) := {X | IsUnit (gramR R σ J X).det} with hUdef
  have hB : IsOpen B := by
    have hdet : Continuous fun S : HermR R σ 1 => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have hset : B = (fun S : HermR R σ 1 => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp [B, IsUnit]
    rw [hset]
    exact hunits.isOpen_range.preimage hdet
  have hUo : IsOpen U := by
    have hpre : U = g ⁻¹' B := by
      ext X
      simp [U, B, hgram X]
    rw [hpre]
    exact hB.preimage hg
  obtain ⟨hf1, hf2, hf3⟩ := hfib
  obtain ⟨hint, hcont⟩ := hf3 φ hφ hφc hφU
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R
  set I : R → ℝ := fun s => ∫ X, φ X ∂(m (hermScal R σ s)) with hI
  set K : Set R := (fun X => qR R σ (g X)) '' tsupport φ with hKdef
  have hK : IsCompact K := hφc.isCompact.image ((continuous_qR R htr).comp hg)
  have hzero : ∀ s, s ∉ K → I s = 0 := by
    intro s hs
    refine integral_eq_zero_of_ae ?_
    filter_upwards [mem_ae_iff.mpr (hf1 (hermScal R σ s))] with X hX
    by_contra hne
    apply hs
    refine ⟨X, subset_tsupport _ (Function.mem_support.mpr hne), ?_⟩
    have e : g X = hermScal R σ s := Subtype.ext ((hgram X).symm.trans hX.1)
    show qR R σ (g X) = s
    rw [e, qR_hermScal R h]
  have hKB : ∀ s ∈ K, hermScal R σ s ∈ B := by
    rintro _ ⟨X, hX, rfl⟩
    have e : hermScal R σ (qR R σ (g X)) = g X := hermScal_qR R h (g X)
    show hermScal R σ (qR R σ (g X)) ∈ B
    rw [e]
    show IsUnit (g X : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det
    rw [← hgram X]
    exact hφU hX
  have hcontI : Continuous I := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : s ∈ K
    · have hD : IsOpen (hermScal R σ ⁻¹' B) := hB.preimage hcs
      have hon : ContinuousOn I (hermScal R σ ⁻¹' B) :=
        hcont.comp hcs.continuousOn (fun _ hx => hx)
      exact hon.continuousAt (hD.mem_nhds (hKB s hs))
    · have hev : I =ᶠ[𝓝 s] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hs) fun t ht => hzero t ht
      exact continuousAt_const.congr hev.symm
  have hcsI : HasCompactSupport I := HasCompactSupport.intro hK hzero
  have hintAll : ∀ S, Integrable φ (m S) := by
    intro S
    by_cases hS : S ∈ B
    · exact hint S hS
    · have hu : (gramR R σ J ⁻¹' {(S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))} ∩ U)ᶜ = Set.univ := by
        rw [Set.compl_univ_iff, Set.eq_empty_iff_forall_notMem]
        rintro X ⟨hX1, hX2⟩
        apply hS
        show IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det
        have hX1' : gramR R σ J X = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hX1
        rw [← hX1']
        exact hX2
      have h0 : m S = 0 := by
        have := hf1 S
        rw [show (Subtype.val S) = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) from rfl, hu] at this
        exact Measure.measure_univ_eq_zero.mp this
      rw [h0]
      exact integrable_zero_measure
  have hthird : ∀ s : R, ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (hermScal R σ s)) = ENNReal.ofReal (I s) :=
    fun s => (ofReal_integral_eq_lintegral_ofReal (hintAll _) (Eventually.of_forall hφ0)).symm
  refine ⟨hcontI, hcsI, hthird, ?_⟩
  have hΦ : Measurable fun X => ENNReal.ofReal (φ X) := hφ.measurable.ennreal_ofReal
  have key := hf2 _ hΦ
  have hU : ∫⁻ X in U, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 M) =
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 M) := by
    rw [← lintegral_indicator hUo.measurableSet]
    congr 1
    refine Set.indicator_eq_self.mpr fun X hX => hφU (subset_tsupport _ ?_)
    intro h0
    apply hX
    simp [h0]
  rw [hU, coordHerm_eq_map R h htr b lam, (measurableEmbedding_hermScal R h htr).lintegral_map] at key
  rw [key, ofReal_integral_eq_lintegral_ofReal (hcontI.integrable_of_hasCompactSupport hcsI)
    (Eventually.of_forall fun s => integral_nonneg fun X => hφ0 X)]
  exact lintegral_congr fun s => (hthird s).symm

end Main

theorem fibre_integral_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ X, 0 ≤ φ X) →
  tsupport φ ⊆ {X | IsUnit (gramR (Ainf F) σ J X).det} →
  Continuous (fun s : Ainf F => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∧
  HasCompactSupport (fun s : Ainf F => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∧
  (∀ s : Ainf F, ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ s)) = ENNReal.ofReal (∫ X, φ X ∂(mi (hermScal (Ainf F) σ s)))) ∧
  ENNReal.ofReal (∫ s, (∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∂li) = ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 2) := by
  intro F E _ _ _ _ _ σ hσ J hJ d b li hli mi hfib φ hφ hφc hφ0 hφU
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact fibre_integral (Ainf F) (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1) hσ hJ b li hli.1 mi hfib φ hφ hφc hφ0 hφU

end GlobalTheory.CompanionTheory.SW.ArchFibre
