import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilOrbitalMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationDisintegrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductHaarMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFreeVectorsSameGramStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneFibreMeasureLocalStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeFact

theorem free_act {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (X : Fin n → Fin M → R ⊗[F] E) (hX : LinearIndependent (R ⊗[F] E) X) :
    LinearIndependent (R ⊗[F] E) (actW R σ J h X) := by
  let g : GL (Fin M) (R ⊗[F] E) := HA.mat R σ J h
  let e : (Fin M → R ⊗[F] E) ≃ₗ[R ⊗[F] E] (Fin M → R ⊗[F] E) :=
    Matrix.toLin'OfInv (M := ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)))
      (M' := (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))) (by simp) (by simp)
  have he : actW R σ J h X = e.toLinearMap ∘ X := by
    funext a
    simp [e, g, actW, actTup, Matrix.toLin'OfInv]
  rw [he]
  exact hX.map' e.toLinearMap (LinearEquiv.ker e)

theorem fib_compact_lt_top {V X Y : Type} [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V}
    {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) (hU : IsOpen U) (b : X)
    {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨φ, hc, hcs, hs, h0, -, h1⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump hK hU hKU
  have hi := (h.2.2 φ hc hcs hs).1 b (Set.mem_univ b)
  refine lt_of_le_of_lt (GlobalTheory.CompanionTheory.SW.FibreFam.le_lintegral_bump _ hK h0 h1) ?_
  exact hi.lintegral_lt_top

theorem local_pack_free {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R)
    (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b)
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hm : IsGramFibFree R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m) :
    (∀ K : Set (Fin 1 → Fin M → R ⊗[F] E), IsCompact K →
      K ⊆ {Y | LinearIndependent (R ⊗[F] E) Y} → m (hermOf R σ 0 h₀) K < ⊤) ∧
    (∀ h : HA R σ J, (m (hermOf R σ 0 h₀)).map (actW R σ J h) = m (hermOf R σ 0 h₀)) ∧
    m (hermOf R σ 0 h₀) ({Y | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
      {Y | LinearIndependent (R ⊗[F] E) Y})ᶜ = 0 ∧
    (({Y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
      {Y | LinearIndependent (R ⊗[F] E) Y}).Nonempty → m (hermOf R σ 0 h₀) ≠ 0) ∧
    (∀ X ∈ {Y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
        {Y | LinearIndependent (R ⊗[F] E) Y},
      ∀ Y ∈ {Y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
        {Y | LinearIndependent (R ⊗[F] E) Y},
      ∃ h : HA R σ J, actW R σ J h X = Y) := by
  obtain ⟨tr, lc, sc, t2, art, red, -⟩ := id hR
  haveI := tr
  haveI := lc
  haveI := sc
  haveI := t2
  obtain ⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (Fin 1 → Fin M → R ⊗[F] E) := tK8 1 M
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam
  haveI := hW 1 M
  haveI := hH 1
  have hU := GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ R hR 1 M
  have hz : (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (F := F) R) = 0 := by
    ext a c
    simp
  refine ⟨fun K hK hKU => fib_compact_lt_top hm hU _ hK hKU,
    fun h => GlobalTheory.T.local_gram_fibration_disintegration F E σ hσ M J hJ R hR 1 _ _ m (hW 1 M) (hH 1) hm h _, ?_, ?_, ?_⟩
  · exact hm.1 (hermOf R σ 0 h₀)
  · rintro ⟨X, hX, hXf⟩
    exact GlobalTheory.T.rank_one_fibre_measure_local F E σ hσ M J hJ R hR _ _ m (hW 1 M) (hH 1) hm X hXf (hX.trans hz) _
  · rintro X ⟨hX, hXf⟩ Y ⟨hY, hYf⟩
    exact GlobalTheory.T.isotropic_free_vectors_same_gram F E σ hσ M J hJ R hR X Y hXf hYf (hX.trans hz) (hY.trans hz)

theorem fact_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ I : Measure (Fin 1 → Fin M → AF F ⊗[F] E), IsLocallyFiniteMeasure I → (∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I) → I {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧ LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ = 0 → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ℝ≥0, ∀ (φinf : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → ∫⁻ X, pureL b S φinf φ X ∂I = (c : ℝ≥0∞) * ((∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b laminf lam hinf hlam minf hminf m hm I hIl hIinv hIT S
  classical
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  have hRI := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  have hRv := GlobalTheory.T.completion_is_local_ring F
  obtain ⟨trI, lcI, scI, t2I, -⟩ := id hRI
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hRv v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hRv v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hRv v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hRv v).2.2.2.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have kA := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  have kI := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  have kV := fun v => GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI := kA.1
  haveI := kA.2.1
  haveI := kA.2.2.1
  haveI := kA.2.2.2.1
  haveI := kA.2.2.2.2.2.2.2.1 1 M
  haveI := kI.1
  haveI := kI.2.1
  haveI := kI.2.2.1
  haveI := kI.2.2.2.1
  haveI := kI.2.2.2.2.2.2.2.1 1 M
  haveI : ∀ v, IsTopologicalRing (Fv F v ⊗[F] E) := fun v => (kV v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v ⊗[F] E) := fun v => (kV v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v ⊗[F] E) := fun v => (kV v).2.2.1
  haveI : ∀ v, T2Space (Fv F v ⊗[F] E) := fun v => (kV v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fin 1 → Fin M → Fv F v ⊗[F] E) := fun v => (kV v).2.2.2.2.2.2.2.1 1 M
  have uA := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  have uI := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (Ainf F)
  have uV := fun v => GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (Fv F v)
  haveI := uI.1
  haveI := uI.2.1
  haveI := uI.2.2.1
  haveI := uI.2.2.2.1
  haveI : ∀ v, IsTopologicalGroup (HA (Fv F v) σ J) := fun v => (uV v).1
  haveI : ∀ v, LocallyCompactSpace (HA (Fv F v) σ J) := fun v => (uV v).2.1
  haveI : ∀ v, SecondCountableTopology (HA (Fv F v) σ J) := fun v => (uV v).2.2.1
  haveI : ∀ v, T2Space (HA (Fv F v) σ J) := fun v => (uV v).2.2.2.1
  have LI := local_pack_free σ hσ J hJ (Ainf F) hRI h₀ b laminf hinf.1 minf hminf
  have LV := fun v => local_pack_free σ hσ J hJ (Fv F v) (hRv v) h₀ b (lam v) (hlam v).1 (m v) (hm v)
  obtain ⟨cI, cF, cV, hlat, hint, -, -, -, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b 1 M
  have hprc : Continuous (FactS.pr S : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
    cI.prodMk (continuous_pi fun v => (cV v.1).comp cF)
  have hprm : Measurable (FactS.pr S : (Fin 1 → Fin M → AF F ⊗[F] E) → _) := hprc.measurable
  have hintm : MeasurableSet (intOff b S : Set (Fin 1 → Fin M → AF F ⊗[F] E)) :=
    (hint S).measurableSet
  have actC : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] ,
      (Continuous fun p : HA R σ J × (Fin 1 → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) →
      ∀ h : HA R σ J, Continuous (actW R σ J h : (Fin 1 → Fin M → R ⊗[F] E) → _) :=
    fun R _ _ _ hc h => hc.comp (Continuous.prodMk_right h)
  have cAI := (uI.2.2.2.2.2 1).1
  have cAV := fun v => ((uV v).2.2.2.2.2 1).1
  have cAA := (uA.2.2.2.2.2 1).1
  set P := (I.restrict (intOff b S)).map (FactS.pr S) with hPdef
  haveI hPc : IsFiniteMeasureOnCompacts P := ⟨fun K hK => by
    rw [hPdef, Measure.map_apply hprm hK.isClosed.measurableSet,
      Measure.restrict_apply (hprm hK.isClosed.measurableSet)]
    exact FactS.preimage_lt_top σ hσ b S I K hK⟩
  have hPinv : ∀ (g₀ : HA (Ainf F) σ J) (g : ∀ v : S, HA (Fv F v.1) σ J),
      P.map (fun x => (actW (Ainf F) σ J g₀ x.1, fun v => actW (Fv F v.1) σ J (g v) (x.2 v))) = P := by
    intro g₀ g
    refine FactS.push_inv σ hσ J hJ b S I hIinv (fun v X => ((uV v).2.2.2.2.2 1).2.1 X) hprm
      (fun h => (actC _ cAA h).measurable) hintm g₀ g ?_
    refine Continuous.measurable (Continuous.prodMk ((actC _ cAI g₀).comp continuous_fst)
      (continuous_pi fun v => ?_))
    exact (actC _ (cAV v.1) (g v)).comp ((continuous_apply v).comp continuous_snd)
  have hZ₀ : IsClosed {Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
      gramR (Ainf F) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Ainf F))} :=
    isClosed_eq (kI.2.2.2.2.2.2.2.2.2 1 M J) continuous_const
  have hZ : ∀ v : S, IsClosed {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
      gramR (Fv F v.1) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Fv F v.1))} := fun v =>
    isClosed_eq ((kV v.1).2.2.2.2.2.2.2.2.2 1 M J) continuous_const
  have hU₀ := GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ (Ainf F) hRI 1 M
  have hU : ∀ v : S, IsOpen {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
      LinearIndependent (Fv F v.1 ⊗[F] E) Y} := fun v =>
    GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ (Fv F v.1) (hRv v.1) 1 M
  have hPZ : P (({Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
        gramR (Ainf F) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Ainf F))} ∩
        {Y | LinearIndependent (Ainf F ⊗[F] E) Y}) ×ˢ
      Set.univ.pi fun v : S => {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
        gramR (Fv F v.1) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Fv F v.1))} ∩
        {Y | LinearIndependent (Fv F v.1 ⊗[F] E) Y})ᶜ = 0 := by
    have hms : MeasurableSet (({Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
        gramR (Ainf F) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Ainf F))} ∩
        {Y | LinearIndependent (Ainf F ⊗[F] E) Y}) ×ˢ
      Set.univ.pi fun v : S => {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
        gramR (Fv F v.1) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Fv F v.1))} ∩
        {Y | LinearIndependent (Fv F v.1 ⊗[F] E) Y}) :=
      (hZ₀.measurableSet.inter hU₀.measurableSet).prod
        (MeasurableSet.univ_pi fun v => (hZ v).measurableSet.inter (hU v).measurableSet)
    rw [hPdef, Measure.map_apply hprm hms.compl]
    refine le_antisymm (le_trans (Measure.restrict_apply_le _ _) ?_) bot_le
    refine le_trans (measure_mono ?_) hIT.le
    rintro X hX ⟨hXg, hXi, hXv⟩
    apply hX
    have hg := ((GlobalTheory.T.gram_matrix_local_global F E σ hσ M J hJ 1 X 0).1.mp hXg)
    exact ⟨⟨hg.1, hXi⟩, fun v _ => ⟨hg.2 v.1, hXv v.1⟩⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.restricted_product_haar_measure (ι := S) (G := fun v : S => HA (Fv F v.1) σ J)
    (W := fun v : S => Fin 1 → Fin M → Fv F v.1 ⊗[F] E)
    (actW (Ainf F) σ J) (fun v => actW (Fv F v.1) σ J)
    cAI (uI.2.2.2.2.2 1).2.1 (uI.2.2.2.2.2 1).2.2.1
    (fun v => cAV v.1) (fun v => ((uV v.1).2.2.2.2.2 1).2.1) (fun v => ((uV v.1).2.2.2.2.2 1).2.2.1)
    _ _ hU₀ hU
    (fun g x hx => free_act _ σ J g x hx) (fun v g x hx => free_act _ σ J g x hx)
    _ _ hZ₀ hZ
    (fun g x hx => ((uI.2.2.2.2.2 1).2.2.2 g x).trans hx)
    (fun v g x hx => (((uV v.1).2.2.2.2.2 1).2.2.2 g x).trans hx)
    LI.2.2.2.2 (fun v => (LV v.1).2.2.2.2)
    (minf (hermOf (Ainf F) σ 0 h₀)) (fun v => m v.1 (hermOf (Fv F v.1) σ 0 h₀))
    LI.1 (fun v => (LV v.1).1)
    LI.2.1 (fun v => (LV v.1).2.1) LI.2.2.1 (fun v => (LV v.1).2.2.1)
    LI.2.2.2.1 (fun v => (LV v.1).2.2.2.1) P hPc hPinv hPZ
  refine ⟨c, fun φinf φ hφinf hφ => ?_⟩
  have h := hc φinf (fun v => φ v.1) hφinf (fun v => hφ v.1)
  have hΦ : Measurable fun x : (Fin 1 → Fin M → Ainf F ⊗[F] E) ×
      ∀ v : S, Fin 1 → Fin M → Fv F v.1 ⊗[F] E => φinf x.1 * ∏ v : S, φ v.1 (x.2 v) :=
    (hφinf.comp measurable_fst).mul
      (Finset.measurable_prod _ fun v _ => (hφ v.1).comp ((measurable_pi_apply v).comp measurable_snd))
  rw [hPdef, lintegral_map hΦ hprm, Finset.prod_coe_sort S fun v => ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ 0 h₀))] at h
  rw [← h]
  unfold pureL
  rw [lintegral_indicator hintm]
  refine lintegral_congr fun X => ?_
  simp only [FactS.pr]
  rw [Finset.prod_coe_sort S fun v => φ v (projV v (projFin X))]

end GlobalTheory.CompanionTheory.WeilSiegel.FreeFact
