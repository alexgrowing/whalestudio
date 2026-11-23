import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOrderDataExistAtPlaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSetContainedInLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeVolumeOrderDataStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeGaussSumEstimateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeQuadraticIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeCharacterIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderConjugationStableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalScalingVolumeByUnitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderStableIntegralStructureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalScalingMeasureByUnitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundByRecursionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedVolumeStatement

noncomputable section

section Pieces

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

theorem GlobalTheory.CompanionTheory.AvgFree.scale_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → ∀ (s : (Fv F v ⊗[F] E)ˣ) (θ : ℝ≥0), (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (s : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ (D : Set (Fin n → Fin M → (Fv F v ⊗[F] E))) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet D → MeasurableSet Y → ∃ Y' : Set (HermR (Fv F v) σ n), MeasurableSet Y' ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y' = ((θ : ℝ≥0∞) ^ n)⁻¹ * (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y ∧ (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) ({X | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l a * dMat (Fv F v) l ((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : (Fv F v ⊗[F] E))) ∈ D} ∩ gramIn (Fv F v) σ J Y) ≤ (θ : ℝ≥0∞) ^ M * (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (D ∩ gramIn (Fv F v) σ J Y') := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv O hOc hOo hOs n M J l a ha hal s θ hmod D Y hD hY
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI := hlv.1
  obtain ⟨hKH, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hKH
  haveI := hW n M
  have hinv : ∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
    have h : ∀ e, σ (σ e) = e := by
      intro e
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      apply τ.injective
      rw [hσ.2.2.2 τ, hσ.2.2.2 τ]
      simp
    exact sigR_sigR _ σ h
  have hnc : ∀ i, negCol (Fv F v) l a i ∈ O := by
    intro i
    unfold negCol
    split_ifs
    · exact O.one_mem
    · exact O.neg_mem (ha i)
  have hncl : negCol (Fv F v) l a l = 1 := by simp [negCol]
  obtain ⟨hY1m, hY1⟩ := GlobalTheory.T.local_order_stable_integral_structure F E σ hσ d b v lv hlv O hOc hOo hOs n l _ hnc hncl Y hY
  obtain ⟨hY2m, hY2⟩ := GlobalTheory.T.local_scaling_measure_by_unit F E σ hσ d b v lv hlv s θ hmod n l _ hY1m
  refine ⟨_, hY2m, by rw [hY2, hY1], ?_⟩
  have hθ : θ ≠ 0 := by
    rintro rfl
    have h := hmod Set.univ
    have hs : (fun x => (s : Fv F v ⊗[F] E) * x) '' Set.univ = Set.univ :=
      Set.image_univ_of_surjective fun y => ⟨((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * y, by simp⟩
    rw [hs] at h
    simp only [ENNReal.coe_zero, zero_mul] at h
    exact (Measure.measure_univ_pos.2 (NeZero.ne _)).ne' h
  have hmod' : ∀ Y : Set (Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv
      ((fun x => ((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) '' Y) =
      (θ⁻¹ : ℝ≥0) * GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv Y := by
    intro Y
    have h := hmod ((fun x => ((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) '' Y)
    have h2 : (fun x => (s : Fv F v ⊗[F] E) * x) ''
        ((fun x => ((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) '' Y) = Y := by
      rw [Set.image_image]
      simp
    rw [h2] at h
    rw [h, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hθ]
    simp
  have hrc : ∀ g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
      Continuous fun X : Fin n → Fin M → Fv F v ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X g := by
    intro g
    refine continuous_pi fun a => continuous_pi fun i => ?_
    unfold GlobalTheory.CompanionTheory.SW.rmul
    exact continuous_finset_sum _ fun c _ =>
      (continuous_apply_apply c i).mul continuous_const
  have hgm : ∀ Y' : Set (HermR (Fv F v) σ n), MeasurableSet Y' →
      MeasurableSet (gramIn (Fv F v) σ J (n := n) Y') := by
    intro Y' hY'
    haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : BorelSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := inferInstanceAs (BorelSpace (Fin n → Fin n → Fv F v ⊗[F] E))
    have h1 : gramIn (Fv F v) σ J (n := n) Y' = gramR (Fv F v) σ J ⁻¹' (Subtype.val '' Y') := by
      ext X
      simp only [gramIn, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
      exact ⟨fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩, fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩⟩
    rw [h1]
    haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
    have hbs := (Subtype.borelSpace (α := Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
      ((HermR (Fv F v) σ n : AddSubgroup _) : Set _)).measurable_eq
    have hY3 : @MeasurableSet {x // x ∈ ((HermR (Fv F v) σ n : AddSubgroup _) : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))} Subtype.instMeasurableSpace Y' := by
      rw [hbs]
      exact hY'
    exact (a10 n M J).measurable ((a9 n).isClosedEmbedding_subtypeVal.measurableEmbedding.measurableSet_image.2 hY3)
  have hD2 := hD.inter (hgm _ hY2m)
  have hwe := GlobalTheory.T.local_order_conjugation_stable F E σ hσ d b v lv hlv O hOc hOo hOs n M l a ha hal
  have hwd := GlobalTheory.T.local_scaling_volume_by_unit F E σ hσ d b v lv hlv s⁻¹ θ⁻¹ hmod' n M l _ hD2
  have hm2 : MeasurableSet {Z | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) Z (dMat (Fv F v) l ((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)) ∈
      D ∩ gramIn (Fv F v) σ J (cjPre (Fv F v) σ (dMat (Fv F v) l (s : Fv F v ⊗[F] E))
        (cjPre (Fv F v) σ (eMat (Fv F v) l (negCol (Fv F v) l a)) Y))} :=
    (hrc _).measurable hD2
  have hsub : {X | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l a *
        dMat (Fv F v) l ((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)) ∈ D} ∩ gramIn (Fv F v) σ J Y ⊆
      (fun X => GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l a)) ⁻¹'
        {Z | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) Z (dMat (Fv F v) l ((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)) ∈
          D ∩ gramIn (Fv F v) σ J (cjPre (Fv F v) σ (dMat (Fv F v) l (s : Fv F v ⊗[F] E))
            (cjPre (Fv F v) σ (eMat (Fv F v) l (negCol (Fv F v) l a)) Y))} := by
    rintro X ⟨hXD, y, hy, hXy⟩
    have h1 := rmul_mul (Fv F v) X (eMat (Fv F v) l a)
      (dMat (Fv F v) l ((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E))
    refine ⟨by simp only [Set.mem_preimage]; rw [h1]; exact hXD, ?_⟩
    let z : HermR (Fv F v) σ n := ⟨cjM (Fv F v) σ (eMat (Fv F v) l a) y, cjM_mem _ σ hinv _ _ y.2⟩
    let w : HermR (Fv F v) σ n := ⟨cjM (Fv F v) σ (dMat (Fv F v) l ((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)) z,
      cjM_mem _ σ hinv _ _ z.2⟩
    refine ⟨w, ⟨z, ⟨y, hy, ?_⟩, ?_⟩, ?_⟩
    · show cjM (Fv F v) σ _ (cjM (Fv F v) σ _ _) = _
      rw [← cjM_mul, eMat_mul_negCol _ _ _ hal, cjM_one]
    · show cjM (Fv F v) σ _ (cjM (Fv F v) σ _ _) = _
      rw [← cjM_mul, dMat_mul _ _ _ _ (by simp), cjM_one]
    · show gramR _ σ J _ = cjM (Fv F v) σ _ (cjM (Fv F v) σ _ _)
      rw [gramR_rmul, gramR_rmul, hXy]
  calc _ ≤ _ := measure_mono hsub
    _ = _ := hwe.measure_preimage hm2.nullMeasurableSet
    _ = _ := hwd
    _ = _ := by
      congr 1
      rw [ENNReal.coe_inv hθ, ENNReal.inv_pow, inv_inv]

theorem GlobalTheory.CompanionTheory.AvgFree.bad_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ), 0 < n → 2 * n < M → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∃ (ι : Type) (I : ℕ → Finset ι) (α β : ℕ → ι → ℝ≥0) (ρ : ℕ → ℝ≥0), Filter.Tendsto ρ Filter.atTop (nhds 0) ∧ (∀ j, ∑ i ∈ I j, α j i * β j i ≤ ρ j ∧ ∑ i ∈ I j, α j i ≤ ρ j) ∧ ∀ (j : ℕ) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y → ∃ Z : ι → Set (HermR (Fv F v) σ n), (∀ i ∈ I j, MeasurableSet (Z i) ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (Z i) = β j i * (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y) ∧ (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (((tupIn (M := M) (n := n) (Fv F v) (L : Set (Fv F v ⊗[F] E))) \ (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j)) ∩ gramIn (Fv F v) σ J Y) ≤ ∑ i ∈ I j, (α j i : ℝ≥0∞) * (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) ((tupIn (M := M) (n := n) (Fv F v) (L : Set (Fv F v ⊗[F] E))) ∩ gramIn (Fv F v) σ J (Z i)) := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv M J n hn hM O S hOS L hLc hLo
  classical
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI := hlv.1
  obtain ⟨hKH, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hKH
  haveI := hW n M
  obtain ⟨hOc, hOo, hOs, hp, -⟩ := id hOS
  have hθ : ∀ p : (Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E), ∃ θ : ℝ≥0, p ∈ S → θ < 1 ∧ 0 < θ ∧
      ∀ Y : Set (Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv ((fun x => (p.1 : Fv F v ⊗[F] E) * x) '' Y) =
        θ * GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv Y := by
    intro p
    by_cases h : p ∈ S
    · obtain ⟨θ, h1, h2⟩ := (hp p h).2.2.2.2
      refine ⟨θ, fun _ => ⟨h1, ?_, h2⟩⟩
      rw [pos_iff_ne_zero]
      rintro rfl
      have h3 := h2 Set.univ
      have hs : (fun x => (p.1 : Fv F v ⊗[F] E) * x) '' Set.univ = Set.univ :=
        Set.image_univ_of_surjective fun y => ⟨((p.1⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * y, by simp⟩
      rw [hs] at h3
      simp only [ENNReal.coe_zero, zero_mul] at h3
      exact (Measure.measure_univ_pos.2 (NeZero.ne _)).ne' h3
    · exact ⟨0, fun h' => absurd h' h⟩
  choose θ hθ using hθ
  have hG := fun (j : ℕ) (p : (Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E)) =>
    (show ∃ G : Finset (Fin n × (Fin n → Fv F v ⊗[F] E)), p ∈ S → (((G.card : ℝ≥0) ≤ n * ((θ p)⁻¹) ^ (j * n)) ∧
        (∀ q ∈ G, (∀ i, q.2 i ∈ O) ∧ q.2 q.1 = 1) ∧
        ∀ X ∈ nearNF (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) (p.1 : Fv F v ⊗[F] E) j,
          ∃ q ∈ G, GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) q.1 q.2 * dMat (Fv F v) q.1 ((p.1 ^ j)⁻¹ : (Fv F v ⊗[F] E)ˣ)) ∈
            tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E))) by
      by_cases h : p ∈ S
      · obtain ⟨G, hG⟩ := GlobalTheory.T.local_lattice_character_integral F E σ hσ d b v lv hlv O S hOS L hLc hLo n M hn p h (θ p) (hθ p h).2.2 j
        exact ⟨G, fun _ => hG⟩
      · exact ⟨∅, fun h' => absurd h' h⟩)
  choose G hG using hG
  have hpow : ∀ p ∈ S, ∀ (j : ℕ) (Y : Set (Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv
      ((fun x => ((p.1 ^ j : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) '' Y) =
      ((θ p ^ j : ℝ≥0) : ℝ≥0∞) * GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv Y := by
    intro p hpS j
    induction j with
    | zero => intro Y; simp
    | succ j ih =>
      intro Y
      have h1 : (fun x => ((p.1 ^ (j + 1) : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) '' Y =
          (fun x => ((p.1 ^ j : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) ''
            ((fun x => (p.1 : Fv F v ⊗[F] E) * x) '' Y) := by
        rw [Set.image_image]
        refine Set.image_congr fun x _ => ?_
        simp [pow_succ, mul_assoc]
      rw [h1, ih, (hθ p hpS).2.2 Y, ← mul_assoc, ← ENNReal.coe_mul, pow_succ]
  refine ⟨Σ _ : (Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E), Fin n × (Fin n → Fv F v ⊗[F] E),
    fun j => S.sigma fun p => G j p, fun j i => (θ i.1 ^ j) ^ M, fun j i => ((θ i.1 ^ j) ^ n)⁻¹,
    fun j => ∑ p ∈ S, (n : ℝ≥0) * (θ p ^ (M - 2 * n)) ^ j, ?_, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun j : ℕ => ∑ p ∈ S, (n : ℝ≥0) * (θ p ^ (M - 2 * n)) ^ j) Filter.atTop
        (nhds (∑ p ∈ S, (n : ℝ≥0) * 0)) :=
      tendsto_finset_sum _ fun p hpS => tendsto_const_nhds.mul
        (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (pow_lt_one₀ zero_le' (hθ p hpS).1 (by omega)))
    simpa using h1
  · intro j
    rw [Finset.sum_sigma, Finset.sum_sigma]
    have key : ∀ p ∈ S, (n : ℝ≥0) * ((θ p)⁻¹) ^ (j * n) * ((θ p ^ j) ^ M * ((θ p ^ j) ^ n)⁻¹) =
        (n : ℝ≥0) * (θ p ^ (M - 2 * n)) ^ j ∧
        (n : ℝ≥0) * ((θ p)⁻¹) ^ (j * n) * (θ p ^ j) ^ M ≤ (n : ℝ≥0) * (θ p ^ (M - 2 * n)) ^ j := by
      intro p hpS
      have h0 : θ p ≠ 0 := (hθ p hpS).2.1.ne'
      set u := θ p ^ j with hu
      have hu0 : u ≠ 0 := pow_ne_zero _ h0
      have hu1 : u ≤ 1 := pow_le_one₀ zero_le' (hθ p hpS).1.le
      have e1 : ((θ p)⁻¹) ^ (j * n) = (u ^ n)⁻¹ := by
        rw [inv_pow, pow_mul]
      have e2 : (θ p ^ (M - 2 * n)) ^ j = u ^ (M - 2 * n) := by
        rw [hu, ← pow_mul, ← pow_mul, mul_comm]
      have e3 : u ^ M = u ^ (M - 2 * n) * u ^ n * u ^ n := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      have hn0 : u ^ n ≠ 0 := pow_ne_zero _ hu0
      rw [e1, e2, e3]
      constructor
      · field_simp
      · have h1 : (n : ℝ≥0) * (u ^ n)⁻¹ * (u ^ (M - 2 * n) * u ^ n * u ^ n) =
            (n : ℝ≥0) * u ^ (M - 2 * n) * u ^ n := by
          field_simp
        rw [h1]
        exact mul_le_of_le_one_right zero_le' (pow_le_one₀ zero_le' hu1)
    constructor
    · refine Finset.sum_le_sum fun p hpS => ?_
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← (key p hpS).1]
      gcongr
      exact (hG j p hpS).1
    · refine Finset.sum_le_sum fun p hpS => ?_
      simp only [Finset.sum_const, nsmul_eq_mul]
      refine le_trans ?_ (key p hpS).2
      gcongr
      exact (hG j p hpS).1
  · intro j Y hY
    have hBm : MeasurableSet (tupIn (M := M) (n := n) (Fv F v) (L : Set (Fv F v ⊗[F] E))) :=
      (isCompact_tupIn _ hLc).measurableSet
    have hZ := fun i : (Σ _ : (Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E), Fin n × (Fin n → Fv F v ⊗[F] E)) =>
      (show ∃ Z : Set (HermR (Fv F v) σ n), i ∈ (S.sigma fun p => G j p) → MeasurableSet Z ∧
          GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n Z =
            (((θ i.1 ^ j) ^ n)⁻¹ : ℝ≥0) * GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n Y ∧
          GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M
            ({X | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) i.2.1 i.2.2 *
                dMat (Fv F v) i.2.1 ((i.1.1 ^ j)⁻¹ : (Fv F v ⊗[F] E)ˣ)) ∈
              tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E))} ∩ gramIn (Fv F v) σ J Y) ≤
            (((θ i.1 ^ j) ^ M : ℝ≥0) : ℝ≥0∞) * GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M
              (tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) ∩ gramIn (Fv F v) σ J Z) by
        by_cases h : i ∈ (S.sigma fun p => G j p)
        · have h1 := Finset.mem_sigma.1 h
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := GlobalTheory.CompanionTheory.AvgFree.scale_density F E σ hσ d b v lv hlv O hOc hOo hOs n M J i.2.1 i.2.2
            ((hG j i.1 h1.1).2.1 i.2 h1.2).1 ((hG j i.1 h1.1).2.1 i.2 h1.2).2 (i.1.1 ^ j) (θ i.1 ^ j)
            (hpow i.1 h1.1 j) _ Y hBm hY
          refine ⟨Z, fun _ => ⟨hZ1, ?_, ?_⟩⟩
          · have h0 : (θ i.1 ^ j) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (hθ i.1 h1.1).2.1.ne')
            rw [hZ2, ENNReal.coe_inv h0]
            push_cast
            rfl
          · simpa using hZ3
        · exact ⟨∅, fun h' => absurd h' h⟩)
    choose Z hZ using hZ
    refine ⟨Z, fun i hi => ⟨(hZ i hi).1, (hZ i hi).2.1⟩, ?_⟩
    have hsub : (tupIn (M := M) (n := n) (Fv F v) (L : Set (Fv F v ⊗[F] E)) \
        goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ∩
          gramIn (Fv F v) σ J Y ⊆
        ⋃ i ∈ (S.sigma fun p => G j p), ({X | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) i.2.1 i.2.2 *
                dMat (Fv F v) i.2.1 ((i.1.1 ^ j)⁻¹ : (Fv F v ⊗[F] E)ˣ)) ∈
              tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E))} ∩ gramIn (Fv F v) σ J Y) := by
      rintro X ⟨⟨hX1, hX2⟩, hX3⟩
      have h1 : ∃ p ∈ S, X ∈ nearNF (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E))
          (L : Set (Fv F v ⊗[F] E)) (p.1 : Fv F v ⊗[F] E) j := by
        by_contra hcon
        push_neg at hcon
        refine hX2 ⟨hX1, ?_⟩
        simp only [Set.mem_iUnion, not_exists]
        exact fun p hpS => hcon p hpS
      obtain ⟨p, hpS, hXp⟩ := h1
      obtain ⟨q, hq, hXq⟩ := (hG j p hpS).2.2 X hXp
      exact Set.mem_biUnion (x := (⟨p, q⟩ : Σ _ : (Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E), Fin n × (Fin n → Fv F v ⊗[F] E)))
        (Finset.mem_coe.2 (Finset.mem_sigma.2 ⟨hpS, hq⟩)) ⟨hXq, hX3⟩
    exact le_trans (measure_mono hsub) (le_trans (measure_biUnion_finset_le _ _)
      (Finset.sum_le_sum fun i hi => (hZ i hi).2.2))

theorem GlobalTheory.CompanionTheory.AvgFree.exhaust_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ A : Set (Fin n → Fin M → (Fv F v ⊗[F] E)), IsCompact A → IsOpen A → ∃ Tt : ℕ → Set (Fin n → Fin M → (Fv F v ⊗[F] E)), Monotone Tt ∧ (∀ j, IsCompact (Tt j) ∧ IsOpen (Tt j) ∧ Tt j ⊆ A ∧ Tt j ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X}) ∧ A ∩ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ (⋃ j, Tt j) ∧ ∃ ε : ℕ → ℝ≥0, Filter.Tendsto ε Filter.atTop (nhds 0) ∧ ∀ (j : ℕ) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) ((A \ Tt j) ∩ gramIn (Fv F v) σ J Y) ≤ ε j * (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv M J hJ n hn hM mv hmv A hAc hAo
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI := hlv.1
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW n M
  obtain ⟨O, S, hOS⟩ := GlobalTheory.T.integral_order_data_exist_at_place F E σ hσ d b v lv hlv
  obtain ⟨L, hLc, hLo, hAL⟩ := GlobalTheory.T.compact_set_contained_in_lattice F E σ hσ v O hOS.1 hOS.2.1 n M A hAc
  obtain ⟨ι, I, α, β, ρ, hρ, hs, hstep⟩ := GlobalTheory.CompanionTheory.AvgFree.bad_density F E σ hσ d b v lv hlv M J n hn hM O S hOS L hLc hLo
  have hcl := GlobalTheory.T.local_lattice_volume_order_data F E σ hσ d b v lv hlv O S hOS L hLc hLo n M
  obtain ⟨hmono, hfree⟩ := GlobalTheory.T.local_lattice_gauss_sum_estimate F E σ hσ d b v lv hlv O S hOS L hLc hLo n M
  have hex := GlobalTheory.T.local_lattice_quadratic_integral F E σ hσ d b v lv hlv O S hOS L hLc hLo n M
  have hBc : IsCompact (tupIn (M := M) (n := n) (Fv F v) (L : Set (Fv F v ⊗[F] E))) := by
    have : tupIn (M := M) (n := n) (Fv F v) (L : Set (Fv F v ⊗[F] E)) =
        Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (L : Set (Fv F v ⊗[F] E)) := by
      ext X
      simp [tupIn]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hLc
  have hj : ∀ᶠ j in Filter.atTop, ρ j < 1 := hρ.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨j₀, hj₀⟩ := hj.exists
  obtain ⟨hmass, -, -, C₀, hC₀⟩ := GlobalTheory.T.local_fibre_measure_unramified_formula F E σ hσ d b v lv hlv M J hJ n mv hmv _ (hcl j₀).1 (hcl j₀).2 (hfree j₀)
  obtain ⟨C, hC⟩ := GlobalTheory.T.density_bound_by_recursion (HermR (Fv F v) σ n) ι (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n)
    (fun Y => GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M
      (tupIn (M := M) (n := n) (Fv F v) (L : Set (Fv F v ⊗[F] E)) ∩ gramIn (Fv F v) σ J Y))
    (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (tupIn (M := M) (n := n) (Fv F v) (L : Set (Fv F v ⊗[F] E))))
    hBc.measure_lt_top.ne (fun Y _ => measure_mono Set.inter_subset_left) (I j₀) (α j₀) (β j₀) C₀
    (fun Y hY => by
      obtain ⟨Z, hZ, hle⟩ := hstep j₀ Y hY
      refine ⟨Z, hZ, ?_⟩
      have h0 : GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M
          (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j₀ ∩
            gramIn (Fv F v) σ J Y) ≤ C₀ * GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n Y := by
        rw [hmass Y hY]
        calc _ ≤ ∫⁻ _ in Y, (C₀ : ℝ≥0∞) ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) :=
              lintegral_mono fun y => hC₀ y
          _ = _ := by rw [setLIntegral_const]
      refine le_trans (measure_mono ?_) (le_trans (measure_union_le _ _) (add_le_add h0 hle))
      rintro X ⟨hX1, hX2⟩
      by_cases hg : X ∈ goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j₀
      · exact Or.inl ⟨hg, hX2⟩
      · exact Or.inr ⟨⟨hX1, hg⟩, hX2⟩)
    (lt_of_le_of_lt (hs j₀).1 hj₀) (lt_of_le_of_lt (hs j₀).2 hj₀)
  refine ⟨fun j => A ∩ goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j,
    fun i j hij => Set.inter_subset_inter_right _ (hmono hij),
    fun j => ⟨hAc.inter_right (hcl j).1.isClosed, hAo.inter (hcl j).2, Set.inter_subset_left,
      Set.inter_subset_right.trans (hfree j)⟩, ?_, fun j => C * ρ j, ?_, ?_⟩
  · rintro X ⟨hXA, hXf⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hex ⟨hAL hXA, hXf⟩)
    exact Set.mem_iUnion.2 ⟨j, hXA, hj⟩
  · simpa using (tendsto_const_nhds (x := C)).mul hρ
  · intro j Y hY
    obtain ⟨Z, hZ, hle⟩ := hstep j Y hY
    have hsub : (A \ (A ∩ goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j)) ∩
        gramIn (Fv F v) σ J Y ⊆
        (tupIn (M := M) (n := n) (Fv F v) (L : Set (Fv F v ⊗[F] E)) \
          goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ∩
        gramIn (Fv F v) σ J Y := by
      rintro X ⟨⟨hXA, hXn⟩, hXg⟩
      exact ⟨⟨hAL hXA, fun h => hXn ⟨hXA, h⟩⟩, hXg⟩
    refine le_trans (measure_mono hsub) (le_trans hle ?_)
    have h1 : ∀ i ∈ I j, (α j i : ℝ≥0∞) * GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M
        (tupIn (M := M) (n := n) (Fv F v) (L : Set (Fv F v ⊗[F] E)) ∩ gramIn (Fv F v) σ J (Z i)) ≤
        (C : ℝ≥0∞) * ((α j i * β j i : ℝ≥0) : ℝ≥0∞) * GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n Y := by
      intro i hi
      have h2 := hC (Z i) (hZ i hi).1
      rw [(hZ i hi).2] at h2
      calc _ ≤ (α j i : ℝ≥0∞) * ((C : ℝ≥0∞) * ((β j i : ℝ≥0∞) * GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n Y)) := by gcongr
        _ = _ := by push_cast; ring
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← ENNReal.coe_finset_sum]
    have h3 : ((∑ i ∈ I j, α j i * β j i : ℝ≥0) : ℝ≥0∞) ≤ (ρ j : ℝ≥0∞) := by exact_mod_cast (hs j).1
    push_cast
    push_cast at h3
    gcongr

end Pieces

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.AvgFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.CompanionTheory.AvgFree.avgFree_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ (c : HermR (Fv F v) σ n) (A : Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsCompact A → IsOpen A → MeasurableSet A ∧ mv c A ≠ ⊤ ∧ ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : HermR (Fv F v) σ n) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets → (∀ k, MeasurableSet (A ∩ gramNear (Fv F v) σ J c (U k)) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ gramNear (Fv F v) σ J c (U k)) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ gramNear (Fv F v) σ J c (U k))).toReal / (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  intro F E _ _ _ _ _ σ hσ M J hJ n hn hM d b v lv hlv mv hmv c A hAc hAo
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a8 n M
  obtain ⟨Tt, h1, h2, h3, ε, h4, h5⟩ := GlobalTheory.CompanionTheory.AvgFree.exhaust_density F E σ hσ d b v lv hlv M J hJ n hn hM mv hmv A hAc hAo
  exact ⟨hAo.measurableSet, GlobalTheory.T.local_fibre_measure_unramified_volume F E σ hσ d b v lv hlv M J hJ n mv hmv c A hAc hAo Tt h1 h2 h3 ε h4 h5⟩
