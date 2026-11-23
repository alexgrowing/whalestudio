import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedDisintegrationCompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartGramFirstEntryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIntegralFormulaHyperbolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDecompositionHomeomorphStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartCompactSupportContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCellOpenIndependentStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero

theorem stages_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → (∀ X, 0 ≤ φ X) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m 0) = ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (φ (chartS R σ J x a 0 Y)) ∂(m' 0) ∂(coordW R b lam 1 n) ∂(m₁ 0) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hLoc n d b lam hlam m m₁ m' hm hm₁ hm' φ hφc hφs hφt hφ0
  have hLoc' := hLoc
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hLoc'
  obtain ⟨_, _, _, _, hsigc, -, -, hbor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := hbor 1 (M + 2)
  haveI := hbor n M
  haveI := hbor 1 n
  haveI := hbor (n + 1) (M + 2)
  obtain ⟨_, _, _, _, hl1⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R 1
  obtain ⟨_, _, _, _, hl3⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R n
  obtain ⟨_, _, _, _, hlN⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R (n + 1)
  have hJ' : IsHermND σ (hypOne J) := isHermND_hypOne σ hJ
  obtain ⟨G₁, hG₁c, hG₁⟩ := hl1 (M + 2) (hypOne J) hJ'
  obtain ⟨G₃, hG₃c, hG₃⟩ := hl3 M J hJ
  obtain ⟨G, hGc, hG⟩ := hlN (M + 2) (hypOne J) hJ'
  obtain ⟨e, he, hep⟩ := GlobalTheory.T.hermitian_block_decomposition_homeomorph F E σ hσ M J hJ R hLoc n d b lam hlam
  obtain ⟨hψc, hψs, hψt⟩ := GlobalTheory.T.chart_compact_support_continuous F E σ hσ M J hJ R hLoc n φ hφc hφs hφt
  obtain ⟨-, hcellF, -, -, -⟩ := GlobalTheory.T.free_cell_open_independent F E σ hσ M J hJ R hLoc n
  obtain ⟨-, hWh, hHh⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam
  haveI := hWh 1 (M + 2)
  haveI := hWh n M
  haveI := hWh 1 n
  haveI := hHh 1
  haveI := hHh n
  have hU1 : IsOpen {X : Fin 1 → Fin (M + 2) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    GlobalTheory.T.linearly_independent_frames_open F E σ hσ R hLoc 1 (M + 2)
  have hU3 : IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    GlobalTheory.T.linearly_independent_frames_open F E σ hσ R hLoc n M
  have hWo : IsOpen {X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    GlobalTheory.T.linearly_independent_frames_open F E σ hσ R hLoc (n + 1) (M + 2)
  have li1 : ∀ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, IsUnit (x 0 0) → LinearIndependent (R ⊗[F] E) x := by
    intro x hx
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 := congrFun hg 0
    simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hx.mul_left_eq_zero.1 h0
  let Q : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) → HermR R σ n :=
    fun p => qH R σ (sig_invol σ hσ) p.1 p.2.1 p.2.2
  have hQc : Continuous Q := by
    refine Topology.IsEmbedding.subtypeVal.continuous_iff.2 (continuous_matrix fun i j => ?_)
    have ca : ∀ i, Continuous fun p : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        p.2.2 0 i := fun i =>
      (continuous_apply i).comp ((continuous_apply 0).comp (continuous_snd.comp continuous_snd))
    have cs : ∀ i, Continuous fun p : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        p.2.1 0 i := fun i =>
      (continuous_apply i).comp ((continuous_apply 0).comp (continuous_fst.comp continuous_snd))
    have ct : Continuous fun p : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        (p.1 : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
      (continuous_fst.subtype_val).matrix_elem 0 0
    exact ((((hsigc.comp (ca i)).mul (cs j)).add ((hsigc.comp (cs i)).mul (ca j))).sub
      (ct.mul ((hsigc.comp (ca i)).mul (ca j))))
  let ψ : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
      (Fin n → Fin M → R ⊗[F] E) → ℝ := fun p => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)
  obtain ⟨hLc, hL⟩ := GlobalTheory.T.staged_disintegration_composition (Fin 1 → Fin (M + 2) → R ⊗[F] E) (Fin n → Fin M → R ⊗[F] E)
    (HermR R σ 1) (HermR R σ n) (Fin 1 → Fin n → R ⊗[F] E) (Fin 1 → Fin n → R ⊗[F] E)
    (Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) (Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (coordW R b lam 1 (M + 2)) (coordW R b lam n M) (coordHerm R σ b lam 1) (coordHerm R σ b lam n)
    (coordW R b lam 1 n) (coordW R b lam 1 n)
    (gramR R σ (hypOne J)) Subtype.val G₁ {X | LinearIndependent (R ⊗[F] E) X} m₁
    (gramR R σ J) Subtype.val G₃ {X | LinearIndependent (R ⊗[F] E) X} m' Q hU1 hU3 hG₁c hG₃c
    Subtype.val_injective Subtype.val_injective hG₁ hG₃ hm₁ hm' hQc ψ hψc hψs
    (fun p hp => ⟨li1 _ (hψt p hp).1, (hψt p hp).2⟩) (fun p => hφ0 _)
  have key : ∀ (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E)
      (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) →
      e (G (chartS R σ J x a s Y)) = (G₁ x, s, G₃ Y + Q (G₁ x, s, a)) := by
    intro x a s Y hx
    obtain ⟨g1, g2, g3⟩ := GlobalTheory.T.chart_gram_first_entry F E σ hσ M J hJ R n x a s Y hx
    obtain ⟨e1, e2, e3⟩ := he (G (chartS R σ J x a s Y))
    rw [← hG] at e1 e2 e3
    have ht : ((G₁ x : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = hR R σ (hypOne J) (x 0) (x 0) := by
      rw [← hG₁]; rfl
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · refine Subtype.ext (Matrix.ext fun i j => ?_)
      obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact e1.trans (g1.trans ht.symm)
    · funext i j
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact (e2 j).trans (g2 j)
    · refine Subtype.ext (Matrix.ext fun i j => ?_)
      refine (e3 i j).trans ((g3 i j).trans ?_)
      show _ = ((G₃ Y : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j +
        (sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j -
          ((G₁ x : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 * (sigR R σ (a 0 i) * a 0 j))
      rw [← hG₃, ht]
  have hφm : Measurable fun X => ENNReal.ofReal (φ X) :=
    ENNReal.measurable_ofReal.comp hφc.measurable
  have hφz : ∀ X, X ∉ freeCell (R ⊗[F] E) M n → φ X = 0 := fun X hX =>
    image_eq_zero_of_notMem_tsupport fun h => hX (hφt h)
  have hmF : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 2)) (gramR R σ (hypOne J))
      Subtype.val {X | LinearIndependent (R ⊗[F] E) X} (coordHerm R σ b lam (n + 1)) Set.univ m := hm
  obtain ⟨hint, hcont⟩ := hmF.2.2 φ hφc hφs (hφt.trans fun X hX => hcellF X hX)
  have hD : ∀ B, ∫⁻ X, ENNReal.ofReal (φ X) ∂(m B) = ENNReal.ofReal (∫ X, φ X ∂(m B)) := fun B =>
    (ofReal_integral_eq_lintegral_ofReal (hint B trivial) (Filter.Eventually.of_forall hφ0)).symm
  have hDc : Continuous fun z : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n =>
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (e.symm z)) := by
    simp only [hD]
    exact ENNReal.continuous_ofReal.comp ((continuousOn_univ.1 hcont).comp e.symm.continuous)
  have hcmp : ∀ S : Set (HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n), IsCompact S →
      ∫⁻ z in S, ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (e.symm z))
        ∂((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) =
      ∫⁻ z in S, (∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y))
          ∂(m' (z.2.2 - Q (z.1, z.2.1, a))) ∂(coordW R b lam 1 n) ∂(m₁ z.1))
        ∂((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) := by
    intro S hS
    have hSm : MeasurableSet S := hS.measurableSet
    have hfm : Measurable (S.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hSm
    have h1 := hL _ hfm
    have h2 : ∀ L : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞,
        (fun z => S.indicator (fun _ => (1 : ℝ≥0∞)) z * L z) = S.indicator L := by
      intro L
      funext z
      by_cases hz : z ∈ S <;> simp [hz]
    rw [h2, lintegral_indicator hSm] at h1
    rw [← h1, ← hep.setLIntegral_comp_preimage_emb e.measurableEmbedding _ S]
    simp only [Homeomorph.symm_apply_apply]
    have hGm := e.continuous.measurable hSm
    rw [← GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage Subtype.val_injective hGc hG hWo subset_rfl hm _ hφm
      (fun X hX => ?_) _ hGm]
    · have hgm : Measurable ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) :=
        hφm.indicator (hGc.measurable hGm)
      have hg0 : ∀ X, X ∉ freeCell (R ⊗[F] E) M n →
          ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) X = 0 := by
        intro X hX
        exact Set.indicator_apply_eq_zero.2 fun _ => by rw [hφz X hX, ENNReal.ofReal_zero]
      have h3 : ∫⁻ v in {X | LinearIndependent (R ⊗[F] E) X},
            ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) v ∂(coordW R b lam (n + 1) (M + 2)) =
          ∫⁻ v, ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) v
            ∂(coordW R b lam (n + 1) (M + 2)) := by
        rw [← lintegral_indicator hWo.measurableSet]
        refine lintegral_congr fun v => ?_
        by_cases hv : v ∈ {X | LinearIndependent (R ⊗[F] E) X}
        · rw [Set.indicator_of_mem hv]
        · rw [Set.indicator_of_notMem hv]
          exact (hg0 v fun hc => hv (hcellF v hc)).symm
      rw [h3, GlobalTheory.T.chart_integral_formula_hyperbolic F E σ hσ M J hJ R hLoc n d b lam hlam _ hgm
        (fun X hX => hg0 X fun hc => hX hc.1)]
      refine lintegral_congr fun x => lintegral_congr fun a => lintegral_congr fun s =>
        lintegral_congr fun Y => ?_
      by_cases hx : IsUnit (x 0 0)
      · have hk := key x a s Y hx
        by_cases hz : (G₁ x, s, G₃ Y + Q (G₁ x, s, a)) ∈ S
        · have hm1 : chartS R σ J x a s Y ∈ G ⁻¹' (e ⁻¹' S) := by
            simpa only [Set.mem_preimage, hk] using hz
          rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hz]
          simp [ψ]
        · have hm1 : chartS R σ J x a s Y ∉ G ⁻¹' (e ⁻¹' S) := by
            simpa only [Set.mem_preimage, hk] using hz
          rw [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hz]
          simp
      · have hp : ψ (x, a, s, Y) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hx (hψt _ h).1
        have hp' : φ (chartS R σ J x a s Y) = 0 := hp
        rw [hp, ENNReal.ofReal_zero, zero_mul]
        exact Set.indicator_apply_eq_zero.2 fun _ => by rw [hp', ENNReal.ofReal_zero]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hX (hcellF X (hφt h)), ENNReal.ofReal_zero]
  have hfin := GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts _ ((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n)))
    Set.univ isOpen_univ _ _ hDc.continuousOn hLc.continuousOn (fun S hS _ => hcmp S hS) 0 trivial
  have he0 : e 0 = 0 := by
    obtain ⟨e1, e2, e3⟩ := he 0
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · refine Subtype.ext (Matrix.ext fun i j => ?_)
      obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact e1
    · funext i j
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact e2 j
    · exact Subtype.ext (Matrix.ext fun i j => e3 i j)
  have hes : e.symm 0 = 0 := by rw [← he0, e.symm_apply_apply]
  have hQ0 : ∀ a, Q (0, 0, a) = 0 := by
    intro a
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    show sigR R σ (a 0 i) * 0 + sigR R σ 0 * a 0 j - 0 * (sigR R σ (a 0 i) * a 0 j) = 0
    simp
  simp only [hes, Prod.fst_zero, Prod.snd_zero, hQ0, sub_zero] at hfin
  exact hfin

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero
