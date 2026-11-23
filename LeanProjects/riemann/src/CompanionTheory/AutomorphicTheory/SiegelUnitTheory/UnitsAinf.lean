import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueNonnegative
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasures
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsIsCharAF
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualAdelicMeasures
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureRankOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosureProperties
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasures
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresScaling
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuity
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainExistsUnitary
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarMeasureNonunitsNull
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContinuousDiag
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsFibreFamilyLength
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsUnitOfTmulOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FinprodEqIndicator

namespace CompanionTheory.HU

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct NNReal ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem loc (hcm : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R)
    (hnull : ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
      ν {c | ¬ IsUnit c} = 0 ∧ μ {X | ¬ IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0))} = 0)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hm : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m) (a c : ℝ≥0) (ha : a ≠ 0) (hc : c ≠ 0) :
    (∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (a • coordW R b lam 1 M)
      (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0)) id Set.univ (c • lam) {x | IsUnit x} fib) ∧
    ∀ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (a • coordW R b lam 1 M)
      (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0)) id Set.univ (c • lam) {x | IsUnit x} fib →
      ∀ x : R, IsUnit x → fib x = (a / c) • m (hermScal R σ x) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hR
  obtain ⟨-, hW, hH⟩ := coord_measures_haar F E σ hcm R d b lam hlam
  have hW1 := hW 1 M
  have hμ : (a • coordW R b lam 1 M).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul _ ha
  have hν : (c • lam).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul _ hc
  have hmap : (c • lam).map (hermScal R σ) = c • coordHerm R σ b lam 1 := by
    rw [Measure.map_smul, (hermScal_main F E σ hcm R d b).2.2 lam hlam]
  have G := Rescale.isGramFib_rescale F E σ hcm M J hJ R hR 1 _ _ m hW1 (hH 1) hm a c ha hc
  rw [← hmap] at G
  obtain ⟨n1, n2⟩ := hnull _ _ hμ hν
  exact ⟨⟨_, isFibreFamily_length F E σ hcm M J hJ R hR _ _ hμ hν n1 n2 _ G⟩,
    fun fib hf x hx => QTie.fib_eq_gramFib F E σ hcm M J hJ R hR _ _ hμ hν n1 n2 fib hf _ G x hx⟩

theorem units_Ainf : {c : Ainf F | ∀ w, c w ≠ 0} = {c | IsUnit c} :=
  Set.ext fun c => (Pi.isUnit_iff.trans (forall_congr' fun _ => isUnit_iff_ne_zero)).symm

theorem units_Fv (v : HeightOneSpectrum (𝓞 F)) : {c : Fv F v | c ≠ 0} = {c | IsUnit c} :=
  Set.ext fun _ => isUnit_iff_ne_zero.symm

theorem sw1b2 (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) : Formalism.MainNotions.StandardLattice.SW1b2 F E σ M J := by
  intro hM β hβ d b Φ Φi Φf Φv hΦi hpure hpos hΦ
  have hcm' : IsCMExt F E σ := hcm
  have hJ' : IsHermND σ J := hJ
  obtain ⟨⟨li, hli⟩, hl⟩ := StdEx.exists_std F
  choose lv hlv using hl
  obtain ⟨hex, hfd⟩ := haar_fundamental_exist F E σ hcm' M J hJ'
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have Ri := isLocR_Ainf F hcm'.1
  have Rv := LocFv.isLocR_Fv F
  refine ⟨CharEx.exists_isCharAF F, fun ψ hψ => ⟨hex, fun μ hμ => ⟨(hfd μ hμ).1, fun 𝓕 h𝓕 => ?_⟩⟩⟩
  obtain ⟨ai, av, hUa, hWi, hWv⟩ := SdTuples.sdW_coord F E σ hcm' M J hJ' d b li lv hli hlv ψ hψ 1
  obtain ⟨ci, cv, hUc, hNi, hNv⟩ := SdAny.selfDual_any F E σ hcm' li lv hli hlv ψ hψ
  refine ⟨⟨_, (hWi _).2 rfl⟩, ⟨_, (hNi _).2 rfl⟩, ⟨_, fun v => (hWv v _).2 rfl⟩, ⟨_, fun v => (hNv v _).2 rfl⟩,
    fun μi νi μv νv h1 h2 h3 h4 => ?_⟩
  obtain rfl := (hWi _).1 h1
  obtain rfl := (hNi _).1 h2
  obtain rfl : μv = fun v => av v • coordW (Fv F v) b (lv v) 1 M := funext fun v => (hWv v _).1 (h3 v)
  obtain rfl : νv = fun v => cv v • lv v := funext fun v => (hNv v _).1 (h4 v)
  obtain ⟨hai, hav, -, -, hU, -⟩ := UnitProdAlg.main F ai ci av cv hUa hUc
  obtain ⟨hci, hcv, -⟩ := UnitProdAlg.main F ci ai cv av hUc hUa
  have Hi : (coordW (Ainf F) b li 1 M).IsAddHaarMeasure ∧ (coordHerm (Ainf F) σ b li 1).IsAddHaarMeasure := by
    obtain ⟨h1, h2, h3, h4, -⟩ := id Ri
    obtain ⟨-, x, y⟩ := coord_measures_haar F E σ hcm' (Ainf F) d b li hli.1
    exact ⟨x 1 M, y 1⟩
  have Hv : ∀ v, (coordW (Fv F v) b (lv v) 1 M).IsAddHaarMeasure ∧
      (coordHerm (Fv F v) σ b (lv v) 1).IsAddHaarMeasure := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := Rv v
    obtain ⟨-, x, y⟩ := coord_measures_haar F E σ hcm' (Fv F v) d b (lv v) (hlv v).1
    exact ⟨x 1 M, y 1⟩
  obtain ⟨mi, hmi⟩ := GramExist.exists_gramFib F E σ hcm' M J hJ' (Ainf F) Ri 1 _ _ Hi.1 Hi.2
  choose mv hmv using fun v => GramExist.exists_gramFib F E σ hcm' M J hJ' (Fv F v) (Rv v) 1 _ _ (Hv v).1 (Hv v).2
  have Li := loc hcm' hJ' (Ainf F) Ri (NullSets.null_sets F E σ hcm' M J hJ' (by omega)) b li hli.1 mi hmi ai ci hai hci
  have Lv := fun v => loc hcm' hJ' (Fv F v) (Rv v) (NullV.null_nonunits F E σ hcm' M J hJ' (by omega) v) b (lv v)
    (hlv v).1 (mv v) (hmv v) (av v) (cv v) (hav v) (hcv v)
  rw [← units_Ainf] at Li
  simp only [← units_Fv] at Lv
  refine ⟨Li.1, ⟨fun v => (Lv v).1.choose, fun v => (Lv v).1.choose_spec⟩, fun fi fv hfi hfv => ?_⟩
  have hu : IsUnit β := hβ.isUnit
  have ei := Li.2 fi hfi _ (hu.map (algebraMap F (Ainf F)))
  have ev := fun v => (Lv v).2 (fv v) (hfv v) _ (hu.map (algebraMap F (Fv F v)))
  let T : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E β
  have hT : ∀ a b, σ (T b a) = T a b := fun _ _ => σ.commutes β
  have hβE : algebraMap F E β ≠ 0 := (map_ne_zero _).2 hβ
  have hdet : T.det ≠ 0 := by rw [Matrix.det_fin_one]; exact hβE
  have hof : ∀ (R : Type) [CommRing R] [Algebra F R], hermOf R σ T hT = hermScal R σ (algebraMap F R β) := fun R _ _ =>
    Subtype.ext (funext fun _ => funext fun _ => by
      show (1 : R) ⊗ₜ[F] algebraMap F E β = algebraMap F R β ⊗ₜ[F] (1 : E)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])
  have hE := OneVector.siegel_one_vector F E σ hcm' M J hJ' hM T hT hdet d b li lv hli hlv μ 𝓕 hμ h𝓕 mi mv hmi hmv
  simp only [hof] at hE
  obtain ⟨k1, k2, k3⟩ := EulerPos.euler_pos F E σ hcm' d b 1 M _ _ _ hE
    (fun v => (LocFin.fibre_loc_fin F E σ hcm' M J hJ' (Fv F v) (Rv v) 1 _ _ (mv v) (Hv v).1 (Hv v).2 (hmv v) _).1)
    _ _ hU Φ Φi Φf Φv hΦi hpure hpos hΦ
  rw [ThetaLint.theta_lint_eq F E σ hcm' M J hJ' μ 𝓕 hμ h𝓕 1 _ Φ k1] at k3
  have hS : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J (x 0) (x 0) = algebraMap F E β} =
      {X | gramE σ J X = T} := by
    ext x
    constructor
    · rintro ⟨-, h⟩
      funext a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      exact h
    · intro h
      have h0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J (x 0) (x 0) = algebraMap F E β := congrFun (congrFun h 0) 0
      refine ⟨fun hx => hβE ?_, h0⟩
      rw [← h0, hx]
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform]
  simp only [ei, ev]
  rw [hS]
  exact ⟨k2, k3⟩

end CompanionTheory.HU
