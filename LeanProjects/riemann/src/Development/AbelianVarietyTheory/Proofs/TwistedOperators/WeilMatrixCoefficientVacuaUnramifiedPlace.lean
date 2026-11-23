import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetCharStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeIntertwinerCoefficientAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexMovedHomLatticeSplitPlaceChartStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexMovedHomLatticeInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalHeckeCharDetDoubleCosetSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceEigenvalueIsSqrtNormStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexNormalizationInertNormEqNegStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacCoef

theorem frameLat_eq_latFrame {D : D7} (V : HSp D) : frameLat V = GlobalTheory.PlaceModel.latFrame V := by
  ext y; rw [mem_frameLat, GlobalTheory.PlaceModel.mem_latFrame]

theorem isSelfDualC_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  rw [frameLat_eq_latFrame]; exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem isUnram_host (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := by
  have hu : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
    haveI := D.host.isCMField_hostE
    exact GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  rw [GlobalTheory.LFun.isUnram_iff]
  intro P hP
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 D.host.F) P.asIdeal :=
    Algebra.unramified_iff_forall.1 hu ⟨P.asIdeal, P.isPrime⟩
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal :=
    Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 D.host.F) (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal).1 ‹_›).2
  have hv : P.asIdeal.under (𝓞 D.host.F) = v.asIdeal := by rw [← hP]; rfl
  have : P.asIdeal.LiesOver v.asIdeal := ⟨hv.symm⟩
  rw [hv] at h1
  rwa [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal _ v.ne_bot] at h1

theorem exists_place (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v ∧
      (¬ IsSplit (E := D.host.E) v → IsInertAt D.host.F D.host.E v w) := by
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (isUnram_host D v) with hs | ⟨w, hw⟩
  · obtain ⟨w, -, -, h, -⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    exact ⟨w, h, fun h' => absurd hs h'⟩
  · exact ⟨w, GlobalTheory.LFun.under_eq_of_isInertAt hw, fun _ => hw⟩

theorem val_inert (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) (hr : ResEta D χ n)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : IsInertAt D.host.F D.host.E v w) (hu : UnrAt χ w) : val χ w = (-1) ^ n :=
  GlobalTheory.LFun.ResEta.val_of_isInertAt (isCMExt_host D).2.2.1 hr hw hu

theorem l2_smul {D : D7} {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (c : ℂ) (f g : WO S T → ℂ) :
    l2 μ 𝓕 (c • f) g = c * l2 μ 𝓕 f g := by
  simp [l2, Formalism.IndefR.Lift.pet, mul_assoc, integral_const_mul]

theorem locChar_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (lam : ℕ →* ℂ)
    (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T))
    (hL : GlobalTheory.FinWeilO.IsLatRep hom.std.1 (frameLat S) (frameLat T) w₀ lam Om)
    (hlam : GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam)
    (hsq : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hs : IsSplit (E := D.host.E) v) {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v) (a : Gv T v) :
    ((locChar χS w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h a)) : ℂˣ) : ℂ) =
      ((locChar χS w' (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h' a)) : ℂˣ) : ℂ) := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hom.std S T
  let g : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f, hf⟩
  have e1 := (GlobalTheory.T.weilDatum_at_place_eq_latticeIntertwiner_mul_det_char D ψ S T χS χT om hom hom.std lam w₀ Om hL hlam hsq v w h a g).1 hs
  have e2 := (GlobalTheory.T.weilDatum_at_place_eq_latticeIntertwiner_mul_det_char D ψ S T χS χT om hom hom.std lam w₀ Om hL hlam hsq v w' h' a g).1 hs
  have hne : (Om (1, embV T v a) g : WO S T → ℂ) ≠ 0 := by
    intro h0
    have h3 : Om (1, embV T v a)⁻¹ (Om (1, embV T v a) g) = g := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have h1 : Om (1, embV T v a) g = 0 := Subtype.ext h0
    rw [h1, map_zero] at h3
    exact f0 (congrArg Subtype.val h3).symm
  exact smul_left_injective ℂ hne (e1.symm.trans e2)

theorem detval : ∀ (D : D7) (T : HSp D) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), UnrAt χ w → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, ((locChar χ w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)))) : ℂˣ) : ℂ) = ((val χ w : ℂˣ) : ℂ) ^ (∑ i, d i) := GlobalTheory.T.localHeckeChar_det_doubleCoset_splitPlace

theorem lamsplit : ∀ (D : D7) (lam : ℕ →* ℂ), (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsSplit (E := D.host.E) v → ∀ m : ℕ, lam (qV D.host.E w ^ m) = (Real.sqrt ((qV D.host.E w ^ m : ℕ) : ℝ) : ℂ) := GlobalTheory.T.split_place_eigenvalue_is_sqrt_norm

theorem laminert : ∀ (D : D7) (lam : ℕ →* ℂ), GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → lam (qV D.host.E w) = -((qV D.host.F v : ℕ) : ℂ) := GlobalTheory.T.indexNormalization_inert_norm_eq_neg

theorem inv_neg_pow_mul (x : ℂ) (N M : ℕ) :
    ((-x) ^ (N * M))⁻¹ = ((((-1 : ℂˣ) ^ N : ℂˣ) : ℂ) * (x ^ N)⁻¹) ^ (M : ℤ) := by
  rw [zpow_natCast, pow_mul, ← inv_pow, neg_pow, mul_inv, ← inv_pow (-1 : ℂ), inv_neg_one]
  push_cast
  rfl

theorem vac_coef : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χS w ∧ UnrAt χT w) → ∃ φ : Gv T v → ℂ, IsLocKer T S.rank (val χS) v φ ∧ ∀ (a : Gv T v) (f₁ f₂ : WO S T → ℂ), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → l2 μ 𝓕 (om (1, embV T v a) f₁) f₂ = φ a * l2 μ 𝓕 f₁ f₂ := by
  intro D ψ S T χS χT om hom μ 𝓕 hμ v hunr
  classical
  have hψ := hom.std
  obtain ⟨lam, hlam, hsq⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w₀, Om, hL⟩ := GlobalTheory.FinWeilO.exists_isLatRep hψ (isSelfDualC_frameLat S) (isSelfDualC_frameLat T) hlam
  obtain ⟨w₁, hw₁, hin₁⟩ := exists_place D v
  let I : Gv T v → ℕ := fun a => GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T))
    ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v a)))
  let ν : Gv T v → ℂ := fun a => if IsSplit (E := D.host.E) v then
    ((locChar χS w₁ (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram hw₁ a)) : ℂˣ) : ℂ) else 1
  refine ⟨fun a => ν a * (lam (I a))⁻¹, fun w h => ⟨fun hs e he => ?_, fun hw c ϖ e hϖ he => ?_⟩,
    fun a f₁ f₂ h₁ h₂ => ?_⟩
  · intro ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
    have hν : ν (e.symm (k₁ * t * k₂)) = ((val χS w : ℂˣ) : ℂ) ^ (∑ i, d i) := by
      simp only [ν, if_pos hs]
      rw [locChar_eq hom lam w₀ Om hL hlam hsq hs hw₁ h]
      exact detval D T χS v w h (hunr w h).1 e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
    have hI : I (e.symm (k₁ * t * k₂)) = qV D.host.E w ^ (S.rank * (∑ i, |d i|).toNat) :=
      GlobalTheory.T.index_movedHomLattice_splitPlaceChart D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
    show ν _ * (lam (I _))⁻¹ = _
    rw [hν, hI, lamsplit D lam hsq v w h hs]
    congr 1
    have hs0 : 0 ≤ ∑ i, |d i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hM : ((∑ i, |d i| : ℤ) : ℂ) = (((∑ i, |d i|).toNat : ℕ) : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg hs0).symm
    rw [hM]
    generalize (∑ i, |d i|).toNat = M
    rw [Real.sqrt_eq_rpow, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  · intro d t ht k₁ hk₁ k₂ hk₂
    have hns : ¬ IsSplit (E := D.host.E) v := not_isSplit_of_isInertAt hw
    have hν : ν (e.symm (k₁ * t * k₂)) = 1 := if_neg hns
    have hI : I (e.symm (k₁ * t * k₂)) = qV D.host.E w ^ (S.rank * (∑ i, max (d i) 0).toNat) :=
      GlobalTheory.T.index_moved_homLattice_inertPlace D S T v w h hw c ϖ e hϖ he d t ht k₁ hk₁ k₂ hk₂
    have hval := val_inert D χS S.rank hom.resS v w hw (hunr w h).1
    have hq := laminert D lam hlam v w hw
    show ν _ * (lam (I _))⁻¹ = _
    rw [hν, hI, map_pow, hq, hval, one_mul]
    have hs0 : 0 ≤ ∑ i, max (d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
    rw [← Int.toNat_of_nonneg hs0, zpow_natCast]
    generalize (∑ i, max (d i) 0).toNat = M
    clear hs0 hq hval hI hν hns hk₁ hk₂ ht
    exact inv_neg_pow_mul _ _ _
  · have hf₁ : IsThetaFunO ψ S T f₁ := h₁.1
    have hf₂ : IsThetaFunO ψ S T f₂ := h₂.1
    let g₁ : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f₁, hf₁⟩
    let g₂ : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f₂, hf₂⟩
    have hc := GlobalTheory.T.weil_latticeIntertwiner_coefficient_at_place D ψ S T hψ lam w₀ Om hL μ 𝓕 hμ v a g₁ g₂ h₁ h₂
    have hn := GlobalTheory.T.weilDatum_at_place_eq_latticeIntertwiner_mul_det_char D ψ S T χS χT om hom hψ lam w₀ Om hL hlam hsq v w₁ hw₁ a g₁
    show l2 μ 𝓕 (om (1, embV T v a) (g₁ : WO S T → ℂ)) (g₂ : WO S T → ℂ) =
      (ν a * (lam (I a))⁻¹) * l2 μ 𝓕 (g₁ : WO S T → ℂ) (g₂ : WO S T → ℂ)
    by_cases hs : IsSplit (E := D.host.E) v
    · rw [hn.1 hs, l2_smul, hc]
      simp only [ν, if_pos hs, I]
      ring
    · rw [hn.2 (hin₁ hs) (hunr w₁ hw₁).1 (hunr w₁ hw₁).2, hc]
      simp only [ν, if_neg hs, I]
      ring

end GlobalTheory.VacCoef
