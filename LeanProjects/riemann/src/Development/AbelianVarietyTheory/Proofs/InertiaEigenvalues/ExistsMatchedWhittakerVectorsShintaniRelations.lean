import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplementStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalSmoothBump
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerMulTorusIteratedFactorisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalSmoothBumpStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockEmbeddingGLTorusElementZeroPaddedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockGLSupportedMemMirabolicSupportedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnipotentInvariantCompactlySupportedWeight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartGlobalWhittakerCoefficient

section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix
set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.Tx.exists_unipotentInvariant_compactlySupported_weight : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (x₀ : GA E (m + 1)),
    ∃ κ : GA E (m + 1) → ℝ, Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h, κ h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart (fun h => (κ h : ℂ)) g) (invSet E (m + 1))) ∧ 0 < κ x₀ := by
  first
  | exact @GlobalTheory.KappaCut.exists_kappa
  | exact GlobalTheory.KappaCut.exists_kappa
  | (intros; apply GlobalTheory.KappaCut.exists_kappa <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix
set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.Tx.contDiffOn_chart_globalWhittakerCoefficient : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g, ContDiffOn ℝ ∞ (chart (GlobalTheory.JSW.whit φ.1) g) (invSet E a) := by
  first | (exact @GlobalTheory.JSW.WhitSmooth.whit_contDiffOn) | (exact GlobalTheory.JSW.WhitSmooth.whit_contDiffOn) | (intros; apply GlobalTheory.JSW.WhitSmooth.whit_contDiffOn  <;> assumption)
end

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

namespace GlobalTheory.JSW.MatchedVec

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem mem_mspanR_of_mem (π : CuspSub E a) {φ : Sm E a} (hφ : φ ∈ π.V) : φ.1 ∈ GlobalTheory.JSW.mspanR π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ hφ

def stab (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | finRep E a k φ = φ}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_level (φ : Sm E a) (hφ : IsAutForm φ) :
    ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧
      ∀ u ∈ U, ∀ g, φ.1 (g * finGL E a u) = φ.1 g :=
  ⟨stab φ, hφ.level, fun u hu g => congrArg (fun ψ : Sm E a => ψ.1 g) (show finRep E a u φ = φ from hu)⟩

theorem chart_mul (f f' : GA E a → ℂ) (g : GA E a) (x : Lie E a) :
    chart (fun h => f h * f' h) g x = chart f g x * chart f' g x := by
  unfold chart
  split_ifs <;> simp

end GlobalTheory.JSW.MatchedVec

open GlobalTheory.JSW.MatchedVec in

theorem GlobalTheory.JSW.MatchedVec.matched_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ),
    (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) →
    (∀ w ∉ S, HasSatGL w (π'.locRep w) (Finset.univ.val.map (β w))) →
    ∃ (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (m + r + 1 + 1), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1)
                       (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) ∧
      (∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
        GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
          (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) ∧
      Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      ∃ h₀ ∈ GlobalTheory.JSW.supS E (m + 1) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0 := by
  intro E _ _ _ m r S hcond π π' hπu hπ'u α β hα hβ
  obtain ⟨φ', hφ'V, hφ'K, x₀, hx₀S, hx₀⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E m S hcond π' β hβ
  obtain ⟨φ₀, hφ₀V, hφ₀K, x₁, hx₁S, hx₁⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E (m + r + 1) S hcond π α hα
  obtain ⟨κ, hκc, hκ0, hκN, ⟨C, hC, hκC⟩, ⟨Uκ, hUκo, hUκ⟩, hκsm, hκx₀⟩ := GlobalTheory.Tx.exists_unipotentInvariant_compactlySupported_weight E m x₀
  have haut' : IsAutForm φ' := (π'.cusp φ' hφ'V).1
  obtain ⟨U', hU'o, hU'⟩ := exists_level φ' haut'
  have hWN : ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ'.1 (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ'.1 g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul haut'.continuous (fun γ g => haut'.left γ g) hu g
  have hWU : ∀ u ∈ U', ∀ g, GlobalTheory.JSW.whit φ'.1 (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit φ'.1 g := by
    intro u hu g
    rw [← GlobalTheory.JSW.KirSemi.whit_rt]
    congr 1
    funext y
    exact hU' u hu y
  have hWsm := GlobalTheory.Tx.contDiffOn_chart_globalWhittakerCoefficient E (m + 1) φ' haut'
  set βf : GA E (m + 1) → ℂ := fun h => (κ h : ℂ) * GlobalTheory.JSW.whit φ'.1 h with hβf
  have hβN : ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, βf (u * g) = GlobalTheory.JSW.psiN u * βf g := by
    intro u hu g
    simp only [hβf, hκN u hu g, hWN u hu g]
    ring
  have hβC : ∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, βf h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C := by
    refine ⟨C, hC, fun h _ hne => hκC h ?_⟩
    intro h0
    apply hne
    simp [hβf, h0]
  have hβU : ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, βf (g * finGL E (m + 1) u) = βf g := by
    refine ⟨Uκ ⊓ U', hUκo.inter hU'o, fun u hu g => ?_⟩
    simp only [hβf, hUκ u hu.1 g, hWU u hu.2 g]
  have hβsm : ∀ g, ContDiffOn ℝ ∞ (chart βf g) (invSet E (m + 1)) := by
    intro g
    have e : chart βf g = fun x => chart (fun h => (κ h : ℂ)) g x * chart (GlobalTheory.JSW.whit φ'.1) g x :=
      funext fun x => chart_mul _ _ g x
    rw [e]
    exact (hκsm g).mul (hWsm g)
  obtain ⟨b, hbN, hbC, hbU, hbsm, hbblk⟩ := GlobalTheory.T.exists_whittaker_bump_extension_schur_complement E m r S βf hβN hβC hβU hβsm
  obtain ⟨F, hFspan, hFb, hFU, hFinv, hFeig⟩ :=
    GlobalTheory.T.kirillov_semilocal_smooth_bump E (m + r + 1) S b hbN hbC hbU hbsm π φ₀ hφ₀V ⟨x₁, hx₁S, hx₁⟩
  refine ⟨F, φ'.1, κ, hFspan, mem_mspanR_of_mem π' hφ'V, hFU, ?_, ⟨U', hU'o, hU'⟩, ?_, ?_, ?_, ?_,
    hκc, hκ0, hκN, ⟨C, hC, fun h _ hne => hκC h hne⟩, ⟨Uκ, hUκo, hUκ⟩, ⟨x₀, hx₀S, hκx₀, hx₀⟩⟩
  · intro w hw k hk g
    refine hFinv _ (pInf_finGL _) ?_ ?_ g
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [GlobalTheory.JSW.BumpShintani.map_comp_eq, pFin_finGL]
      exact pLoc_locGL_of_ne hne _
    · intro g'
      exact congrArg (fun ψ : Sm E (m + r + 1 + 1) => ψ.1 g') (hφ₀K w hw k hk)
  · intro w hw k hk g
    exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 g) (hφ'K w hw k hk)
  · intro ϖ hϖ l hl h hh
    exact GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + 1) S hcond π' β hβ φ' hφ'V hφ'K ϖ hϖ l hl h hh
  · intro ϖ hϖ l hl h hh
    set l' : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + r + 1 + 1) → ℕ) :=
      l.mapRange GlobalTheory.RSnmUnf.padNat GlobalTheory.RSnmUnf.padNat_zero with hl'
    have hsupp : l'.support = l.support := by
      ext w
      simp only [hl', Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq]
      constructor
      · intro h1 h2
        apply h1
        rw [h2, GlobalTheory.RSnmUnf.padNat_zero]
      · intro h1 h2
        apply h1
        funext i
        have := congrFun h2 ⟨i, by omega⟩
        simpa [GlobalTheory.RSnmUnf.padNat, i.2] using this
    have hl's : ∀ w ∈ l'.support, w ∉ S := fun w hw => hl w (hsupp ▸ hw)
    have hC := GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + r + 1 + 1) S hcond π α hα φ₀ hφ₀V hφ₀K ϖ hϖ l' hl's
    have hS : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l') = 1 :=
      fun w hw => GlobalTheory.JSW.BumpShintani.loc_tl ϖ l' w (fun h => hl's w h hw)
    have hmir := GlobalTheory.T.blockGL_supported_mem_mirabolic_supported E m r S h hh
    rw [map_mul, GlobalTheory.T.blockEmbeddingGL_torus_element_zero_padded E m r ϖ l, hFeig _ _ (GlobalTheory.JSW.BumpShintani.pInf_tl ϖ l') hS hC _ hmir.1, hsupp]
    rfl
  · intro h hh
    clear hβsm hβU hβC hβN hWsm hWU hWN hFeig hFinv
    exact (hFb _ (GlobalTheory.T.blockGL_supported_mem_mirabolic_supported E m r S h hh)).trans (hbblk h hh)
