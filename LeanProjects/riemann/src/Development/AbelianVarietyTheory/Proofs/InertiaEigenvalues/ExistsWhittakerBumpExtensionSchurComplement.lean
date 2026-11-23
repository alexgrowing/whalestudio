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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGLStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApplyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGLStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionWhittakerEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionCompactSupportModuloUnipotent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionSmoothRightInvariant

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.Tx.schur_function_whittaker_equivariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) → (∀ u ∈ GlobalTheory.JSW.NA E (r + 1), ∀ g, b₁ (u * g) = GlobalTheory.JSW.psiN u * b₁ g) → ∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, schurF β b₁ χ (u * g) = GlobalTheory.JSW.psiN u * schurF β b₁ χ g := by
  first | (exact @GlobalTheory.SchurEquiv.schurF_equivariant) | (exact GlobalTheory.SchurEquiv.schurF_equivariant) | (intros; apply GlobalTheory.SchurEquiv.schurF_equivariant <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.Tx.schur_function_compact_support_modulo_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (r + 1), u⁻¹ * p ∈ C) → HasCompactSupport χ → ∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S (m + r + 1), schurF β b₁ χ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), u⁻¹ * p ∈ C := by
  first
  | exact @GlobalTheory.SchurExtCpt.exists_compact_support
  | exact GlobalTheory.SchurExtCpt.exists_compact_support
  | (intros; apply GlobalTheory.SchurExtCpt.exists_compact_support <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.Tx.schur_function_smooth_right_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) → (∃ U : Subgroup (GL (Fin (r + 1)) (Af E)), IsOpen (U : Set (GL (Fin (r + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b₁ (g * finGL E (r + 1) u) = b₁ g) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (r + 1), u⁻¹ * p ∈ C) → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS E (m + r + 1 + 1) S → ∀ x ∈ GlobalTheory.JSW.supS E (m + r + 1 + 1) S, schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := by
  first | (exact @GlobalTheory.SchurExt.schurF_mul_finGL_eq) | (exact GlobalTheory.SchurExt.schurF_mul_finGL_eq) | (intros; apply GlobalTheory.SchurExt.schurF_mul_finGL_eq <;> assumption)
end

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.SchurExt
open scoped Topology

namespace GlobalTheory.SchurExt.Parts

theorem L_glob : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ b : GA E (a + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA E (a + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (a + 1)), IsCompact C ∧ ∀ p, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (a + 1), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (a + 1)) (Af E)), IsOpen (U : Set (GL (Fin (a + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (a + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (a + 1)) := GlobalTheory.T.exists_smooth_whittakerBump_adelicGL

theorem L_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) → (∀ u ∈ GlobalTheory.JSW.NA E (r + 1), ∀ g, b₁ (u * g) = GlobalTheory.JSW.psiN u * b₁ g) → ∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, schurF β b₁ χ (u * g) = GlobalTheory.JSW.psiN u * schurF β b₁ χ g := GlobalTheory.Tx.schur_function_whittaker_equivariant

theorem L_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (r + 1), u⁻¹ * p ∈ C) → HasCompactSupport χ → ∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S (m + r + 1), schurF β b₁ χ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), u⁻¹ * p ∈ C := GlobalTheory.Tx.schur_function_compact_support_modulo_unipotent

theorem L_inv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) → (∃ U : Subgroup (GL (Fin (r + 1)) (Af E)), IsOpen (U : Set (GL (Fin (r + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b₁ (g * finGL E (r + 1) u) = b₁ g) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (r + 1), u⁻¹ * p ∈ C) → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS E (m + r + 1 + 1) S → ∀ x ∈ GlobalTheory.JSW.supS E (m + r + 1 + 1) S, schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := GlobalTheory.Tx.schur_function_smooth_right_invariant

theorem L_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) → (∀ g, ContDiffOn ℝ ∞ (chart b₁ g) (invSet E (r + 1))) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (r + 1), u⁻¹ * p ∈ C) → ContDiff ℝ ∞ χ → ∀ g, ContDiffOn ℝ ∞ (chart (schurF β b₁ χ) g) (invSet E (m + r + 1 + 1)) := GlobalTheory.T.contDiffOn_chart_schurComplementExtension

theorem L_block : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), ∀ h : GA E (m + 1), schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h * b₁ 1 * (χ 0 : ℂ) := GlobalTheory.T.schurComplementExtensionFunction_blockDiag_apply

theorem L_projNA : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ u ∈ GlobalTheory.JSW.NA E a, prS S a u ∈ GlobalTheory.JSW.NA E a ∧ prO S a u ∈ GlobalTheory.JSW.NA E a ∧ GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := GlobalTheory.T.adelicGLProjections_upperUnitriangular_genericChar

theorem L_projSupS : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ g ∈ GlobalTheory.JSW.supS E a S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS E a S := GlobalTheory.T.adelicGLProjections_on_supportedAtPlaces

theorem L_projInf : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)), prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := GlobalTheory.T.adelicGLProjections_mul_infiniteAdelicGL

theorem L_projFin : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := GlobalTheory.T.eventually_adelicGLProjections_finite_near_one

theorem L_blockSupS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS E (m + r + 1 + 1) S := GlobalTheory.T.blockDiagGL_mem_adelicGLSupportedAtFinitePlaces

end GlobalTheory.SchurExt.Parts
open GlobalTheory.SchurExt.Parts

theorem GlobalTheory.SchurExt.exists_ext : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (β : GA E (m + 1) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, β h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) →
    (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) →
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) →
    ∃ b : GA E (m + r + 1 + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧
      (∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S (m + r + 1), b p ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), u⁻¹ * p ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, b (g * finGL E (m + r + 1 + 1) u) = b g) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + r + 1 + 1))) ∧
      ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, b (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h := by
  intro E _ _ _ m r S β hβN hβC hβU hβS
  obtain ⟨b₁, h1one, h1N, h1C, h1U, h1S⟩ := L_glob E r
  obtain ⟨Φ, hΦ1, hΦN, -, ⟨UΦ, hUΦo, hUΦ⟩, -⟩ := GlobalTheory.WhitBump.exists_bump E (m + r + 1) S
  let f : ContDiffBump (0 : Fin (r + 1) → Fin (m + 1) → Cinf E) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨C, hC, hCp⟩ := L_cpt E m r S β b₁ f hβC h1C f.hasCompactSupport
  obtain ⟨W, hW, hWk⟩ := L_inv E m r S β b₁ f hβU hβC h1U h1C
  refine ⟨extB S β b₁ f Φ, ?_, ⟨C, hC, ?_⟩, ?_, ?_, ?_⟩
  · intro u hu g
    obtain ⟨h1, h2, h3⟩ := L_projNA E (m + r + 1 + 1) S u hu
    simp only [extB, map_mul]
    rw [L_equiv E m r β b₁ f hβN h1N _ h1, hΦN _ h2, ← h3]
    ring
  · intro p hp hne
    obtain ⟨e1, e2⟩ := (L_projSupS E _ S).1 p hp.1
    refine hCp p hp fun h0 => hne ?_
    simp only [extB, e1, e2, h0, zero_mul]
  · let U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)) :=
      { carrier := {k | ∀ g, extB S β b₁ f Φ (g * finGL E _ k) = extB S β b₁ f Φ g}
        mul_mem' := fun {a b} ha hb g => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, ← mul_assoc, hb, ha]
        one_mem' := fun g => by simp only [map_one, mul_one]
        inv_mem' := fun {a} ha g => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          have := ha (g * finGL E _ a⁻¹)
          rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
          exact this.symm }
    refine ⟨U, Subgroup.isOpen_of_mem_nhds U (g := 1) ?_, fun u hu g => hu g⟩
    have hV' : (UΦ : Set _) ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)) := hUΦo.mem_nhds UΦ.one_mem
    filter_upwards [L_projFin E _ S W _ hW hV'] with k hk
    obtain ⟨⟨k', hk'W, hk'⟩, ⟨k'', hk''V, hk''⟩⟩ := hk
    intro g
    simp only [extB, map_mul, hk', hk'']
    rw [hWk k' hk'W (hk' ▸ (L_projSupS E _ S).2 _) _ ((L_projSupS E _ S).2 g), hUΦ k'' hk''V]
  · intro g
    have hs := (L_smooth E m r β b₁ f hβS h1S h1C f.contDiff (prS S _ g)).mul
      (contDiffOn_const (c := Φ (prO S _ g)))
    refine hs.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    obtain ⟨e1, e2⟩ := L_projInf E _ S g hx'.unit
    simp only [chart, dif_pos hx', extB, e1, e2]
  · intro h hh
    obtain ⟨e1, e2⟩ := (L_projSupS E _ S).1 _ (L_blockSupS E m r S h hh)
    have hf0 : f 0 = 1 := f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)
    simp only [extB, e1, e2, hΦ1, mul_one, L_block, h1one, hf0, Complex.ofReal_one]
