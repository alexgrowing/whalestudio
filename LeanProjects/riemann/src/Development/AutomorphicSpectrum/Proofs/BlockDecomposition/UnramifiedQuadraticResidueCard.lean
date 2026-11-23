import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusEntryLeMRow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsQuadCharUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdChEOfOrdUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLFactorHalfNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticUniformizerOrderStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralSubst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdEqZeroOfModulusEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticExtensionValuationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerRightUnipotentFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSchwartzCompactSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSmoothVectorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RamifiedQuadraticExtensionValuationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RamifiedQuadraticExtensionUniformizerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticExtensionUniformizerValuationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionWhittakerFormulaStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WInert

theorem winert_span : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → residueCard E = residueCard F ^ 2 → ∀ χ : AddChar F Circle, IsStd χ → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ η : Fˣ →* ℂˣ, (∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) → ∀ c : Eˣ →* ℂˣ, IsUnit1 c → IsUnramifiedChar c → ∀ b : ℂˣ, b ^ 2 = c (Units.map (algebraMap F E).toMonoidHom (unifUnit F)) → ∀ Φ ∈ GL2LocalData.SBc F E c, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) (GL2LocalData.lamE E χ η) c Φ ∈ Submodule.span ℂ {f : GL (Fin 2) F → ℂ | ∃ h : GL (Fin 2) F, f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![b, -b] (g * h)} := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ h2 hcont hres χ hχ σ hσ η hη c hc1 hc b hb Φ hΦ
  have hord := GlobalTheory.T.unramified_quadratic_extension_valuation F E h2 hcont hres
  obtain ⟨η', hη'⟩ := GlobalTheory.CompanionTheory.SphTheta.UnramQuad.exists_quadChar_unramified F E h2 hcont hord
  have hηe : η = η' := by
    ext a
    rw [hη, hη'.1]
  subst hηe
  have hstd := GlobalTheory.CompanionTheory.SphTheta.isStd_chE_of_ord_unif F E h2 hcont hord χ hχ
  have hlam := GlobalTheory.CompanionTheory.LamUnr.lamE_eq_one F E χ η hχ hstd hη'.2.1 hη'.2.2.1
  have hform := GlobalTheory.CompanionTheory.SphTheta.inert_rw F E h2 hcont hord χ η σ hσ hχ hstd hη'
    (GlobalTheory.T.unramified_quadratic_uniformizer_order F E h2 hcont hord χ η hχ hstd hη')
  rw [hlam]
  have hψ : ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar χ) x = 1 := by
    intro x hx
    have h1 := isTrivialOn_addCharConductor hχ.1 hχ.2.1 x
      (by rw [hχ.2.2]; exact mem_valBall_zero_iff.2 hx)
    simp [h1]
  set f₁ : GL (Fin 2) F → ℂ := Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![b, -b] with hf₁
  have hW0 : ∀ g, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd g = f₁ g := by
    intro g
    have hg := Spherical.eq_iwasawa g
    have hu := Spherical.iwasawaUnip_mem g
    have hk := Spherical.iwasawaInt_mem g
    set u := Spherical.iwasawaUnip g
    set k := Spherical.iwasawaInt g
    set l := Iwasawa.iwasawaExponent F 2 g
    rw [hg, hf₁, Spherical.sphericalWhittaker_apply hψ _ hu hk,
      GlobalTheory.T.ramified_quadratic_extension_valuation F E h2 hcont hord χ η σ c hχ hc hη' hform _ k hk, mul_assoc,
      GlobalTheory.T.ramified_quadratic_extension_uniformizer F E h2 hcont hord χ η σ c hχ hc hη' hform u _ hu,
      GlobalTheory.T.quadratic_extension_uniformizer_valuation F E h2 hcont hord χ η σ c hχ hc hη' hform b hb l]
    have hpsi : Whittaker.psiN (Circle.coeHom.compAddChar χ) u = (χ (u.val 0 1) : ℂ) := by
      simp [Whittaker.psiN, Whittaker.superdiagSum, Fin.sum_univ_two]
      rfl
    rw [hpsi]
    split_ifs with hl
    · ring
    · simp
  obtain ⟨s, n, a, y, hdec⟩ := GlobalTheory.T.unramified_extension_whittaker_formula F E h2 hcont hord χ hχ c hc Φ hΦ
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  set Ψ : Fin n → E → ℂ := fun j x => (χ (y j * Algebra.norm F x) : ℂ) * intInd (x * (s : E)) with hΨ
  have hΦe : Φ = fun z => ∑ j, a j * Ψ j z := funext hdec
  have hI0 : Continuous (fun x : E => (intInd (x * (s : E)) : ℂ)) :=
    (InertAsm.intInd_isLocallyConstant (K := E)).continuous.comp (continuous_id.mul continuous_const)
  have hI1 : HasCompactSupport (fun x : E => (intInd (x * (s : E)) : ℂ)) :=
    (InertAsm.intInd_hasCompactSupport (K := E)).comp_homeomorph (Homeomorph.mulRight₀ (s : E) s.ne_zero)
  have hPc : ∀ j, Continuous (Ψ j) := fun j => by
    have hN := GroundTheory.LocalField.continuous_algebraNorm F E
    exact (continuous_induced_dom.comp (hχ.1.comp (continuous_const.mul hN))).mul hI0
  have hPs : ∀ j, HasCompactSupport (Ψ j) := fun j => hI1.mul_left
  set κ : ℂ := ((c s : ℂˣ) : ℂ) * (((modulus (Algebra.norm F (s : E)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) with hκ
  have hκ0 : κ ≠ 0 := by
    refine mul_ne_zero (Units.ne_zero _) ?_
    have h0 : ((modulus (Algebra.norm F (s : E)) : ℝ) : ℂ) ≠ 0 := by
      have := modulus_ne_zero (K := F) ((Algebra.norm_ne_zero_iff).2 s.ne_zero)
      exact_mod_cast this
    simp [Complex.cpow_eq_zero_iff, h0]
  have hstep : ∀ j g, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c (Ψ j) g =
      κ⁻¹ * f₁ (g * (uni2 (y j) * dg2 (Units.map (Algebra.norm F : E →* F) s) 1)) := by
    intro j g
    have h1 := GlobalTheory.T.weil_whittaker_right_unipotent_formula F E h2 χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c (fun z => intInd (z * (s : E))) (y j) g
    have h2' := GlobalTheory.T.weil_whittaker_schwartz_compact_support F E h2 χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd
      (InertAsm.intInd_mem_SBc c hc) s (g * uni2 (y j))
    rw [← hW0, ← mul_assoc g, h2', h1, ← hκ, inv_mul_cancel_left₀ hκ0]
  have hfun : GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c Φ =
      ∑ j, (a j * κ⁻¹) • (fun g => f₁ (g * (uni2 (y j) * dg2 (Units.map (Algebra.norm F : E →* F) s) 1))) := by
    funext g
    rw [hΦe, GlobalTheory.T.weil_whittaker_smooth_vector F E h2 hcont χ hχ.1 σ 1 c n a Ψ hPc hPs g, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hstep, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [hfun]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GlobalTheory.CompanionTheory.WInert
