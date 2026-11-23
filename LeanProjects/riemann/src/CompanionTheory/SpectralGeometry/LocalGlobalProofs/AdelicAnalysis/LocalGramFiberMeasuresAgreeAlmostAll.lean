import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureProdOfAddGroupsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormsIntegrallyEquivalentAlmostAllStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresChangeOfFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem lattice_mass_fibre_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ n : ℕ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m', IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → IsGramFib (Fv F v) σ J' n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ S, m S (latV b v) = m' S (latV b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ J' hJ' d b n
  filter_upwards [GlobalTheory.T.hermitian_forms_integrally_equivalent_almost_all F E σ hσ M J hJ J' hJ' d b] with v hv
  intro lam hlam m m' hm hm' S
  obtain ⟨g, hg, hlat⟩ := hv
  have hL := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hL
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  haveI := hlam.1
  obtain ⟨-, c2, c3⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam hlam.1
  haveI := c2 n M
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b n M v
  have hcont : ∀ k : GL (Fin M) (Fv F v ⊗[F] E),
      Continuous (actTup (Fv F v) (n := n) k) := by
    intro k
    refine continuous_pi fun a => ?_
    exact Continuous.matrix_mulVec continuous_const ((continuous_apply a))
  have hinv : ∀ (k l : GL (Fin M) (Fv F v ⊗[F] E)), k * l = 1 → ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      actTup (Fv F v) k (actTup (Fv F v) l X) = X := by
    intro k l hkl X
    funext a
    have h : (k : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * (l : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) = 1 := by
      rw [← Units.val_mul, hkl, Units.val_one]
    simp only [actTup, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  let e : (Fin n → Fin M → Fv F v ⊗[F] E) ≃+ (Fin n → Fin M → Fv F v ⊗[F] E) :=
    { toFun := actTup (Fv F v) g
      invFun := actTup (Fv F v) g⁻¹
      left_inv := hinv g⁻¹ g (inv_mul_cancel g)
      right_inv := hinv g g⁻¹ (mul_inv_cancel g)
      map_add' := by
        intro X Y
        funext a
        simp only [actTup, Pi.add_apply, Matrix.mulVec_add] }
  have hmap : (coordW (Fv F v) b lam n M).map e = coordW (Fv F v) b lam n M :=
    (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open _ _ (coordW (Fv F v) b lam n M) (coordW (Fv F v) b lam n M) e (hcont g)
      (hcont g⁻¹)).2 (latV b v) (latV b v) a1 a2 ⟨0, a3⟩ (hlat n) rfl
  have hfib := GlobalTheory.T.gram_fiber_measures_change_of_form F E σ hσ M J hJ J' hJ' (Fv F v) hL n (coordW (Fv F v) b lam n M)
    (coordHerm (Fv F v) σ b lam n) m (c2 n M) (c3 n) hm (coordW (Fv F v) b lam n M) m' (c2 n M) hm' g hg 1
    (by rw [one_smul]; exact hmap) S
  have hval := congrArg (fun μ => μ (latV b v)) hfib
  simp only [one_smul] at hval
  rw [Measure.map_apply (hcont g).measurable a2.measurableSet] at hval
  have hpre : actTup (Fv F v) (n := n) g ⁻¹' latV (M := M) (n := n) b v = latV b v := by
    ext X
    exact hlat n X
  rw [hpre] at hval
  exact hval.symm

end GlobalTheory.CompanionTheory.SW
