import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigRescale

open GlobalTheory GlobalTheory.ArchMetricCompare

theorem exists_rescale_rig : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (rig : LB.Gen (L.pull (eSec A))), L.IsLB → rig.IsGen → ∃ (u' : HolUnif A L g) (lam : ℂ), lam ≠ 0 ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsRig rig ∧ ∀ i z, u'.fr i z = lam * u.fr i z := by
  intro A _ L g u rig hL hr
  have h0 : (u.ex 0).left = eSec A := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp [eSec]
  obtain ⟨j₀, hj₀⟩ := exists_chart_at hL (u.ex 0).left
  have hj₀' : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ (L.pull (eSec A)).U (fun _ => j₀) := by
    exact (le_pull_iff L (eSec A) (𝟙 (Sp ℂ)) (fun _ => j₀)).2 (by rw [Category.id_comp, ← h0]; exact hj₀)
  have hr₀ := valAt'_unit_ne_zero _ hj₀' (rig.s (fun _ => j₀))
  have hf₀ : u.fr j₀ 0 ≠ 0 := u.fr_ne j₀ 0 hj₀
  set r₀ := valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U (fun _ => j₀)) (rig.s (fun _ => j₀)).val with hr₀def
  let u' : HolUnif A L g :=
    { u with
      fr := fun i z => r₀ / u.fr j₀ 0 * u.fr i z
      fr_hol := fun i => (u.fr_hol i).const_mul _
      fr_ne := fun i z h => mul_ne_zero (div_ne_zero hr₀ hf₀) (u.fr_ne i z h)
      fr_compat := fun i j z h => by
        show r₀ / u.fr j₀ 0 * u.fr i z = _ * (r₀ / u.fr j₀ 0 * u.fr j z)
        rw [u.fr_compat i j z h]; ring }
  refine ⟨u', r₀ / u.fr j₀ 0, div_ne_zero hr₀ hf₀, rfl, rfl, ?_, fun _ _ => rfl⟩
  intro j hj
  have hj1 : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ (L.pull (eSec A)).U j := fun p _ => hj trivial
  have hm : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ ((L.pull (eSec A)).U j ⊓ (L.pull (eSec A)).U (fun _ => j₀)) :=
    (top_le_preimage_inf _ _ _).2 ⟨hj1, hj₀'⟩
  have hz : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U j₀) := by
    rw [top_le_preimage_inf, h0]
    exact ⟨by simpa only [Category.id_comp] using (le_pull_iff L (eSec A) (𝟙 (Sp ℂ)) j).1 hj1, by rw [← h0]; exact hj₀⟩
  have e := congrArg (fun a => valAt' (𝟙 (Sp ℂ)) _ (Units.val a)) (hr j (fun _ => j₀))
  simp only [Units.val_mul] at e
  rw [valAt'_mul] at e
  have e1 := (valAt'_res _ inf_le_left _ hm).symm.trans (e.trans (congrArg _ (valAt'_res _ inf_le_right _ hm)))
  have hg := val_pull_g L (eSec A) (𝟙 (Sp ℂ)) j (fun _ => j₀) hm
  rw [Category.id_comp] at hg
  have hc := u.fr_compat (j PUnit.unit) j₀ 0 hz
  rw [h0] at hc
  show r₀ / u.fr j₀ 0 * u.fr (j PUnit.unit) 0 = _
  rw [e1, hg, hc, ← hr₀def]
  field_simp

end GlobalTheory.RigRescale
