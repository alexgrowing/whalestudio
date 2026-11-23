import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSectionOfLevelCoverThetaClassSumStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaClassSumDominantWeightIsCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsReducedIntegralBasisHarmonicPolynomials

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ClsVal

namespace GlobalTheory.ClsVal

theorem exists_cusp_isThClsD_unique : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → Formalism.L2.Pj.IsUnf (U σ)) → l.A = 1 → CovPin Xo c (fun _ : Unit => d) → GlobalTheory.Dict.UnitC d → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (bad : ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → LastPos Dw a → (∀ j, DatEq d ψ (w j)) → RepsOK (l := d.l₂) bad La Nc gam → LinearMap.range io ≤ Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ xs : Cl → Vs, ∃ f ∈ Formalism.L2.Pj.cusp Xo c U a n, IsThClsD Xo c d w La Nc gam vol ep io xs f ∧ ∀ f' ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f' → f' = f := by
  intro hci E _ _ _ H Dw l Xo c n d r U hr hU hA hcov hunit ψ hψ Cl _ w La Nc gam bad vol ep Vs _ _ io a hD hL hw hreps
    hio xs
  obtain ⟨hlev, hA₂, hnab⟩ := hcov ()
  have hLat : LatsOK d.l₂.M La Nc := fun k => ⟨(hreps k).1, (hreps k).2.2.1, (hreps k).2.2.2.1⟩
  have hP : ∀ v, io v ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := fun v =>
    GlobalTheory.HarmBasis.mem_HHa_of_mem_span subset_rfl (hio (LinearMap.mem_range_self io v))
  obtain ⟨f, hf, hcls⟩ := GlobalTheory.T.exists_section_of_levelCover_thetaClassSum hci E H Dw l Xo c n d hlev (hA₂.trans hA.symm) hnab ψ hψ Cl w La Nc gam vol ep
    Vs io xs a hw hLat fun j => hP _
  refine ⟨f, ?_, hcls, fun f' hf' hcls' => ?_⟩
  · rw [← Formalism.L2.PjFree.cusp_ofPj]
    exact GlobalTheory.T.thetaClassSum_dominant_weight_isCuspForm hci E H Dw l Xo c n d r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr
      (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hU σ hσ)) hA hlev hA₂ hnab hunit Cl w La Nc gam vol ep Vs io xs a
      hD hL hLat (fun j => hP _) f hf hcls
  · exact GlobalTheory.ClassSumUnique.isThClsD_unique hci E H Dw l Xo c n d Cl w La Nc gam vol ep Vs io hlev hnab hLat a hP xs a n
      f' hf' f hf hcls' hcls

end GlobalTheory.ClsVal
