import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SumInner
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.MatBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Gl2LocalToAdelicEmbedding
import Development.AutomorphicArithmetic.WhittakerHecke.BlockDiagonalEqLeviEmbedding
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceB
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.constantTerm_heckeOperator_eq_sum_satake :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (w : Pl E) (ϖ : w.adicCompletion E) (hϖ : ϖ ∈ Ov E w) (hu : IsUnifV E w ϖ)
      [Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩)] (j : ℕ), j ≤ r + s → ∀ φ : Sm E (r + s), Umg φ → (∀ k ∈ KGL w (r + s), rw (r + s) w k φ = φ) → ∀ (x : GA E r) (m : GA E s),
      AutomorphicForm.constantTerm r (heckeVec (rw (r + s) w) (KGL w (r + s)) (Tj ℂ (r + s) (Ov E w) ϖ j) φ).1 (lev (Ad E) r s (x, m)) =
        ∑ p : Fin (r + 1) × Fin (s + 1), UpperTheory.V.Cj.S.coef (qV E w) r s j p *
          ∑ i₁ : SatakeIdx w hϖ (n := r) p.1, ∑ i₂ : SatakeIdx w hϖ (n := s) p.2,
            AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁)), m * finGL E s (locGL E s w (satakeB w hϖ hu i₂)))) := by
  intro E _ _ _ r s w ϖ hϖ hu _ j hj φ hφ hK x m
  have hc : Continuous φ.1 := ((UpperTheory.ConvolutionTheory.BW.umgOps E (r + s)).2 φ hφ).1
  obtain ⟨b1, b2, b3, -⟩ := UpperTheory.V.Cj.S.gl2_local_to_adelic_embedding E w r s
  have h1 := UpperTheory.V.Cj.S.hkSum E w (r + s) (Sm E (r + s)) (rw (r + s) w) ϖ hϖ hu j hj φ (GlobalTheory.LGrp.mem_fixed.2 hK)
  have h2 : ∀ g, AutomorphicForm.constantTerm r (heckeVec (rw (r + s) w) (KGL w (r + s)) (Tj ℂ (r + s) (Ov E w) ϖ j) φ).1 g =
      ∑ i : SatakeIdx w hϖ (n := r + s) j,
        AutomorphicForm.constantTerm r φ.1 (g * finGL E _ (locGL E _ w (satakeB w hϖ hu i))) := fun g => by
    unfold AutomorphicForm.constantTerm
    rw [← integral_finsetSum _ fun i _ => AutomorphicForm.integrableOn_constantTerm hc _, h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, ← mul_assoc]
    rfl
  rw [h2, ← UpperTheory.blockDiagonal_eq_leviEmbedding, UpperTheory.V.Cj.S.hkLocal UpperTheory.V.Cj.S.sumInner UpperTheory.V.Cj.S.matBlock E w r s ϖ hϖ hu j
    (fun g => AutomorphicForm.constantTerm r φ.1 (UpperTheory.V.Af.Fin.blk x m * finGL E _ (locGL E _ w g))) (fun X g => by
      obtain ⟨Y, hY⟩ := b2 X
      obtain ⟨Y', hY'⟩ := b3 x m Y
      simp only [map_mul]
      rw [hY, ← mul_assoc, hY', mul_assoc, PositivityTheory.Rg.Rs.SliceClasses.constantTerm_unipGL_mul hφ.left])]
  simp only [b1]
  simp only [UpperTheory.blockDiagonal_eq_leviEmbedding, ← map_mul, Prod.mk_mul_mk]
