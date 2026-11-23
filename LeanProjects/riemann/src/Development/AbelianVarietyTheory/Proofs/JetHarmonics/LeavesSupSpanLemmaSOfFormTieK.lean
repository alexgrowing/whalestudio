import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupLatticeIsLatInStable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaSpansIsLatIn
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledSpanClauses
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevActMemMlat
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RunWeightsSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaStableOfAlgHom
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductsShortRec

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem leaves_sup_span_lemmaS_of_formTieK : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc), (∀ (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J), ∃ (T : Full D) (h : LawsP T.toTop) (j : ℕ) (hj : InR D j) (p : ℕ) (_ : Algebra (recB h.toLawsCore).KO K), ∃ z act, ∃ ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), FormTieK (recPJ h j hj) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO O v i z act ∧ IsLevAct T.toTop h j (kaR Tp hK j) ℓ act ∧ LawsFull T ∧ (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) ∧ OneCover T.toTop j ∧ 0 < p ∧ Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h.toLawsCore) j (kaR Tp hK j) ∧ ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) (kaR Tp hK j) ∧ WeightAlgebra.H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j)) → LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O := by
  intro hCI D L Pm Tp hK hinj EX K _ _ _ Bs Df S P _ _ oc O H
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J),
      (IsLatIn ⊤ (O.Ms i) ∧ ∀ g : P, (O.Ms i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Ms i) ∧
      (IsLatIn ⊤ (O.Th v i) ∧ IsLatIn ⊤ (O.ThK v i)) ∧
      (O.Th v i ≤ O.Ms i ∧ (∀ g : P, (O.Th v i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Th v i) ∧
        O.σ v i ≠ 0 ∧ O.Th v i ≤ Formalism.EigenvalueLevelCeiling.sc (O.σ v i) (O.ThK v i)) := by
    intro v i
    obtain ⟨T, h, j, hj, p, inst, z, act, ℓ, hFK, hA, hFull, hxi, hO, hp, hLat, hSp, hH⟩ := H v i
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.RunDepth.run_weights_sum D L Pm Tp hK j hj
    have hF := hFK.toFormTie (shortTh_fg _ hinj EX hp _ _ _ _ hLat hH)
      (productsShort_rec hCI D T.toTop h j hj hFull.sh hO (hFull.lvA j hj 0) _ _ _ _ h1 h2 h3 h4 (kaWt_n _ _ _ _))
    exact ⟨supLattice_isLatIn_stable D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF hLat
        (levAct_mem_Mlat D T.toTop h j hj _ P ℓ act hA),
      theta_spans_isLatIn D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF hp h1 h2 h3 hLat hSp hH,
      GlobalTheory.scaledSpan_clauses D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF h1 h2 h3 hH
        (levAct_theta hCI D T h j hj hFull hxi _ _ _ _ _ h1 h2 h3 h4 P ℓ act hA)⟩
  obtain ⟨v₀, -⟩ := exists_place3 K
  exact ⟨fun i => (key v₀ i).1,
    fun w _ => ⟨fun i => (key w i).2.1, fun i => (key (conjPl w) i).2.1⟩,
    fun w _ => ⟨fun i => (key w i).2.2, fun i => (key (conjPl w) i).2.2⟩⟩

end GlobalTheory.FormTies
