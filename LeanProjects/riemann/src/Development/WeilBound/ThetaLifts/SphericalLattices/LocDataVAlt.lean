import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalChartInertPlaceUnitaryPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceLocalHeisenbergEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalHeisenbergOperatorsLawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelOppositeLagrangianUnitaryOpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesVacuumInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilHomFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceWeilNormalisesHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceIntegralUnitaryPointsFixVacuumStatement

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.KFinLoc

theorem locDataV' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hTr : IsTriple B G X om om') {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hv : v ∉ X.T) : LocData G.M' om' v := by
  obtain ⟨ϖ, σL, q, δ, JS, JT, ψL, κ, ιS, ιT, hC⟩ := GlobalTheory.T.exists_localChart_inertPlace_unitaryPair F E σ B a a' G X om om' hTr v w hw hv
  have hC' := hC
  obtain ⟨unr, hodd, intS, intT, hS, hT, hδ, p1, p2, -, -, -, -, -, hιS, hιT, hKS, hKT⟩ := hC'
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_inertPlace_local_heisenbergEndomorphism F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_localWeilHom_finitePlace F E σ B a a' G X om om' hTr v w hw hv σL JS JT ιS ιT hιS hιT
  obtain ⟨r0, rmul⟩ := GlobalTheory.T.inertPlace_localHeisenbergOperators_law F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  obtain ⟨s, hs, hs0, hsv⟩ := GlobalTheory.T.inertPlace_vacuum_isLocalVacuum_chart F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  have hline := GlobalTheory.T.exists_smul_vac_eq_of_localVacuum_linearModel F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s
  have hspan := GlobalTheory.T.span_heisenbergTranslates_vacuum_inertPlace F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s hs
  have hnorm := GlobalTheory.T.inertPlace_weil_normalises_heisenberg F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ ω hω
  have hfix := GlobalTheory.T.inertPlace_integralUnitaryPoints_fix_vacuum F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ω hω s hs
  refine ⟨w.adicCompletion E, inferInstance, inferInstance, inferInstance, inferInstance, ϖ, σL, q, δ, JS, JT, ψL, ρ, ω,
    ιS, ιT, s, ⟨unr, hodd, intS, intT, hS, hT, hδ, p1, p2, r0, rmul, ?_, hnorm, ?_⟩, hs0, hsv, hspan, hs,
    hιS, hιT, hKS, hKT, fun g h m φ₁ hφ₁ => hω g h m φ₁ hφ₁⟩
  · rw [eq_top_iff, ← hspan]
    exact Submodule.span_mono (by rintro _ ⟨x, rfl⟩; exact ⟨x, s, hsv, rfl⟩)
  · intro g h hg hh t ht
    obtain ⟨c, rfl⟩ := hline t hs ht
    rw [map_smul, hfix g h hg hh]

end PositivityTheory.Sph

end
