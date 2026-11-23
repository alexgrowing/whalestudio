import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponents
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsDeepLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SpanShortProd

theorem eLpNorm_homN_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (x : ℝ)
    {D : D7} {W : HSp D} (dict : GA D W → Σ k, Frame (V.X k).Ψ r) (μ : MeasureTheory.Measure (AutQ W))
    (hμ : μ Set.univ ≤ 1) (G : WTZ E) (f : Rul Xo c) (hf : rdU V f ∈ holSub V.X (GlobalTheory.AllWt.modelWt V G)) :
    MeasureTheory.eLpNorm (fun q : AutQ W => GlobalTheory.AllWt.homN V x G f (dict q.out)) 2 μ ≠ ⊤ := by
  have hb : ∀ q : AutQ W, ‖GlobalTheory.AllWt.homN V x G f (dict q.out)‖ₑ ≤
      ENNReal.ofReal (GlobalTheory.AllWt.lieFacZ Dw x G) * supE V.X (GlobalTheory.AllWt.modelWt V G) (rdU V f) := by
    intro q
    rw [Real.enorm_eq_ofReal (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _), GlobalTheory.AllWt.homN,
      ENNReal.ofReal_mul (GlobalTheory.AllWt.lieFacZ_pos _ _).le]
    gcongr
    by_cases h : (dict q.out).2 ∈ (V.X (dict q.out).1).dom
    · exact le_iSup (fun p : FPt V.X => ENNReal.ofReal ((V.X p.1).pnorm (GlobalTheory.AllWt.modelWt V G p.1) (rdU V f p.1) p.2))
        ⟨(dict q.out).1, ⟨(dict q.out).2, h⟩⟩
    · have h0 : rdU V f (dict q.out).1 (dict q.out).2 = 0 := by simp [rdU, h]
      have h1 : GlobalTheory.AllWt.ptN (GlobalTheory.AllWt.modelWt V G) (rdU V f) (dict q.out) = 0 := by
        show ‖rdU V f (dict q.out).1 (dict q.out).2‖ * _ = 0
        rw [h0, norm_zero, zero_mul]
      rw [h1, ENNReal.ofReal_zero]; exact bot_le
  refine ne_top_of_le_ne_top ?_ (MeasureTheory.eLpNorm_le_of_ae_enorm_bound (Filter.Eventually.of_forall hb))
  rw [smul_eq_mul]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (supE_ne_top _ _ hf))
    (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (ne_top_of_le_ne_top ENNReal.one_ne_top hμ))

theorem petOn_mul_sig_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) {Z : Comp Xo c} {G G₀ : WTZ D.host.E}
    (t : GlobalTheory.FlatTw.TwSec U x Z G₀) (hG : Even G.2) {F : Rul Xo c} (hF : F ∈ cuspW Xo c U G) (σ : c.F →+* ℂ) :
    petOn U x V dict Z (G + G₀) σ (F * t.sig) ≤ t.cInf σ * petOn U x V dict Z G σ F := by
  unfold petOn
  rw [GlobalTheory.AllWt.petAt_eq, GlobalTheory.AllWt.petAt_eq]
  have hpt : ∀ q : AutQ (V (goodOf c σ)),
      ‖GlobalTheory.AllWt.homN (U (goodOf c σ)) x (G + G₀) (F * t.sig) (dict (goodOf c σ) q.out)‖ ≤
        (t.cInf σ • fun q : AutQ (V (goodOf c σ)) => GlobalTheory.AllWt.homN (U (goodOf c σ)) x G F (dict (goodOf c σ) q.out)) q := by
    intro q
    rw [Real.norm_of_nonneg (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _), Pi.smul_apply, smul_eq_mul]
    by_cases hz : dict (goodOf c σ) q.out ∈ GlobalTheory.AllWt.framesOn (U (goodOf c σ)) Z
    · rw [t.homN_mul_sig hG F hz, mul_comm]
    · have h0 : rdU (U (goodOf c σ)) (F * t.sig) (dict (goodOf c σ) q.out).1 (dict (goodOf c σ) q.out).2 = 0 :=
        GlobalTheory.AllWt.rdU_eq_zero _ (GlobalTheory.AllWt.mul_mem_suppOn F t.sig_mem_suppOn) hz
      have h1 : GlobalTheory.AllWt.homN (U (goodOf c σ)) x (G + G₀) (F * t.sig) (dict (goodOf c σ) q.out) = 0 := by
        show _ * (‖rdU (U (goodOf c σ)) (F * t.sig) (dict (goodOf c σ) q.out).1 (dict (goodOf c σ) q.out).2‖ * _) = 0
        rw [h0, norm_zero, zero_mul, mul_zero]
      rw [h1]
      exact mul_nonneg (t.cInf_pos σ).le (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _)
  have h1 := MeasureTheory.eLpNorm_mono_real (p := 2) (μ := GlobalTheory.AllWt.muOn (U (goodOf c σ)) (V (goodOf c σ))
    (dict (goodOf c σ)) Z) hpt
  rw [MeasureTheory.eLpNorm_const_smul, Real.enorm_eq_ofReal (t.cInf_pos σ).le] at h1
  have hfin := eLpNorm_homN_ne_top (U (goodOf c σ)) x (dict (goodOf c σ))
    (GlobalTheory.AllWt.muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z) (GlobalTheory.AllWt.muPart_univ_le _ _ _) G F
    ((GlobalTheory.AllWt.mem_cuspW.1 hF).2 _ (goodEmb_goodOf c σ))
  calc _ ≤ (ENNReal.ofReal (t.cInf σ) * MeasureTheory.eLpNorm (fun q : AutQ (V (goodOf c σ)) =>
        GlobalTheory.AllWt.homN (U (goodOf c σ)) x G F (dict (goodOf c σ) q.out)) 2
          (GlobalTheory.AllWt.muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h1
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (t.cInf_pos σ).le]

theorem exists_span_mul_twSec : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G G₀ : WTZ D.host.E) (t : GlobalTheory.FlatTw.TwSec U x Z G₀), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ w, 0 ≤ t.lo w) → ∀ s₀ : Set (Rul Xo c), s₀ ⊆ (cuspW Xo c U G : Set (Rul Xo c)) → (∀ f ∈ s₀, ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) → cuspW Xo c U G ≤ Submodule.span c.F s₀ → ∃ s : Set (cuspOn U Z (G + G₀)), s ⊆ (latOn U Z (G + G₀) : Set (cuspOn U Z (G + G₀))) ∧ Submodule.span c.F s = ⊤ ∧ ∀ y ∈ s, ∃ f ∈ s₀, ∀ σ, normOn U x V dict Z (G + G₀) σ y ≤ t.cInf σ * petOn U x V dict Z G σ f := by
  intro D H Dw l Xo c r U x V dict Z G G₀ t hU hG hlo s₀ hsub hval hspan
  let Q : cuspW Xo c U G →ₗ[c.F] cuspOn U Z G :=
    LinearMap.codRestrict (cuspOn U Z G) ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype)
      (fun F => GlobalTheory.CuspSplit.idem_mul_mem_cuspOn hU Z F)
  let ψ : cuspW Xo c U G →ₗ[c.F] cuspOn U Z (G + G₀) := (GlobalTheory.FlatTw.Mul.mulEquiv t G hG).toLinearMap ∘ₗ Q
  let s₁ : Set (cuspW Xo c U G) := {F | (F : Rul Xo c) ∈ s₀}
  have hQ : Function.Surjective Q := fun g =>
    ⟨⟨g, GlobalTheory.AllWt.cuspOn_le U Z G g.2⟩, Subtype.ext (GlobalTheory.CuspSplit.idem_mul_of_mem_cuspOn g.2)⟩
  have hψ : Function.Surjective ψ := (GlobalTheory.FlatTw.Mul.mulEquiv t G hG).surjective.comp hQ
  have hs₁ : Submodule.span c.F s₁ = ⊤ := by
    apply Submodule.map_injective_of_injective (cuspW Xo c U G).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    have e : (cuspW Xo c U G).subtype '' s₁ = s₀ := by
      ext f
      constructor
      · rintro ⟨F, hF, rfl⟩; exact hF
      · intro hf; exact ⟨⟨f, hsub hf⟩, hf, rfl⟩
    rw [e]
    exact le_antisymm (Submodule.span_le.2 hsub) hspan
  refine ⟨ψ '' s₁, ?_, ?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩
    have hFl : F ∈ GlobalTheory.AllWt.latW U G := hval F hF
    have hQF : Q F ∈ latOn U Z G := GlobalTheory.CuspSplit.mem_latOn_part hU F hFl Z
    exact GlobalTheory.FlatTw.Mul.mem_latOn_of_mul t 1 one_ne_zero (fun w => by
      have h1 : vAdd w (1 : c.F) = 0 := by simp [vAdd]
      rw [h1, Int.cast_zero, zero_add]; exact hlo w)
      (Q F) hQF (ψ F) (by rw [one_smul]; rfl)
  · rw [Submodule.span_image, hs₁, Submodule.map_top, LinearMap.range_eq_top]
    exact hψ
  · rintro _ ⟨F, hF, rfl⟩
    refine ⟨F, hF, fun σ => ?_⟩
    have e : ((ψ F : cuspOn U Z (G + G₀)) : Rul Xo c) = (F : Rul Xo c) * t.sig := by
      show idem Z * (F : Rul Xo c) * t.sig = _
      rw [mul_comm (idem Z), mul_assoc, t.idem_sig]
    show petOn U x V dict Z (G + G₀) σ _ ≤ _
    rw [e]
    exact petOn_mul_sig_le U x V dict t hG F.2 σ

end GlobalTheory.SpanShortProd
