import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceChartFramesConjMaximalCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameInteg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLatHatIffOfSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section
namespace GlobalTheory.ChartStab

set_option maxHeartbeats 1000000 in

theorem mem_splitLat_iff {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (u : Fin n → Fv D.host.F v) :
    u ∈ GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ ↔
      ∀ i, Valued.v ((((frCo φ β)⁻¹ : GL (Fin n) (Fv D.host.F v)).1 *ᵥ u) i) ≤ 1 := by
  set e := GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ) with he_def
  have hπ : GlobalTheory.SplitHecke.Chart e v (rdA φ) := GlobalTheory.SplitProjChart.chart_idem φ
  have he : IsSplitIdem D e := GlobalTheory.EmbChart.isSplitIdem_idem _
  have hemb : GlobalTheory.AdelicU.chartEmb hπ = GlobalTheory.SplitProjChart.emb φ := AlgHom.ext fun x => by
    rw [GlobalTheory.AdelicU.chartEmb_apply, GlobalTheory.SplitProjChart.rdA_incA]; rfl
  choose y hy using fun k => hπ.1 (u k)
  obtain ⟨Λ₁, hle, hfg, heq⟩ := GlobalTheory.ChainOnto.LStab.exists_fg_sub hβ
  have hsl : GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ₁ = GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ := by
    ext w
    rw [GlobalTheory.AdelicU.mem_splitLat, GlobalTheory.AdelicU.mem_splitLat, GlobalTheory.ChainOnto.LStab.latLoc_eq hle hfg heq v]
  have h1 := GlobalTheory.AdelicU.SplitFrame.mem_latHat_iff_of_support (GlobalTheory.AdelicU.isCMExt_host D) _ hfg
    (GlobalTheory.AdelicU.SplitFrame.vecLoc_self he hπ y) (GlobalTheory.AdelicU.SplitFrame.vecLoc_ne he hπ y)
  rw [hemb, hsl, show (fun k => rdA φ (y k)) = u from funext hy] at h1
  rw [← h1, GlobalTheory.SplitFrameColumn.latHat_iff_hatL, heq]
  have hβ' := hβ (fun k => Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * y k)))
  rw [hβ']
  have hsw : (fun k => Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * y k))) =
      toEAf D e • fun k => toEAf D (y k) := funext fun k => (toEAf D).map_mul e (y k)
  rw [hsw, Matrix.mulVec_smul]
  set w : Fin n → EAf D := (β⁻¹).1 *ᵥ fun k => toEAf D (y k) with hw
  refine forall_congr' fun i => ?_
  have h2 : (toEAf D e • w) i = toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (w i)) := by
    rw [map_mul, GlobalTheory.SplitFrameColumn.toEAf_finEmb]; rfl
  have h3 : rdA φ (GlobalTheory.AdelicLatMove.finEmb D (w i)) =
      ((((frCo φ β)⁻¹ : GL (Fin n) (Fv D.host.F v)).1 *ᵥ u) i) := by
    rw [← GlobalTheory.SplitProjChart.rdE_toEAf, GlobalTheory.SplitFrameColumn.toEAf_finEmb, hw, RingHom.map_mulVec]
    unfold frCo
    rw [← map_inv]
    congr 1
    funext k
    exact (GlobalTheory.SplitProjChart.rdE_toEAf φ (y k)).trans (hy k)
  rw [h2, show toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (w i)) =
      Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * GlobalTheory.AdelicLatMove.finEmb D (w i))) from rfl,
    GlobalTheory.SplitFrameColumn.comm_mem_intAf_iff, hπ.2.2.2, GlobalTheory.SplitHecke.isInt_Ov, HeightOneSpectrum.mem_adicCompletionIntegers, h3]

theorem hermND (D : D7) (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem isSelfDualAt_of_isSelfDualC {D : D7} (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSelfDualC V Λ) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.IsSelfDualAt D.sp.cm.sig V.gram Λ v := by
  refine (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff (hermND D V).2 hΛ.1).2 (fun y => ?_) v
  refine (hΛ.2 y).trans (forall₂_congr fun x _ => ?_)
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, hb⟩

theorem isSplitBasis_frCo {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) :
    GlobalTheory.AdelicU.IsSplitBasis (GlobalTheory.SplitProjChart.emb φ) Λ (frCo φ β) := fun u => by
  rw [mem_splitLat_iff hβ φ, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]

theorem grpCo_emb {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (B : GL (Fin V.rank) (Fv D.host.F v)) (x : GlobalTheory.FinZeta.Gv V v) :
    grpCo φ V B (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v x) =
      GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (hermND D V) (GlobalTheory.SplitProjChart.emb φ) B x := by
  rw [GlobalTheory.AdelicU.splitEquivIn_apply, ← GlobalTheory.SplitChartLink.rdA_matHom_embV]
  rfl

section Reindex

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem reindex_mem_KO {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (ε : ι ≃ m)
    {x : GL m K} (hx : x ∈ GlobalTheory.SplitWeil.KO K m) (y : GL ι K) (h : ∀ i j, y.1 i j = x.1 (ε i) (ε j)) :
    y ∈ GlobalTheory.SplitWeil.KO K ι := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨Units.map (Matrix.reindexAlgEquiv (ValuativeRel.valuation K).integer (ValuativeRel.valuation K).integer ε.symm).toMonoidHom a, ?_⟩
  ext i j
  rw [h]
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

theorem mem_KO_iff_reindex {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (ε : ι ≃ m)
    (x : GL m K) (y : GL ι K) (h : ∀ i j, y.1 i j = x.1 (ε i) (ε j)) :
    x ∈ GlobalTheory.SplitWeil.KO K m ↔ y ∈ GlobalTheory.SplitWeil.KO K ι :=
  ⟨fun hx => reindex_mem_KO ε hx y h,
    fun hy => reindex_mem_KO ε.symm hy x fun i j => by rw [h]; simp⟩

end Reindex

theorem chart_stab : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _ := by
  intro D s k v φ ι hsd hfr hch e he y
  obtain ⟨ε, -, hε⟩ := hch
  have hB := isSplitBasis_frCo hfr φ
  have hL := isSelfDualAt_of_isSelfDualC s.V hsd v
  rw [GlobalTheory.AdelicU.mem_stabLoc_iff_GLint (GlobalTheory.AdelicU.isCMExt_host D) (hermND D s.V) hL hB,
    (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne v _).1]
  have h2 := (hε y).2
  rw [he y, grpCo_emb] at h2
  exact mem_KO_iff_reindex ε _ y fun i j => by rw [← h2]; rfl

end GlobalTheory.ChartStab
