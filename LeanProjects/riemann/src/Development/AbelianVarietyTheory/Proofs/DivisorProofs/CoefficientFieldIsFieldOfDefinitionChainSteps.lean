import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnalyticTiesTrueCols
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubStdL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TildeQDetPtEqChiId
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90USurjective
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyLiftObj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows.FldDef

theorem sd_of_isSdLat {B : Base} {n : ℕ} {L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)}
    (h : Formalism.L2.Col.IsSdLat (E := B.fields.E) L) : letI := B.host.cmStar; IsSDLat B.host.E n L := by
  letI := B.host.cmStar
  refine ⟨h.1.1, h.1.2, fun y => ?_⟩
  have h2 : y ∈ Formalism.HermitianLatticesTheory.dual (hStd B.fields.E n) L ↔ y ∈ L := by rw [h.2]
  rw [← h2, Formalism.L2.Col.mem_dual]
  refine forall₂_congr fun x _ => ?_
  rw [Submodule.mem_one]
  rfl

theorem sd_stdL (D : D7) (n : ℕ) : StandardLatticesGL3.SD D (Th.stdL D.host n) := by
  exact GlobalTheory.Glob.IntegralWittCoefficients.Model.isSDLat_std _ _

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem chiRec_detId {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)}
    (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl) (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E))
    (hL : StandardLatticesGL3.SD (I.rec7 l Z) L) :
    TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host n) L) = I.chi (Th.detId B.host (Th.stdL B.host n) L) := by
  letI := B.host.cmStar
  let S0 : SDLat B.host.E n := ⟨Th.stdL B.host n, sd_stdL (I.rec7 l Z) n⟩
  let L1 : SDLat B.host.E n := ⟨L, hL⟩
  have h2 : idl ((I.rec7 l Z).relDet n S0 L1) = TaylorLogMetric.detId (I.rec7 l Z) S0.1 L1.1 := hidl.2.2.2.2 n S0 L1
  have e : TaylorLogMetric.detId (I.rec7 l Z) S0.1 L1.1 = Th.detId B.host (Th.stdL B.host n) L := rfl
  have hl : TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host n) L) =
      ((TaylorLogMetric.chiQ (I.rec7 l Z) ((I.rec7 l Z).relDet n S0 L1) : ℂˣ) : ℂ) := by
    rw [← e, ← h2, TaylorLogMetric.chiRec_idl _ _ hidl.1]
  rw [hl]
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective ((I.rec7 l Z).relDet n S0 L1)
  rw [← ht]
  have hχ := I.C.isChi
  have hK := (GlobalTheory.Mem.KerDet.kernel_open_and_factor B.R B.host).2.2.2 I.C.chiPsi hχ.triv (fun v y hy _ => hχ.unr v y hy)
    fun v _ => hχ.unr v
  have hr : (QuotientGroup.mk (toDtT B.host I.SQ t) : DtT B.host ⧸ UOT B.host) = relDetT B.host n (Th.stdL B.host n) L := by
    have h1 := toDtTMod_mk B.host I.SQ (t : DtQ B.host I.SQ)
    have h3 := toDtTMod_relDetQ B.host I.SQ n (Th.stdL B.host n) L
    have h6 : (QuotientGroup.mk (t : DtQ B.host I.SQ) : DtQ B.host I.SQ ⧸ UOQ B.host I.SQ) = relDetQ B.host I.SQ n (Th.stdL B.host n) L := ht
    rw [← h1, h6, h3]
  have h5 : ((tildeQ B.host I.SQ I.C.chiPsi t : ℂˣ) : ℂ) = ((tildeD B.host I.C.chiPsi (toDtT B.host I.SQ t) : ℂˣ) : ℂ) := by
    rw [tildeQ_eq_comp B.host I.SQ hK]; rfl
  exact h5.trans (GlobalTheory.Mem.ChiDet.tildeD_eq_chiId B.R B.host I.C.chiPsi hχ n L ⟨hL.1, hL.2.1⟩ _ hr)
end GlobalTheory.ColRows.FldDef

namespace GlobalTheory.ColRows.FldDef
open GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

theorem fieldOfDefinition_congr {B : Base} (J : AmbIn B.host) (χ₁ χ₂ : Submodule (𝓞 B.host.E) B.host.E → ℂ)
    (hχ : ∀ (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)), Formalism.L2.Col.IsSdLat (E := B.fields.E) L →
      χ₁ (Th.detId B.host (Th.stdL B.host n) L) = χ₂ (Th.detId B.host (Th.stdL B.host n) L))
    {Pr : Primes B.fields} {R : Ranks} (W : Formalism.L2.Col.Wts B.fields Pr.Word R)
    (sel : HeightOneSpectrum (𝓞 B.fields.F) → HeightOneSpectrum (𝓞 B.fields.E)) {Sg : Set ℕ}
    (mu : Tup B.fields.F B.fields.E B.fields.K Sg) (cst : LocCst B.fields (rowSG Pr sel mu)) (u : Pr.Word) :
    FieldOfDefinition W sel mu cst u (J.amb B χ₁) → FieldOfDefinition W sel mu cst u (J.amb B χ₂) := by
  intro h i hi L L' c x hR e hdeg
  obtain ⟨y, hy⟩ := h i hi L L' c x hR e hdeg
  have hc : Th.chiFac B.host χ₁ (R.N i) (R.N (i + 1)) L L' = Th.chiFac B.host χ₂ (R.N i) (R.N (i + 1)) L L' := by
    unfold Th.chiFac
    rw [hχ _ L hR.1, hχ _ L' hR.2.1]
  have he : (J.amb B χ₁).e (R.N i) (R.N (i + 1)) L L' = (J.amb B χ₂).e (R.N i) (R.N (i + 1)) L L' := by
    funext z
    show Th.chiFac B.host χ₁ _ _ L L' * _ = Th.chiFac B.host χ₂ _ _ L L' * _
    rw [hc]
  have hth : (J.amb B χ₁).thInd (Sall sel mu u) L L' c x = (J.amb B χ₂).thInd (Sall sel mu u) L L' c x := by
    unfold Amb.thInd
    rw [he]
    rfl
  refine ⟨y, hy.trans ?_⟩
  rw [hth]
  show (Th.chiFac B.host χ₁ _ _ L L')⁻¹ * _ = (Th.chiFac B.host χ₂ _ _ L L')⁻¹ * _
  rw [hc]
  rfl
end GlobalTheory.ColRows.FldDef

open GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds in

theorem GlobalTheory.ColRows.fieldOfDefinition_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → ∀ u a, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.FieldOfDefinition W t.sel (t.tup a) (t.cst a) (t.word u) t.amb := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W hJ hS hW u a
  obtain ⟨-, -, -, hFD⟩ := GlobalTheory.Core.Ht2.analyticTies_trueCols I hOk (GlobalTheory.Mem.Col2.base_fields_primes_ok B X).1 l Z hJ
  have hχ : ∀ (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)), Formalism.L2.Col.IsSdLat (E := B.fields.E) L →
      I.chi (Th.detId B.host (Th.stdL B.host n) L) = t.χ (Th.detId B.host (Th.stdL B.host n) L) := fun n L hL => by
    have h1 := GlobalTheory.ColRows.FldDef.chiRec_detId I l Z t.idl_ok n L (GlobalTheory.ColRows.FldDef.sd_of_isSdLat hL)
    have h2 := congrFun t.χ_rec (Th.detId B.host (Th.stdL B.host n) L)
    exact h1.symm.trans h2.symm
  have hF : ∀ (u' : (B.primes X).Word) (a' : I.ι), FieldOfDefinition (Pr := B.primes X) B.wts I.sel (I.tup a') (I.cst a') u' (I.J.amb B t.χ) :=
    fun u' a' => by
      have h3 := GlobalTheory.ColRows.FldDef.fieldOfDefinition_congr (R := B.R) I.J I.chi t.χ hχ B.wts I.sel (I.tup a') (I.cst a') u'
      have h4 : FieldOfDefinition (Pr := B.primes X) B.wts I.sel (I.tup a') (I.cst a') u' (I.J.amb B I.chi) := hFD u' a'
      exact h3 h4
  clear hFD hχ
  obtain ⟨hX, -, hPr, -, hsel, hS', hword, htup, hcst, -, -, -, hamb, -, -⟩ := hS
  cases t
  subst hX
  obtain rfl := eq_of_heq hPr
  subst hS'
  obtain rfl := eq_of_heq hsel
  obtain rfl := eq_of_heq htup
  obtain rfl := eq_of_heq hcst
  obtain rfl := eq_of_heq hword
  obtain rfl := eq_of_heq hW
  have hamb' := eq_of_heq hamb
  rw [hamb']
  exact hF u a
