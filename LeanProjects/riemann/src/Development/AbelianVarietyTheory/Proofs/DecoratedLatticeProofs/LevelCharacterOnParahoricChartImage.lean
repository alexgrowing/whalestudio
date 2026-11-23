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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopologicalIsoParahoricChartSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainChartParahoricEqLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ChartChi

set_option maxHeartbeats 2000000 in

theorem levChi_chart : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t), ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ι hι ξl hξ y hy d hd
  have hlev := (GlobalTheory.chart_level_iff D c w hw j hj s hs PP hPP v φ hφ ι hι y).2 hy
  obtain ⟨hr, hL, hfl⟩ := hs
  obtain ⟨e, he⟩ := GlobalTheory.ChartSplitIso.exists_equiv_emb D s j v φ ι hfl.selfDual hfl.frame hι
  have hv : v = PP.under (𝓞 D.host.F) := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1
  obtain ⟨ε, hε, hch⟩ := hι
  rw [Lev.levG, Lev.mem_levA, hL] at hlev
  have hmem := hlev.2
  rw [mem_lev, mem_parLev] at hmem
  obtain ⟨⟨-, hS, -, hQ⟩, -⟩ := hmem
  have hPc : PP ∈ c.Pg := by
    classical
    rw [hw.union]; exact Finset.mem_union_right _ hPP
  have hone : ∀ PP', PP' ∈ c.Pg → PP' ≠ PP → redFn s.β PP' (Lev.finE s.V (ι y)) = 1 := by
    intro PP' hP' hne
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β _ PP' hS ?_
    have hu : PP'.under (𝓞 D.host.F) ≠ v := by
      intro h
      exact hne (GlobalTheory.LevelPlaces.injOn_under D c hw.com hP' hPc (h.trans hv))
    rw [he y]
    exact GlobalTheory.AdelicU.proj_emb_ne _ _ hu _
  have hsub : ∀ PP', PP' ∈ w.Pg ∨ PP' ∈ w.Q → PP' ∈ c.Pg := by
    classical
    intro PP' h
    rw [hw.union]
    exact Finset.mem_union.2 h
  rw [Lev.levChi, hL]
  set L := Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B with hLd
  have hLxq : L.xq = fun PP => (w.ξ PP)⁻¹ := by rw [hLd]; simp [Lev.datY]
  have hLPg : L.Pg = w.Pg := rfl
  have hLQ : L.Q = w.Q := rfl
  have hLr : L.r = D.R.r := rfl
  set x := Lev.finE s.V (ι y) with hx
  have h1 : ext1 L.P.H (⇑L.P.chi) (rTup s.β L x) = 1 := Lev.subgroupCharExtension_one_apply (LevelP.triv w.Pg D.R.r ℂ).H _
  have h2 : ∏ PP ∈ L.Pg, ∏ c ∈ Finset.range L.s, (L.cg (c + 1) PP) (dBlk (blkOf L.r L.t) (c + 1) (redFn s.β PP x)) = 1 := by
    refine Finset.prod_eq_one fun PP' hP' => Finset.prod_eq_one fun c' _ => ?_
    have hne : PP' ≠ PP := by
      rintro rfl
      exact Finset.disjoint_left.1 hw.disj hP' hPP
    rw [hone PP' (hsub _ (Or.inl hP')) hne, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  have h3 : ∏ PP ∈ L.Q, (L.xq PP) (dBlk (blk2 L.r) 1 (redFn s.β PP x)) = (L.xq PP) (dBlk (blk2 L.r) 1 (redFn s.β PP x)) := by
    refine Finset.prod_eq_single PP (fun PP' hP' hne => ?_) (fun h => absurd hPP h)
    rw [hone PP' (hsub _ (Or.inr hP')) hne, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  unfold levFn
  rw [h1, h2, h3, one_mul, one_mul, hLxq]
  obtain ⟨⟨rr, -, -, hrel, hN⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφ
  have hQP : redFn s.β PP x ∈ blockTri (blk2 D.R.r) := hQ PP hPP
  obtain ⟨Y, hY⟩ := hS
  set G := (grpCo φ s.V (frCo φ s.β) (ι y)).val with hG
  have hi : intGL D.host.F D.host.E _ Y = s.β⁻¹ * x * s.β := by
    rw [← hY]
    simp [frGL, MulAut.conj_apply]
    group
  have hxm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) x =
      Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom s.V (ι y)) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (x.val i j) = rdA φ ((Formalism.L2.Theta.matHom s.V (ι y)).val i j)
    exact GlobalTheory.SplitProjChart.rdE_toEAf φ _
  have hm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (s.β⁻¹ * x * s.β) = grpCo φ s.V (frCo φ s.β) (ι y) := by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, hxm]
    rfl
  have key : ∀ a b, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((Y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) = G a b := by
    intro a b
    rw [hG, ← hm, ← hi]
    rfl
  have hint : ∀ a b, G a b ∈ v.adicCompletionIntegers D.host.F := fun a b => key a b ▸ (hN _ (Y.val a b).2).1
  have hred : ∀ a b, rr ⟨G a b, hint a b⟩ = (redFn s.β PP x).val a b := by
    intro a b
    obtain ⟨h, hh⟩ := hN _ (Y.val a b).2
    rw [← hY, redFn_frGL]
    have e : (⟨G a b, hint a b⟩ : v.adicCompletionIntegers D.host.F) = ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (Y.val a b : Lev.EAf D), h⟩ :=
      Subtype.ext (key a b).symm
    rw [e, hh]
    rfl
  have hT : ∀ i : Blocks j D.R.t, blk2 D.R.r (ε (.inr i)) = 1 := by
    intro i
    have := GlobalTheory.ChartLevel.eps_inr_ge ε hε i
    simp [blk2, not_lt.2 this]
  let f : Blocks j D.R.t → {a : Fin s.V.rank // blk2 D.R.r a = 1} := fun i => ⟨ε (.inr i), hT i⟩
  have hfb : Function.Bijective f := by
    constructor
    · intro i i' h
      have := congrArg Subtype.val h
      exact Sum.inr_injective (ε.injective this)
    · rintro ⟨a, ha⟩
      obtain ⟨p, rfl⟩ := ε.surjective a
      rcases p with p | p
      · exfalso
        have hp : ((ε (.inl p) : Fin s.V.rank) : ℕ) < D.R.r := by rw [hε]; exact p.2
        simp [blk2, hp] at ha
      · exact ⟨p, rfl⟩
  let ef := Equiv.ofBijective f hfb
  let Gi : Matrix (Fin s.V.rank) (Fin s.V.rank) (v.adicCompletionIntegers D.host.F) := fun a b => ⟨G a b, hint a b⟩
  let A : Matrix {a : Fin s.V.rank // blk2 D.R.r a = 1} {a : Fin s.V.rank // blk2 D.R.r a = 1} (v.adicCompletionIntegers D.host.F) :=
    Gi.submatrix Subtype.val Subtype.val
  have hdA : (d : Fv D.host.F v) = ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) := by
    rw [hd]
    have e1 : ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) =
        (G.submatrix (Subtype.val : {a : Fin s.V.rank // blk2 D.R.r a = 1} → Fin s.V.rank) (Subtype.val : {a : Fin s.V.rank // blk2 D.R.r a = 1} → Fin s.V.rank)).det := by
      rw [show ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) = (v.adicCompletionIntegers D.host.F).subtype A.det from rfl,
        RingHom.map_det]
      congr 1
    rw [e1, ← Matrix.det_submatrix_equiv_self ef]
    congr 1
    refine Matrix.ext fun i i' => ?_
    have := congrFun (congrFun (hch y).2 (.inr i)) (.inr i')
    exact this.symm
  have hk : ((dBlk (blk2 D.R.r) 1 (redFn s.β PP x) : (kP PP)ˣ) : kP PP) = rr A.det := by
    rw [diag_block_det_val 1 hQP, RingHom.map_det]
    congr 1
    ext a b
    exact (hred a b).symm
  have hrel' : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (d : Fv D.host.F v) ((dBlk (blk2 D.R.r) 1 (redFn s.β PP x) : (kP PP)ˣ) : kP PP) := by
    rw [hrel]
    refine ⟨hdA ▸ A.det.2, ?_⟩
    rw [hk]
    congr 1
    exact Subtype.ext hdA
  have hξd := hξ d _ hrel'
  show ((((w.ξ PP)⁻¹) (dBlk (blk2 D.R.r) 1 (redFn s.β PP x)) : ℂˣ) : ℂ) = _
  rw [MonoidHom.inv_apply, hξd]

end GlobalTheory.ChartChi
