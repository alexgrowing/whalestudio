import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTraceLevelCompatibleProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRows

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.ConjTwist (BaseOf)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceFlatLevel

open GlobalTheory.TraceLevelPf

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem traceLevel_flat (R : RealDat D A Ks) (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)) (hB : B.Good) (hBo : BaseOf R i B)
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c))
    (hU : ∀ g, e g ∈ B.G.P.H ↔ g ∈ U)
    (hchi : ∀ (u : U) (hu : e u ∈ B.G.P.H), ((B.G.P.chi ⟨e u, hu⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ u : D.what₂.LLˣ) : D.what₂.LL))
    (τ : Twist D Circle) (hτ : τ.Good) (hQ : B.admitted τ.Q) (ω : PairRep (Vc D i) (Wc D i)) (hω : B.IsWeil τ.chi ω)
    (hh : GA D (Vc D i)) (P : PolF D (Wc D i).rank (Vc D i).rank) :
    levelTrace R i U ψ (series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P) = series B.F ω (B.vecFlat τ) hh P := by
  classical
  have hW : IsWeilDatumO B.F.ψ (Vc D i) (Wc D i) _ _ ω := hω
  have hlift := fun g => exists_lift_datWp hB hBo e hent g
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  have hQ' : (GlobalTheory.FlatVecSum.princ B).admitted τ.Q := hQ
  have hfθ : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
      (Base.isThetaAt_vecAt (GlobalTheory.FlatVecSum.princ_good hB) hQ' _) hB.frame.vac.2.theta
  have hsum : B.vecFlat τ = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) •
      ω (1, (hlift (e.symm p)).choose) ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) :=
    GlobalTheory.FlatVecSum.vecFlat_eq_sum_princ hB (D.sp.V_sig _) hτ hQ hω (fun p => (hlift (e.symm p)).choose) (fun p => by
      have := lifts_of_datWp hBo e hent (hlift (e.symm p)).choose_spec
      rwa [MulEquiv.apply_symm_apply] at this)
  funext x
  have hL : levelTrace R i U ψ (series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P) x =
      ∑ g, (if hg : g ∈ U then D.what₂.embLL (((ψ ⟨g, hg⟩)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0) *
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P (x * (hlift g).choose) := by
    unfold levelTrace gaL
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    show Lev.actG0 _ _ _ _ _ x = _
    rw [Lev.actG0]
    split_ifs with hk
    · rw [GlobalTheory.CuspMult.EqCut.levChi_flag rfl rfl, inv_one]
      exact one_mul _
    · exact absurd (hlift g) hk
  have hR : series B.F ω (B.vecFlat τ) hh P x = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) *
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P (x * (hlift (e.symm p)).choose) := by
    rw [hsum, GlobalTheory.SpecFac.series_sum hB ω _ _ _ (fun p _ => hW.om_pres _ _ hfθ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [series_om_fin hB hW hfθ hh P x (hlift (e.symm p)).choose_spec.1]
  rw [hL, hR]
  symm
  refine Fintype.sum_of_injective (fun p : B.G.P.H => e.symm p) (fun p q hpq => Subtype.ext (e.symm.injective hpq)) _ _
    (fun g hg => ?_) (fun p => ?_)
  · rw [dif_neg, zero_mul]
    intro hgU
    exact hg ⟨⟨e g, (hU g).2 hgU⟩, e.symm_apply_apply g⟩
  · have hp : e.symm p ∈ U := (hU _).1 (by rw [MulEquiv.apply_symm_apply]; exact p.2)
    have key : ((B.G.P.chi p : ℂˣ) : ℂ) = D.what₂.embLL ((ψ ⟨e.symm p, hp⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have hp' : e (e.symm p) ∈ B.G.P.H := by rw [MulEquiv.apply_symm_apply]; exact p.2
      have := hchi ⟨e.symm p, hp⟩ hp'
      have hpe : (⟨e (e.symm p), hp'⟩ : B.G.P.H) = p := Subtype.ext (e.apply_symm_apply p)
      rw [hpe] at this
      exact this
    rw [dif_pos hp, Units.val_inv_eq_inv_val, key, Units.val_inv_eq_inv_val, map_inv₀]

end GlobalTheory.TraceFlatLevel

namespace GlobalTheory.BigOn.Exp.TupLe

theorem traceSt : TraceSt := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm ρ hρ hpin hlev i b ψ ω hψ hQ hω h P
  have hL := GlobalTheory.BigOn.links2_of_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B i j b) := { baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin i j b with }
  refine GlobalTheory.TraceFlatLevel.traceLevel_flat (R2 p) j (ρ.B i j b) (hρ.base i j b) hBo (F2 p).P0 (F2 p).ψ0⁻¹
    ((p.R.eG.trans p.cG).trans (ρ.eG i j b)) (fun g P h h' a c => ?_) (fun g => mem_level_iff hm.2.2 hlev i j b g)
    (fun u hu => ?_) ψ hψ hQ ω hω h P
  · have e1 := hpin.grp i j b (p.cG (p.R.eG g)) P h h' a c
    rw [MulEquiv.symm_apply_apply] at e1
    exact e1
  · refine (level_chi hm.2.2 hρ hlev i j b u hu).1.trans ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rfl

end GlobalTheory.BigOn.Exp.TupLe
