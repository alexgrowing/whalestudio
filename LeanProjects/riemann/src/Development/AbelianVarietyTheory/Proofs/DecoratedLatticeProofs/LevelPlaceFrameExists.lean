import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFrameHermitianIdeal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselTranslateVector
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZeroStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairCentralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitMultipliersLineInMovedLatticeSplitStatement
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section

namespace GlobalTheory.LineAtG

theorem tOf_fix_first {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (hW : PkHyp W) (hr : 1 ≤ D.R.rS) (u : D.what₂.Word) (f : FamCh W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)) (c : AE D) :
    Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (tOf f B a₀ a)⁻¹) (fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) =
      Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) (fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) := by
  have hId : GlobalTheory.Core.Mi.IdE W.S.X := hW.bot.idE
  set v0 : Fin (D.sp.Y 0).rank → AE D := fun i => Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩
    (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) with hv0
  have hv : (fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) = c • v0 := rfl
  rw [hv]
  set x : GA D (D.sp.Y 0) := (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) with hxdef
  set E : GA D (D.sp.Y 0) := embA B.d B.o (a₀ * a) with hEdef
  set b : GA D (D.sp.Y 0) := (show GA D (D.sp.Y 0) from f.g.b 0) with hbdef
  have hx : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) x) v0 = v0 := by
    refine GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hId {W.S.X.eR ⟨0, hr⟩} _ rfl x ?_
    have e : iotaX W.S.X W.Q.instEq x = (1, W.S.X.xu u) := (iotaX W.S.X W.Q.instEq).apply_symm_apply _
    rw [e]
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (W.S.X.xu_fix u ⟨0, hr⟩).1
  have hE : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) E⁻¹) v0 = v0 := by
    refine GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hId (Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet W.S.X u) (W.S.X.eR ⟨0, hr⟩) (Or.inl (Or.inl ⟨⟨0, hr⟩, rfl⟩)) E⁻¹ ?_
    exact (B.tieH E⁻¹).1 ((embA B.d B.o).range.inv_mem ⟨a₀ * a, rfl⟩)
  have e : (tOf f B a₀ a)⁻¹ = b⁻¹ * (E⁻¹ * x) := by
    show (x⁻¹ * E * b)⁻¹ = _
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e]
  show Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹ * (Formalism.L2.Theta.mt (D.sp.Y 0) E⁻¹ * Formalism.L2.Theta.mt (D.sp.Y 0) x)) (c • v0) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hE]

set_option maxHeartbeats 1600000 in

theorem mem_latLoc_line_iff {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat V) (hL : L.FG) (v : GlobalTheory.FinPl.Pl D) (t : GA D V)
    (ε : Fin V.rank → D.host.E) (y : AE D) (hy : y ∈ GlobalTheory.FinPl.idAt D (· = v)) :
    Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig V.gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v t))⁻¹).val
        (GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y) 0 • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i) ∈
        GlobalTheory.AdelicU.latLoc D.host.F L v ↔
      Matrix.mulVec (Formalism.L2.Theta.mt V t⁻¹) (fun i => y * Formalism.L2.Theta.incA D (ε i)) ∈ GlobalTheory.FinPl.latV V L (· = v) := by
  have hy' : ∀ i, (fun i => y * Formalism.L2.Theta.incA D (ε i)) i ∈ GlobalTheory.FinPl.idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ hy
  rw [GlobalTheory.StMoves.mem_latV_iff_latLoc V L hL v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ t⁻¹ hy'), GlobalTheory.FinPl.KOpen.fin_mulVec,
    GlobalTheory.AdelicU.vecLoc_mulVec, map_inv, map_inv]
  have hv : GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun i => y * Formalism.L2.Theta.incA D (ε i)) =
      GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y) 0 • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i := by
    funext i
    simp only [Function.comp, GlobalTheory.AdelicU.vecLoc, Pi.smul_apply, smul_eq_mul, map_mul]
    congr 1
  rw [hv]

set_option maxHeartbeats 1600000 in

theorem line_atG : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∃ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) = v) → ∃ (e : Fin (D.sp.Y 0).rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) (α : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ), ∀ u (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B → ∀ a₀ a, IsAt f B a₀ a → ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (tOf f B a₀ a)))⁻¹).val (c • e) ∈ GlobalTheory.AdelicU.latLoc D.host.F ((pk W).ΛY 0) v ↔ ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr v hv
  refine ⟨fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)), ?_⟩
  by_cases hex : ∃ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B ∧ ∃ a₀ a, IsAt f B a₀ a
  · obtain ⟨u₀, f₀, B₀, hP₀, b₀₀, b₀₁, hA₀⟩ := hex
    obtain ⟨hτ, hm⟩ : Nonempty (D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ∧ 0 < D.R.m := by
      obtain ⟨PP, hPP, rfl⟩ := hv
      obtain ⟨k, _, _, _, _, ι, v', o, n, G, pl, -, -, -, -, -, hGR, -⟩ := hP₀
      have hs := (G (pl.symm ⟨PP, hPP⟩)).hs
      refine ⟨?_, by omega⟩
      obtain ⟨w, τ, -, hw⟩ := GlobalTheory.AdelicU.Supp.isIdemAt_iff_exists.1 (hGR.idem (pl.symm ⟨PP, hPP⟩)).1
      rw [Equiv.apply_symm_apply] at hw
      change PP = GlobalTheory.AdelicU.splitPrime τ at hw
      subst hw
      rw [GlobalTheory.AdelicU.splitPrime_under]
      exact ⟨τ⟩
    have hΛ := (GlobalTheory.T.self_dual_lattice_frame_chain W hW 0 hm).1
    haveI : Submodule.IsLattice D.host.E ((pk W).ΛY 0) := hΛ.1
    have hfg : ((pk W).ΛY 0).FG := Submodule.IsLattice.fg (A := D.host.E)
    obtain ⟨α, hα⟩ := GlobalTheory.T.exists_unit_multipliers_line_in_movedLattice_split D v hτ _ ((pk W).ΛY 0) hΛ.1
      ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (tOf f₀ B₀ b₀₀ b₀₁)))⁻¹) _ (GlobalTheory.T.firstIsotropicVector_coordinates_ne_zero W.S.X W.Q.instEq hr)
    refine ⟨α, fun u f B hP a₀ a hA c => ?_⟩
    rw [← hα c]
    obtain ⟨y, hy, hyc⟩ := GlobalTheory.StMoves.exists_supp_vecLoc_eq (D := D) (n := 1) v fun _ => c
    have hc : GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y 0) 0 = c := congrFun hyc 0
    rw [← hc]
    refine (mem_latLoc_line_iff (D.sp.Y 0) ((pk W).ΛY 0) hfg v _ (fun i => W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) (y 0) (hy 0)).trans
      (Iff.trans ?_ (mem_latLoc_line_iff (D.sp.Y 0) ((pk W).ΛY 0) hfg v _ (fun i => W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) (y 0) (hy 0)).symm)
    beta_reduce
    rw [tOf_fix_first W hW hr, tOf_fix_first W hW hr]
    exact GlobalTheory.T.placed_bessel_pair_central W hW hr u u₀ f f₀ B B₀ hP hP₀ a₀ a b₀₀ b₀₁ hA hA₀ v hv (y 0) (hy 0)
  · exact ⟨1, fun u f B hP a₀ a hA c => absurd ⟨u, f, B, hP, a₀, a, hA⟩ hex⟩

end GlobalTheory.LineAtG
