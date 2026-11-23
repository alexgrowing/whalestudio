import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RtrMemOfNorm
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

set_option maxHeartbeats 1000000 in
open GlobalTheory.Core.Mi.CenAct in

theorem GlobalTheory.MiTop.central_isom_ramified : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → ∀ u (d : BotDat W u) z, d.Pin z → ∃ R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ C C₀, IsCol W u C (R φ) → IsCol W u C₀ φ → ∀ ξ, d.B.colForm C₀.1 ξ = rTrans d.a⁻¹ (d.B.colForm C.1 ξ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hB u d z hP
  have hδ : ∀ k : Hfin W.S.X u, (d.B.toH d.a).2 * k = k * (d.B.toH d.a).2 := toH_snd_comm d.B hP.cen
  have hta : d.B.toH d.a = (1, (d.B.toH d.a).2) := Prod.ext (toH_fst d.B hP.fin) rfl
  generalize (d.B.toH d.a).2 = δ at hδ hta
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  let e := Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)
  let col : D.what₂.Mu u →ₗ[ℂ] Cu W.S.X u W.S.Y.hK :=
    e.symm.toLinearMap ∘ₗ (Submodule.inclusion hram) ∘ₗ (D.eMu u).toLinearMap
  have hcol : ∀ φ, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (col φ) =
      ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) := fun φ =>
    congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion hram (D.eMu u φ)))
  let mv : Cu W.S.X u W.S.Y.hK →ₗ[ℂ] Cu W.S.X u W.S.Y.hK :=
    (Formalism.L2.SG.ColDict.rtr W.S.X δ).restrict (fun T hT => rtr_mem_Cu W.S.Y.hK hδ hT)
  have hmv : ∀ T, (mv T).1 = Formalism.L2.SG.ColDict.rtr W.S.X δ T.1 := fun T => rfl
  have hmem : ∀ φ, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)) ∈ (D.mem u).A.Mram := fun φ =>
    GlobalTheory.MiTop.CenIsom.ram_rtr (W.S.tr u) W.S.Y.hK (W.S.lev u) (W.S.into u) (W.S.bij u) δ hδ (col φ) (mv (col φ)) (hmv _) (by rw [hcol]; exact (D.eMu u φ).2)
  let g0 : D.what₂.Mu u →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :=
    Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK ∘ₗ mv ∘ₗ col
  let fL : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u := (D.eMu u).symm.toLinearMap ∘ₗ g0.codRestrict _ hmem
  have hfL : ∀ φ, ((D.eMu u (fL φ) : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) =
      Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)) := fun φ => by
    have h1 : D.eMu u (fL φ) = ⟨Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)), hmem φ⟩ :=
      (D.eMu u).apply_symm_apply _
    rw [h1]
  clear_value fL g0 mv col e
  have hinner : ∀ x y, ⟪fL x, fL y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => by
    refine ((D.eMu_isom u (fL x) (fL y)).trans ?_).trans (D.eMu_isom u x y).symm
    refine (congrArg₂ ((D.fm u).ipC 0) (hfL x) (hfL y)).trans ?_
    refine (GlobalTheory.MiTop.CenIsom.isom_rtr W.S hB.fin u δ hδ (col x) (col y) (mv (col x)) (mv (col y)) (hmv _) (hmv _)).trans ?_
    exact congrArg₂ ((D.fm u).ipC 0) (hcol x) (hcol y)
  let Li := fL.isometryOfInner hinner
  haveI : FiniteDimensional ℂ (D.mem u).A.Mu0 := (D.mem u).A.Mu0_fd
  haveI : FiniteDimensional ℂ (D.mem u).A.Mram := Submodule.finiteDimensional_of_le hram
  haveI : FiniteDimensional ℂ (D.what₂.Mu u) := LinearEquiv.finiteDimensional (D.eMu u).symm
  have hsurj : Function.Surjective Li := (LinearMap.injective_iff_surjective (f := Li.toLinearMap)).1 Li.injective
  refine ⟨LinearIsometryEquiv.ofSurjective Li hsurj, ?_⟩
  intro φ C C₀ hC hC₀ ξ
  have e1 : C = mv (col φ) := (W.S.bij u).1 (hC.trans (hfL φ))
  have e2 : C₀ = col φ := (W.S.bij u).1 (hC₀.trans (hcol φ).symm)
  rw [e1, e2]
  funext g
  simp only [SBes.colForm, rTrans]
  rw [hmv]
  have h4 : d.B.toH (g * d.a⁻¹) * (1, δ) = d.B.toH g :=
    (congrArg (fun y => d.B.toH (g * d.a⁻¹) * y) hta.symm).trans
      ((toH_mul d.B _ _).symm.trans (congrArg d.B.toH (inv_mul_cancel_right g d.a)))
  exact (congrArg ((col φ).1 ξ) h4).symm
