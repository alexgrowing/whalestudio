import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunUniformisationComponentsShareCmDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunUniformisationCharacterTrivialArithmeticGStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservedByComponentStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelGroupTransportUniformisationComponentStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Build

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem exists_runModel (p : PtAt ex Csz) (hm : More p) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (ho : OwnPin r)
    (i : Fin D.R.m) : ∃ (C : Type) (_ : Finite C) (_ : MulAction p.P.Gp C) (M : TwoLevels D.host.E D.R.r p.P.Gp C)
      (ka : Wt M.Ψ D.R.r), RunModel p r h i M ka := by
  classical
  obtain ⟨v⟩ := nonempty_place D
  have hne : Nonempty (uAt r v i).Comp := GlobalTheory.ModelLatticeCheck.comp_nonempty _ _ _
  have hcom := GlobalTheory.T.uniformisation_components_share_cmData p hm r h ho i v
  have hchi := GlobalTheory.T.uniformisation_character_trivial_arithmeticGroup p hm r h ho i v
  have hcong := GlobalTheory.T.lattice_preserved_by_component_stabilizer p hm r h ho i v
  obtain ⟨act, tr, h1, hmul, hmt, hconj, hcoc, hfaith, ⟨a, ha⟩, hd2⟩ := GlobalTheory.T.exists_levelGroup_transport_uniformisation_components p hm r h ho i v
  choose Xx hXd hXL using exists_dataX_latP p r h i v
  have hΓ : ∀ c, (Xx c).Γ = ((uAt r v i).X c).Γ := fun c => congrArg Data.Γ (hXd c)
  have hΛ : ∀ c, (Xx c).Λ = ((uAt r v i).X c).Λ := fun c => congrArg Data.Λ (hXd c)
  let k0 : (uAt r v i).Comp := hne.some
  letI inst : MulAction p.P.Gp (uAt r v i).Comp := { smul := act, one_smul := h1, mul_smul := hmul }
  let M : TwoLevels D.host.E D.R.r p.P.Gp (uAt r v i).Comp :=
    { Ψ := ((uAt r v i).X k0).Ψ
      Gm := ((uAt r v i).X k0).Gm
      p0 := ((uAt r v i).X k0).p0
      ξ0 := ((uAt r v i).X k0).ξ0
      comp := Xx
      comp_Ψ := fun c => (congrArg Data.Ψ (hXd c)).trans (hcom c k0).1
      comp_Gm := fun c => (congrArg Data.Gm (hXd c)).trans (hcom c k0).2.2.1
      comp_basePoint := fun c => (congrArg Data.p0 (hXd c)).trans (hcom c k0).2.1
      comp_ξ0 := fun c => (congrArg Data.ξ0 (hXd c)).trans (hcom c k0).2.2.2
      χ_one := fun c => chi_one_of_toData (Xx c) _ (hXd c) (hchi c)
      Γ_L' := fun c γ hγ w => by
        rw [hXL c]
        rw [hΓ c] at hγ
        exact mem_localLattice_iff_mulVec D _ (((uAt r v i).X c).Γ_stab γ hγ).2 w
      tr := tr
      tr_herm := fun u c w w' => by
        have e := (hmt u c).iso w w'
        rw [(hcom (act u c) k0).2.2.1, (hcom c k0).2.2.1] at e
        exact e
      tr_Λ := fun u c w => by
        rw [hΛ c, hΛ (u • c)]
        exact (hmt u c).lat w
      tr_L' := fun u c w => by
        rw [hXL c, hXL (u • c)]
        exact mem_localLattice_iff_mulVec D _ (hmt u c).lat w
      tr_conj := fun u c γ => by
        rw [hΓ c, hΓ (u • c)]
        exact hconj u c γ
      tr_mul := fun u u' c => by
        rw [hΓ]
        exact hcoc u u' c
      tr_faithful := fun u c hu ht => hfaith u c hu (by rw [hΓ c] at ht; exact ht) }
  let ka : Wt M.Ψ D.R.r := fun τ j => laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k0 τ j
  refine ⟨(uAt r v i).Comp, inferInstance, inst, M, ka, v, Equiv.refl _, fun c => hXd c, ?_, ⟨a, ?_⟩, ?_, ?_⟩
  · intro c τ h1 h2 j
    show laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k0 ⟨τ, h1⟩ j = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) c ⟨τ, h2⟩ j
    unfold laR laU
    rw [(hcom c k0).2.1]
  · intro F g c x hx h1 h2
    have hx' : castFrame h1 x ∈ ((uAt r v i).X c).dom := by
      show castFrame h1 x ∈ GG ((uAt r v i).X c).Ψ ((uAt r v i).X c).Gm ((uAt r v i).X c).p0
      rw [(hcom c k0).2.2.1, (hcom c k0).2.1]
      exact fun τ => hx ⟨τ.1, by rw [h1]; exact τ.2⟩
    have e := ha F g c (castFrame h1 x) hx' (h1.symm.trans h2)
    exact e
  · intro c γ hγ w hw
    rw [hXL c] at hw ⊢
    rw [hΓ c] at hγ
    exact hcong c γ hγ w hw
  · exact hd2 (fun c => (Xx c).L') hXL

end Build

end GlobalTheory.ShareOn

end
