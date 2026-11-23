import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Formalism.SharpRestriction.LevelLetterCocycles.ThetaScalarFamilyOfEigenvalue
import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExtNRowsGen

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module

namespace Formalism.L2.N.ExtNRows3

open Formalism.L2.N.ExtNRows

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

theorem finrank_Mj_eq_dW (P : RowSideFamily ex) (i : Fin D.R.m) :
    finrank ℂ (D.what₂.Mj ((i : ℕ) + 1)) = P.S0.dW i := by
  have th := P.tied.div.th
  have := Module.finrank_eq_card_basis (Module.Basis.mk (th.li i) (th.span i).ge)
  rw [this, Fintype.card_fin]
  rfl

section Pin

variable (T : TiedDataSK ex) (P : RowSideFamily ex) (hp : RowSideDetermined T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)

include h in

theorem wf0 : (P.A3.side3 P.P0 P.ψ0 P.Zs).WF := by
  obtain ⟨s, hs⟩ := h.famOk
  exact P.A3.side_well_formed hs _ _ _ h.zsSt h.zsBl h.famSep

include h in
theorem dW_eq_D (i : Fin D.R.m) : P.S0.dW i = P.S0.D := by
  obtain ⟨R0, hR0⟩ := h.rows0
  exact hR0 ▸ R0.dW_eq (wf0 P h) i

include h in
theorem Ep_decomp : iSupIndep P.S0.Ep ∧ (⨆ p, P.S0.Ep p) = ⊤ := by
  obtain ⟨R0, hR0⟩ := h.rows0
  exact hR0 ▸ R0.Ep_decomp (wf0 P h)

include hp hL h in
open Classical in

theorem base_rows_eq_record_rows : P.S0.D = D.what₂.D0 := by
  obtain ⟨cOf, -, -, h3⟩ := hL
  have e1 := sum_finrank P.S0.Ep (Ep_decomp P h).1 (Ep_decomp P h).2
  rw [Module.finrank_fin_fun] at e1
  have e2 : ∑ c, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = c), D.what₂.nRows0 σ = ∑ σ, D.what₂.nRows0 σ :=
    Finset.sum_fiberwise _ _ _
  have e3 : ∑ σ, D.what₂.nRows0 σ = D.what₂.D0 := by
    unfold Rows.Data.nRows0
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.what₂.ft0), Fintype.card_fin]
  rw [← e1, ← e3, ← e2]
  exact Finset.sum_congr rfl fun c _ => (h3 c).symm

include hp hL h in

theorem finrank_Mj_of_pin : ∀ j, 1 ≤ j → j ≤ D.R.m → finrank ℂ (D.what₂.Mj j) = D.what₂.D0 := by
  intro j h1 h2
  have hM := finrank_Mj_eq_dW P ⟨j - 1, by omega⟩
  have hj : ((⟨j - 1, by omega⟩ : Fin D.R.m) : ℕ) + 1 = j := by
    show j - 1 + 1 = j
    omega
  rw [hj] at hM
  rw [hM, dW_eq_D P h, base_rows_eq_record_rows T P hp hL h]

end Pin

theorem thetaP_surj (P : RowSideFamily ex) (h : RowsHold0_3 P)
    (hR : Formalism.L2.DIV.DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (i : Fin D.R.m) (t : P.T)
    (hl : Function.Surjective (lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec) :
    Function.Surjective (D.what₂.thetaP (P.I.tup t) ((i : ℕ) + 1)) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← P.tied.div.th.span i, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨R0, hR0⟩ := h.rows0
  have hb : Function.Bijective (P.S0.θ i t).mulVec := hR0 ▸ R0.l1c.2.1 i t
  obtain ⟨z, hz⟩ := hb.2 (Pi.single k 1)
  obtain ⟨x, hx⟩ := hl z
  refine ⟨_, (hR.thTheta i t x).trans ?_⟩
  refine congrArg (P.I.jW i) ?_
  exact (congrArg _ hx).trans hz

theorem adjoint_injective {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (A : V →ₗ[ℂ] W) (hA : Function.Surjective A) :
    Function.Injective (LinearMap.adjoint A) := by
  refine (injective_iff_map_eq_zero (LinearMap.adjoint A)).2 fun z hz => ?_
  obtain ⟨v, hv⟩ := hA z
  have h1 := LinearMap.adjoint_inner_left A v z
  rw [hz, inner_zero_left, hv] at h1
  exact inner_self_eq_zero.mp h1.symm

theorem finrank_Zj_of_pin (T : TiedDataSK ex) (P : RowSideFamily ex) (hp : RowSideDetermined T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)
    (hR : Formalism.L2.DIV.DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (i : Fin D.R.m) (t : P.T)
    (hl : Function.Surjective (lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec) :
    Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) ∧
      finrank ℂ (D.what₂.Zj (P.I.tup t) ((i : ℕ) + 1)) = D.what₂.D0 := by
  have hi : Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) :=
    adjoint_injective _ (thetaP_surj P h hR i t hl)
  refine ⟨hi, ?_⟩
  unfold Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj hi]
  exact finrank_Mj_of_pin T P hp hL h _ (Nat.succ_le_succ (Nat.zero_le _)) i.2

end Formalism.L2.N.ExtNRows3

end
