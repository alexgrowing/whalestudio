import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem finite_tuples_of_indefiniteSidePoint : Finite p.P.T := by
  have h := p.charW.tup
  refine Finite.of_surjective (fun o : Option p.R.twPl => o.elim p.P.A3.A.μ0 fun w => p.R.mu w) fun t => ?_
  rcases h.mu_used t with rfl | ⟨w, rfl⟩
  · exact ⟨none, rfl⟩
  · by_cases hw : w ∈ p.R.twPl
    · exact ⟨some ⟨w, hw⟩, rfl⟩
    · exact ⟨none, (h.mu_off w hw).symm⟩

theorem ray_zero {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] (φ : K →+* M) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ 0 := fun P h => absurd (by simp) h

theorem tupLevel_ne (t : p.P.T) : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel (R2 p) t ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    (Finset.prod_ne_zero_iff.2 fun q hq => ?_)
  obtain ⟨PP, -, rfl⟩ := Finset.mem_image.1 hq
  have : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  exact Nat.card_pos.ne'

theorem twisted_iff (w : D.what₂.places.Pl) : D.plEq w ∈ p.R.twPl ↔ TwistedAt D w := by
  have h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 := by
    rw [← p.P.div.tup.mu0]; exact p.tupT_tup _
  refine ⟨fun hw e => p.charW.tup.mu_ne _ hw ?_, fun hw => ?_⟩
  · rw [← p.tupAt w, e, h0]
  · by_contra hn
    apply hw
    have e := p.charW.tup.mu_off _ hn
    rw [← p.tupAt w] at e
    rw [← p.tupTie _ (Or.inr ⟨w, rfl⟩), e]
    exact p.P.div.tup.mu0

theorem ownAt_ne (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ownAt D v ≠ Formalism.EigenvalueLevelCeiling.plc v := by
  unfold ownAt
  split_ifs with h
  · rw [h]; exact D.host.pde_ne.symm
  · exact fun e => h e.symm

theorem chi_eq (Z : GlobalTheory.SeriesTie.ExportTie p.nexp p.v₀) (h : LevelIs D.nexp (p.R.eG.trans p.cG) p.P.P0 p.P.ψ0⁻¹)
    (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (u : p.P.P0) :
    ∃ hu, (((Z.ρ.B i j b).G.P.chi ⟨Z.ρ.eG i j b ((p.R.eG.trans p.cG) u), hu⟩ : ℂˣ) : ℂ) =
      (D.what₂.embLL (p.P.ψ0 u : D.what₂.LLˣ))⁻¹ := by
  have hU := (h.1 u).2 u.2
  obtain ⟨x, hx, hy⟩ := h.2 i b u hU
  refine ⟨((Z.tie i j b).U_eq _).2 hU, ?_⟩
  have e := (Z.tie i j b).psiU_eq ⟨_, hU⟩ (((Z.tie i j b).U_eq _).2 hU)
  rw [e, hy, Z.good.e_LL0]
  change D.what₂.embLL (x : D.what₂.LL) = _
  rw [hx, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]

theorem err_nonneg (w) (j) : 0 ≤ (p.S false).err0 w j := by
  rw [show (p.S false).err0 w j = _ from p.err_eq w j]
  have := ramw_pos w
  unfold errCan
  positivity

theorem twoRunDatum_boundUnit_at_indefinitePoint {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (r : TwoRuns p.T p.P.Gp) {c : OnConst} (O : Obj p c)
    (h : RecAt p Tp r O) (C CH : ℝ) : ErrorConstantMatchesDefinition ((R2 p).num (F2 p) C CH) O C ∧ O.b = L.sc.b := by
  obtain ⟨st, hd⟩ := h.1.depth
  letI := hostAlg D
  have hb : O.b = L.sc.b := by
    unfold OnObj.b OnObj.xe
    rw [hd.x_eq, hd.eps_eq]; rfl
  refine ⟨fun j => ?_, hb⟩
  change C * (L.sc.x ^ L.sc.eps * ((D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.x ^ L.sc.eps + L.Nc)) = C * O.E1u
  unfold OnObj.E1u OnObj.B0
  rw [L_eq, hb, h.1.Nc_eq, hd.f_eq, hd.m_eq]
  unfold OnObj.xe
  rw [hd.x_eq, hd.eps_eq]

theorem not_on_zero (CH : ℝ) (j) (w₀) (hw : w₀ ∈ (p.S false).Tw) (he : 0 < (p.S false).err0 w₀ j)
    (hJ : ∀ w ∈ (p.S false).Tw, 0 ≤ (p.N 0 CH).J0 ((p.S false).μ w) w j) : ¬ (p.S false).ON (p.N 0 CH) := by
  intro h
  have h3 := h.2.2 j
  have e : (p.N 0 CH).E1 j = 0 := zero_mul _
  rw [e] at h3
  refine absurd h3 (not_le.2 (Finset.sum_pos' (fun w hw' => ?_) ⟨w₀, hw, ?_⟩))
  · have := (lw_pos w).le
    have := (ramw_pos w).le
    have := err_nonneg p w j
    have := hJ w hw'
    positivity
  · have := lw_pos w₀
    have := ramw_pos w₀
    have := hJ w₀ hw
    positivity

end GlobalTheory.BigOn.Check

end
