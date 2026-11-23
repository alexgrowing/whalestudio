import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLiftTw
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.PStabEq

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLiftInv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl Formalism.MainNotions.G.CmpJ.PCmpLift
  Formalism.MainNotions.G.CmpJ.PCmpLiftDesc Formalism.MainNotions.G.CmpJ.PCmpLiftTw

theorem grp2 {Γ : Type} [Group Γ] (b y k : Γ) (h : y = b * y * k) : b = y * k⁻¹ * y⁻¹ := by
  rw [show y * k⁻¹ * y⁻¹ = (b * y * k) * k⁻¹ * y⁻¹ by rw [← h]]
  group

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

set_option maxHeartbeats 4000000 in

theorem cmpInvRaw_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : CmpInvRawOf S e := by
  intro hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ γ hγ κ hyc y y' hy
  have Hb := H β
  obtain ⟨x, hx⟩ : ∃ x, x = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1 :=
    ⟨_, rfl⟩
  rw [← hx] at hpt
  have hxU : x ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (PStabEq.bc_mem hγ0) ((S.K β).y c).2) (PStabEq.U_le κ0.2)
  have hb : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ =
      ((S.K β).y c).1 * κ.1⁻¹ * ((S.K β).y c).1⁻¹ := grp2 _ _ _ hyc
  have hyU : ((S.K β).y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((S.K β).y c).1 ∈
      (S.K β).lev.U := by
    rw [hb, show ((S.K β).y c).1⁻¹ * (((S.K β).y c).1 * κ.1⁻¹ * ((S.K β).y c).1⁻¹) * ((S.K β).y c).1 = κ.1⁻¹ by group]
    exact (S.K β).lev.U.inv_mem κ.2
  have hδU : γ0 * γ * γ0⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ0 hγ) (Subgroup.inv_mem _ hγ0)
  have hδx : x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x ∈ (S.K β).lev.U :=
    PStabEq.conj_mem' x ((S.K β).y c).1 γ0 γ κ0 hx hyU
  obtain ⟨⟨γ', hfix⟩, hγ'⟩ := (PStabEq.stab_bij Hb.good Hb.int Hb.hypP (X.hypC β) Hb.bad_p Hb.actB Hb.gam Hb.gamU (rep c).1
    (X.inj β _) (X.onto β _) (rep c).2 g hL ⟨x, hxU⟩ hpt).2 ⟨γ0 * γ * γ0⁻¹, hδU, hδx⟩
  have hgam : (S.loc β).gamI (rep c).1 γ' = γ0 * γ * γ0⁻¹ := congrArg Subtype.val hγ'
  obtain ⟨κa, hκa⟩ := awayEx_of Hb.good (S.K β).lev Hb.gam (rep c).1 γ'
  obtain ⟨r, hr, hr1⟩ := Hb.chi (rep c).1 γ' κa hκa

  have hN : natActR (Hc S β).P D.what₂.LL (blkLL (S.loc β) (sigD D) (tEL D) S.pos ((S.loc β).gamI (rep c).1 γ')) Q = r • Q := by
    apply MvPolynomial.map_injective e e.injective
    have h1 := hQ.2 γ' hfix
    rw [actX_map (S.loc β) (tEL D) S.pos e Hb.actB Hb.pos_emb (rep c).1 γ' Q] at h1
    have hr1' : algebraMap G.O G.Kf (((Hc S β).lev (rep c).1).χ γ' : G.O) * e r = 1 := hr1
    rw [mapE_smul e r Q, ← h1, ← algebraMap_smul G.Kf (((Hc S β).lev (rep c).1).χ γ' : G.O), smul_smul, mul_comm (e r), hr1',
      one_smul]

  have e1 : x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x =
      κ0.1⁻¹ * κ.1⁻¹ * κ0.1 := by
    rw [hx, map_mul, map_mul, map_inv, hb]
    group
  have ht : ∀ v ∈ S.bad, bc (prV (E := D.host.E) v) (κa * (κ0⁻¹ * κ * κ0)).1 = 1 := by
    intro v hv
    have hvp := Hb.bad_p v hv
    have a1 := hκa.2 v hvp
    have a2 : bc (prV (E := D.host.E) v) ((S.loc β).yG (rep c).1) = bc (prV (E := D.host.E) v) x := (hpt.1 v hvp).symm
    have key : bc (prV (E := D.host.E) v) κa.1 =
        bc (prV (E := D.host.E) v) (x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x) := by
      rw [a1, hgam]
      simp only [map_mul, map_inv, a2]
    have e2 : (κa * (κ0⁻¹ * κ * κ0)).1 = κa.1 * (κ0.1⁻¹ * κ.1 * κ0.1) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e2, map_mul, key, ← map_mul, e1,
      show κ0.1⁻¹ * κ.1⁻¹ * κ0.1 * (κ0.1⁻¹ * κ.1 * κ0.1) = 1 by group, map_one]
  have hc : ((S.K β).lev.chi κa : ℂ) * ((S.K β).lev.chi κ : ℂ) = 1 := by
    have h0 := congrArg (fun w : ℂˣ => (w : ℂ)) ((S.K β).lev.chi_triv _ ht)
    simp only [map_mul, map_inv, Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val] at h0
    have hne : ((S.K β).lev.chi κ0 : ℂ) ≠ 0 := Units.ne_zero _
    field_simp at h0
    linear_combination h0

  have hz : IsTr (atInf (embT D) ((S.loc β).gamI (rep c).1 γ').1) (foTrR (embT D) γ0 y') (foTrR (embT D) γ0 y) := by
    rw [foIsTr_iff, hgam, (foIsTr_iff (embT D) γ y' y).1 hy, ← foTrR_mul, ← foTrR_mul]
    congr 1
    group
  have hE := evC_blk (S.loc β) (tEL D) S.pos (embT D) D.what₂.embLL (tEL_emb D) ((S.loc β).gamI (rep c).1 γ')
    (unit_of_std (S.loc β).B _ Hb.std (Hb.gamU _ γ')) (gramC (gramN D i hi) (embT D)) _ _ hz Q
  rw [hN, Formalism.L2.G.Cmp.map_smul', map_smul, Pi.smul_apply, smul_eq_mul, hr] at hE
  show _ = ((S.K β).lev.chi κ : ℂ) * _
  linear_combination (((S.K β).lev.chi κ : ℂ)) * hE - (evC (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D))
    (crdB (embT D) (S.loc β).B) (MvPolynomial.map D.what₂.embLL Q) (foTrR (embT D) γ0 y)) * hc

theorem cmpLiftOf_of_evVal (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) : CmpLiftOf S e :=
  cmpLiftOf_of_raw S e hV (cmpInvRaw_holds S e)

theorem invLeOf_of_evVal (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) : InvLeOf S e :=
  invLeOf_of_cmp S e (cmpLiftOf_of_evVal S e hV)

def EvValCAt (S : StepIn M i hi G) (β : S.Ch) : Prop :=
  EvValC (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D)) (atInfGL (embT D) (S.loc β).B⁻¹) (M.lam i)

theorem evValLe_of (S : StepIn M i hi G) (β : S.Ch) (h : EvValCAt S β)
    (hw : WtTie (Hc S β).P (S.loc β).rk S.pos (M.lam i)) : EvValLe S β := by
  intro Q hQ
  rw [← h hw]
  exact Submodule.mem_map_of_mem hQ

theorem cmpLiftOf_of_evValC (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (h : ∀ β, EvValCAt S β) : CmpLiftOf S e := by
  intro hS H X
  exact cmpLiftOf_of_evVal S e (fun β => evValLe_of S β (h β) (H β).wt) hS H X

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

theorem cmpJHyp_of_evVal (c : LatCmp D) {I : CmpJIn Tw u μ w h Lv} (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (iwF : ∀ j hj β, (I.at' j hj).st.IwF β) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (X : ∀ j hj, KAat.ChX (I.at' j hj).st) (hV : ∀ j hj β, EvValLe (I.at' j hj).st β) : CmpJHyp c I :=
  cmpJHyp_of_cmp c Gt hS core ok twUnit valIntN iwF hfin X fun j hj => cmpLiftOf_of_evVal _ _ (hV j hj)

theorem cmpJHyp_of_evValC (c : LatCmp D) {I : CmpJIn Tw u μ w h Lv} (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (iwF : ∀ j hj β, (I.at' j hj).st.IwF β) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (X : ∀ j hj, KAat.ChX (I.at' j hj).st) (hV : ∀ j hj β, EvValCAt (I.at' j hj).st β) : CmpJHyp c I :=
  cmpJHyp_of_cmp c Gt hS core ok twUnit valIntN iwF hfin X fun j hj => cmpLiftOf_of_evValC _ _ (hV j hj)

end Card

end Formalism.MainNotions.G.CmpJ.PCmpLiftInv
