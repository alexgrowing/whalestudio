import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteVertexClassesCardLePrincipalCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.ClassCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

set_option maxHeartbeats 2000000 in

theorem finCl_mk_eq_iff (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (a b : GfC V) :
    DoubleCoset.mk (ratFin V) (K.comap (finG V)) a = DoubleCoset.mk (ratFin V) (K.comap (finG V)) b ↔
      (DoubleCoset.mk (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) (GlobalTheory.DefFree.finU V a.1) :
        Cl D.sp.cm V.gram K) = DoubleCoset.mk _ _ (GlobalTheory.DefFree.finU V b.1) := by
  rw [DoubleCoset.eq, DoubleCoset.eq]
  constructor
  · rintro ⟨γ, hγ, k, hk, rfl⟩
    have hγ' : finG V γ ∈ (GQ V).map (Lev.finE V) := hγ
    obtain ⟨γ0, hγ0, e0⟩ := hγ'
    refine ⟨GlobalTheory.DefFree.finU V γ.1, ?_, GlobalTheory.DefFree.finU V k.1, ?_, ?_⟩
    · have : GlobalTheory.DefFree.finU V γ.1 = GlobalTheory.DefFree.finU V γ0 := Subtype.ext e0.symm
      rw [this]
      exact GlobalTheory.DefFree.AdelCls.rat_mem V γ0 hγ0
    · exact Subgroup.mem_subgroupOf.2 hk
    · simp only [Subgroup.coe_mul, map_mul]
  · rintro ⟨q, hq, k, hk, e⟩
    have hq' : q ∈ (GQ V).map (GlobalTheory.DefFree.finU V) := by rw [GlobalTheory.DefFree.AdelCls.map_rat]; exact hq
    obtain ⟨γ0, hγ0, rfl⟩ := hq'
    obtain ⟨γ1, hγ1, e1⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V (GlobalTheory.DefFree.finU V γ0)
    obtain ⟨κ, hκ, e2⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V k
    refine ⟨⟨γ1, hγ1⟩, ?_, ⟨κ, hκ⟩, ?_, ?_⟩
    · refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨γ0, hγ0, ?_⟩)
      exact (congrArg Subtype.val e1).symm
    · refine Subgroup.mem_comap.2 ?_
      have := Subgroup.mem_subgroupOf.1 hk
      rw [← e2] at this
      exact this
    · apply Subtype.ext
      have hx : (b.1)⁻¹ * (γ1 * a.1 * κ) ∈ GinfC V := by
        rw [← GlobalTheory.DefFree.AdelCls.finU_eq_one_iff, MonoidHom.map_mul, MonoidHom.map_inv, MonoidHom.map_mul, MonoidHom.map_mul,
          e1, e2, e]
        exact inv_mul_cancel _
      have hy : (b.1)⁻¹ * (γ1 * a.1 * κ) ∈ GfC V :=
        (GfC V).mul_mem ((GfC V).inv_mem b.2) ((GfC V).mul_mem ((GfC V).mul_mem hγ1 a.2) hκ)
      exact inv_mul_eq_one.1 (GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V hy hx)

theorem card_finCl_eq (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) :
    Nat.card (FinCl V K) = Nat.card (Cl D.sp.cm V.gram K) := by
  let f : FinCl V K → Cl D.sp.cm V.gram K := Quotient.lift
    (fun x : GfC V => (DoubleCoset.mk (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) (GlobalTheory.DefFree.finU V x.1) :
      Cl D.sp.cm V.gram K))
    (fun a b h => (finCl_mk_eq_iff V K a b).1 ((DoubleCoset.eq'' _ _).2 h))
  refine Nat.card_eq_of_bijective f ⟨fun c c' h => ?_, fun c => ?_⟩
  · induction c using Quotient.inductionOn with | h a => ?_
    induction c' using Quotient.inductionOn with | h b => ?_
    exact (finCl_mk_eq_iff V K a b).2 h
  · induction c using Quotient.inductionOn with | h x => ?_
    obtain ⟨h, hh, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V x
    exact ⟨DoubleCoset.mk _ _ (⟨h, hh⟩ : GfC V), by
      show (DoubleCoset.mk _ _ (GlobalTheory.DefFree.finU V h) : Cl D.sp.cm V.gram K) = _
      rw [e]⟩

theorem card_clPlus_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U →
    (Nat.card G.ClPlus : ℝ) ≤ hBd D (G.V (.top 0)).rank * (Ideal.absNorm G.modul : ℝ) ^ ((G.V (.top 0)).rank ^ 2) := by
  intro D T L sc G U hS
  have h := GlobalTheory.T.definiteVertexClasses_card_le_principalCongruence G hS (.top 0) (Nat.zero_le _) G.modul (G.pl.modul_ne_bot sc) G.Kplus le_rfl
  rw [card_finCl_eq] at h
  exact h

end GlobalTheory.ClassCount

end
