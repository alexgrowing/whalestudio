import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalAtPlaceConjProduct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckePairCount

theorem card_pairs_eq {G : Type} [Group G] (J L : Subgroup G) (x y : G) (A B : Finset G)
    (hθ : ∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧
      (∀ k ∈ J ⊓ L, θ k ∈ J) ∧ ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b)
    (hAL : ∀ a ∈ A, a ∈ L) (hBL : ∀ a ∈ B, a ∈ L) (hA : Bridge.IsDC J x A) (hB : Bridge.IsDC J y B) (c : G ⧸ J) :
    ((A ×ˢ B).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card =
      ((B ×ˢ A).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card := by
  obtain ⟨θ, hL, hm, hi, hK, hdc⟩ := hθ
  by_cases hc : ∃ z ∈ L, (z : G ⧸ J) = c
  · obtain ⟨z, hz, rfl⟩ := hc
    have key : ∀ C E : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ E, a ∈ L) →
        (C ×ˢ E).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = (z : G ⧸ J)) =
          (C ×ˢ E).filter (fun p => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) := by
      intro C E hC hE
      refine Finset.filter_congr fun p hp => ?_
      rw [Finset.mem_product] at hp
      rw [eq_comm, QuotientGroup.eq, QuotientGroup.eq]
      exact ⟨fun h => ⟨h, L.mul_mem (L.inv_mem hz) (L.mul_mem (hC _ hp.1) (hE _ hp.2))⟩, fun h => h.1⟩
    rw [key A B hAL hBL, key B A hBL hAL]
    have e1 := GlobalTheory.DoubleCosetComm.card_pairs (A := A) hB hAL hBL hz
    have e2 := GlobalTheory.DoubleCosetComm.card_pairs (A := B) hA hBL hAL hz
    have e3 := le_antisymm (GlobalTheory.DoubleCosetComm.card_conv_le hm hi hK hL hdc hA hB hAL hz)
      (GlobalTheory.DoubleCosetComm.card_conv_le hm hi hK hL hdc hB hA hBL hz)
    exact e1.trans (e3.trans e2.symm)
  · have key : ∀ C E : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ E, a ∈ L) →
        (C ×ˢ E).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c) = ∅ := by
      intro C E hC hE
      refine Finset.filter_eq_empty_iff.2 fun p hp h => hc ?_
      rw [Finset.mem_product] at hp
      exact ⟨_, L.mul_mem (hC _ hp.1) (hE _ hp.2), h⟩
    rw [key A B hAL hBL, key B A hBL hAL]

set_option maxHeartbeats 1600000 in

theorem side_count {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hβ : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) {Pl0 : Type}
    (pl : Pl0 → Formalism.L2.DIV.Pl D.host.E) (ok : Set Pl0) (Sp : Set (Formalism.L2.DIV.Pl D.host.E))
    (hok : ∀ P, P ∈ ok ↔ Bridge.SplitOff (pl P) Sp) (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ∈ Sp) (i i' : ok × ℕ)
    (hv : (pl i.1).under (𝓞 D.host.F) = (pl i'.1).under (𝓞 D.host.F)) (hi : i.2 ≤ V.rank)
    (x y : Bridge.Gf V) (A B : Finset (Bridge.Gf V)) (hx : isTEnv V pl ok i x)
    (hA : ∀ a ∈ A, isLocEnv V pl ok i a) (hB : ∀ a ∈ B, isLocEnv V pl ok i' a)
    (dA : Bridge.IsDC (levEnv V β L).J x A) (dB : Bridge.IsDC (levEnv V β L).J y B)
    (c : Bridge.Gf V ⧸ (levEnv V β L).J) :
    ((A ×ˢ B).filter (fun p => ((p.1 * p.2 : Bridge.Gf V) : Bridge.Gf V ⧸ (levEnv V β L).J) = c)).card =
      ((B ×ˢ A).filter (fun p => ((p.1 * p.2 : Bridge.Gf V) : Bridge.Gf V ⧸ (levEnv V β L).J) = c)).card := by
  refine (hx hi).elim fun α h0 => h0.1.elim fun e h1 => h1.elim fun ϖ h2 => ?_
  have he := h2.1
  have hsp := (hok _).1 i.1.2
  have hl := GlobalTheory.SplitHeckeAdj.local_group V β Λ L hβ (pl i.1) e he
    fun PP h => GlobalTheory.SplitHeckeAdj.off_of_splitOff hsp PP (hS PP h)
  refine hl.elim fun Lc hl => ?_
  have l1 := hl.1
  have l4 := hl.2.2.2.1
  have hm : ∀ x, isLocEnv V pl ok i x → x ∈ Lc := fun x hx => by
    refine (GlobalTheory.SplitHeckeAdj.loc_supp V hx he).elim fun g hg => ?_
    rw [← hg.2]
    exact l1 g hg.1
  have hm' : ∀ x, isLocEnv V pl ok i' x → x ∈ Lc := fun x hx => by
    refine hm x (GlobalTheory.FrameProdLoc.isLocEnv_of_mem V pl ok i x e he ?_)
    rw [hv]
    exact GlobalTheory.FrameProdLoc.mem_locGrp_of_isLocEnv V pl ok i' x hx
  exact card_pairs_eq (levEnv V β L).J Lc x y A B l4 (fun a ha => hm a (hA a ha)) (fun a ha => hm' a (hB a ha)) dA dB c

set_option maxHeartbeats 1600000 in

theorem card_pairs_comm : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i i' : (blk p j t).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → 1 ≤ i'.2 → i'.2 ≤ (Vc D j).rank → (plOf p j t i.1).under (𝓞 D.host.F) = (plOf p j t i'.1).under (𝓞 D.host.F) → ∀ c : Bridge.Gf (Vc D j) ⧸ levJ p j t, ((hkA p j t i ×ˢ hkA p j t i').filter (fun x => ((x.1 * x.2 : Bridge.Gf (Vc D j)) : Bridge.Gf (Vc D j) ⧸ levJ p j t) = c)).card = ((hkA p j t i' ×ˢ hkA p j t i).filter (fun x => ((x.1 * x.2 : Bridge.Gf (Vc D j)) : Bridge.Gf (Vc D j) ⧸ levJ p j t) = c)).card := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t i i' h1 h2 h1' h2' hv c
  have hb := p.charW.base
  refine hb.fam.tie.elim fun gramR h3 => h3.elim fun c0R h4 => h4.elim fun c0L tie => ?_
  refine (hb.lev.βV j).elim fun c' hc => ?_
  rw [one_pow] at hc
  have main := side_count (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) hc p.R.pl (p.P.A3.A.ok t) _ (tie.ok t)
    (fun PP hP => hP.elim (fun h1 => Or.inl (hb.fam.Sb h1)) Or.inr) i i' hv h2
    ((p.R.B.L j t).hecke.hx i) ((p.R.B.L j t).hecke.hx i') (hkA p j t i) (hkA p j t i')
    ((p.R.B.L j t).hecke.hx_ok i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hA_loc i' ⟨h1', h2'⟩)
    ((p.R.B.L j t).hecke.hDC i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hDC i' ⟨h1', h2'⟩) c
  exact main

end GlobalTheory.HeckePairCount

end
