import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.MassDataKppVolOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocKMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.CompPiVLocGSame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.CstNatCastApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Single

noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField IsDedekindDomain
  Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open Formalism.MainNotions.S (AutInst)

theorem index_pi₂ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  classical
  show Nat.card ((∀ i, G i) ⧸ Subgroup.pi Set.univ H) = ∏ i, Nat.card (G i ⧸ H i)
  rw [← Nat.card_pi]
  refine Nat.card_congr (Equiv.ofBijective
    (fun q => Quotient.liftOn' q (fun g i => (QuotientGroup.mk (g i) : G i ⧸ H i)) ?_) ⟨?_, ?_⟩)
  · intro a b hab
    funext i
    rw [QuotientGroup.eq]
    have h1 : a⁻¹ * b ∈ Subgroup.pi Set.univ H := QuotientGroup.leftRel_apply.mp hab
    exact (Subgroup.mem_pi _).mp h1 i (Set.mem_univ i)
  · intro q q' h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
    rw [QuotientGroup.eq, Subgroup.mem_pi]
    intro i _
    exact QuotientGroup.eq.mp (congrFun h i)
  · intro f
    refine ⟨QuotientGroup.mk (fun i => (f i).out), ?_⟩
    funext i
    exact QuotientGroup.out_eq' (f i)

def KsetSub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

theorem mem_KsetSub (I : AutInst) (x : I.Gf) : x ∈ KsetSub I ↔ x ∈ I.Kset := by
  exact Iff.rfl

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def levelSubgroupOfCharacter (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hK.1
  mul_mem' {a b} ha hb := hK.2.1 a ha b hb
  inv_mem' {a} ha := hK.2.2.1 a ha

theorem IP_K2HA_eq : levelUnitary X hb = tf X.B.I hb '' X.K2 := rfl

theorem IP_KppS (hK : X.LevelSubgroupCharacter) : KppS X hb = (levelSubgroupOfCharacter X hK).map (tfHom X.B.I hb) := by
  rw [← Subgroup.closure_eq (levelSubgroupOfCharacter X hK), MonoidHom.map_closure]
  rfl

theorem IP_KfS : KfS X = (KsetSub X.B.I).map (tfHom X.B.I hb) := by
  ext h
  rw [Subgroup.mem_map]
  constructor
  · intro hh
    obtain ⟨x, rfl⟩ := Bridge_tf_surjective X.B.I hb h
    exact ⟨x, (Bridge_mem_Kf_iff X.B.I hb x).1 hh, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (Bridge_mem_Kf_iff X.B.I hb x).2 hx

theorem IP_gIdx (hK : X.LevelSubgroupCharacter) : gIdx X hb = (levelSubgroupOfCharacter X hK).relIndex (KsetSub X.B.I) := by
  rw [gIdx, IP_KppS X hb hK, IP_KfS X hb]
  exact Subgroup.relIndex_map_map_of_injective _ _ (Bridge_tf_injective X.B.I hb)

def KvSub (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :=
  (Kloc p.1 (lamS X)).comap (HR (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J).subtype

theorem IP_KvS (p : TypX X) : KvS X p = KvSub X p := by
  rw [KvS]
  exact Subgroup.closure_eq (KvSub X p)

theorem piV_mem_KvS (p : TypX X) (x : X.B.I.Gf) (hx : x ∈ X.B.I.Kset) :
    piV X.B.I p.1 (tf X.B.I hb x) ∈ KvS X p := by
  rw [IP_KvS]
  have h := (Bridge_mem_Kf_iff X.B.I hb x).2 hx
  rw [Kf, Subgroup.mem_iInf] at h
  exact h p.1

def phiK : KsetSub X.B.I →* ∀ p : TypX X, KvS X p :=
  MonoidHom.pi fun p => MonoidHom.codRestrict
    (((piV X.B.I p.1).comp (tfHom X.B.I hb)).comp (KsetSub X.B.I).subtype) (KvS X p)
    (fun x => piV_mem_KvS X hb p x.1 x.2)

theorem phiK_apply₂ (x : KsetSub X.B.I) (p : TypX X) :
    ((phiK X hb x p : KvS X p) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) = piV X.B.I p.1 (tf X.B.I hb x.1) := rfl

theorem IP_KppvS (hK : X.LevelSubgroupCharacter) (p : TypX X) :
    KppvS X hb p = (levelSubgroupOfCharacter X hK).map ((piV X.B.I p.1).comp (tfHom X.B.I hb)) := by
  rw [KppvS]
  have : compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1 =
      ((levelSubgroupOfCharacter X hK).map ((piV X.B.I p.1).comp (tfHom X.B.I hb)) : Set _) := by
    rw [Subgroup.coe_map, compSet, IP_K2HA_eq, Set.image_image]; rfl
  rw [this, Subgroup.closure_eq]

theorem g_ne_zero₂ (i : Fin 2) : D.host.g i ≠ 0 := (D.host.g_prime i).ne_zero

theorem levelSubgroupAlt_subgroupOf_eq_comap_pi (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) :
    (levelSubgroupOfCharacter X hK).subgroupOf (KsetSub X.B.I) =
      (Subgroup.pi Set.univ fun p => (KppvS X hb p).subgroupOf (KvS X p)).comap (phiK X hb) := by
  ext ⟨z, hz⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, Subgroup.mem_subgroupOf, phiK_apply₂, IP_KppvS X hb hK,
    Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply, Bridge_tfHom_apply]
  constructor
  · intro h p
    exact ⟨z, h, rfl⟩
  · intro h
    have hgc := Cst_gc X.B.I (D.host.g 0) (D.host.g 1) (g_ne_zero₂ (D := D) 0) (g_ne_zero₂ (D := D) 1)
    rw [← X.g_eq] at hgc
    refine LocK_mem X.B.I X.K2 hK.1 hK.2.1 X.B.g (fun x hx => (hL.1 x hx).1) Finset.univ
      (fun p : TypX X => chi X.B.I p.1) (fun p => Comp_chi_idem X.B.I p.1)
      (fun p q hpq => Comp_chi_orth X.B.I p.1 q.1 fun h => hpq (Subtype.ext h))
      (cElt X.B.I (D.host.g 0) (D.host.g 1)) (Cst_int X.B.I _ _) hgc z hz ?_
    intro p _
    obtain ⟨w, hw, hwz⟩ := h p
    rw [Comp_sep X.B.I hb p.1 z w hwz.symm]
    exact LocB_K2set X.B.I _ _ _ _ _ (Comp_chi_idem X.B.I p.1) (Comp_chi_int X.B.I p.1) w hw

theorem phiK_surjective (hS : SngSurj) : Function.Surjective (phiK X hb) := by
  classical
  intro f
  have key : ∀ S : Finset (TypX X), ∃ z : KsetSub X.B.I, ∀ p,
      (phiK X hb z p : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) = if p ∈ S then (f p : _) else 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, fun p => by simp⟩
    | insert q S hq ih =>
      obtain ⟨z, hz⟩ := ih
      have hfq : ((f q : KvS X q) : HA (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J) ∈
          Kv X.B.I.cm.sig X.B.I.J (lamS X) q.1 := by
        have h2 : ∀ x, x ∈ KvS X q → x ∈ Kv X.B.I.cm.sig X.B.I.J (lamS X) q.1 := fun x hx => by
          rw [IP_KvS] at hx; exact hx
        exact h2 _ (f q).2
      obtain ⟨h, hKf, hq1, hq2⟩ := hS X.B.I q.1 _ hfq
      obtain ⟨y, rfl⟩ := Bridge_tf_surjective X.B.I hb h
      have hy : y ∈ KsetSub X.B.I := (Bridge_mem_Kf_iff X.B.I hb y).1 hKf
      refine ⟨⟨y, hy⟩ * z, fun p => ?_⟩
      rw [map_mul, Pi.mul_apply, Subgroup.coe_mul, hz p, phiK_apply₂]
      by_cases hpq : p = q
      · subst hpq
        rw [if_neg hq, if_pos (Finset.mem_insert_self p S), Subgroup.coe_one, mul_one]
        exact hq1
      · have hp1 : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
        rw [hq2 p.1 hp1, one_mul]
        by_cases hpS : p ∈ S
        · rw [if_pos hpS, if_pos (Finset.mem_insert_of_mem hpS)]
        · rw [if_neg hpS, if_neg]
          intro hm
          rcases Finset.mem_insert.1 hm with h' | h'
          · exact hpq h'
          · exact hpS h'
  obtain ⟨z, hz⟩ := key Finset.univ
  refine ⟨z, funext fun p => Subtype.ext ?_⟩
  rw [hz p, if_pos (Finset.mem_univ p)]

theorem IP_idxProd (hS : SngSurj) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) : IdxProd X hb := by
  show gIdx X hb = ∏ p : TypX X, lIdx X hb p
  rw [IP_gIdx X hb hK]
  show ((levelSubgroupOfCharacter X hK).subgroupOf (KsetSub X.B.I)).index = _
  rw [levelSubgroupAlt_subgroupOf_eq_comap_pi X hb hK hL, Subgroup.index_comap_of_surjective (hf := phiK_surjective X hb hS), index_pi₂]
  rfl

theorem idxProdAll_of (hS : SngSurj) : IdxProdAll := by
  intro D X hb hK _ hL
  exact IP_idxProd X hb hS hK hL

end PI.MassDataKppVolLemmas
