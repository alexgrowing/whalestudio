import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.PrincipalCongruenceLeLevel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Transfer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImASubKpp

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct Matrix

variable {D : D7}

abbrev xuP (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J :=
  PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb (X.xu u))

theorem mem_K2Hp_iff (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (u : D.what₂.Word) (p : TypX X) (x : KvH X u p.1) :
    x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1) ↔
      (xuP X hb u p)⁻¹ * ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
        HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) * xuP X hb u p ∈ MassDataIdxSteps.KppX X hb p := by
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hy' : (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u := by
      have : y ∈ (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) := hy
      rw [coe_K2Hg X hb hK u] at this
      exact this
    obtain ⟨k, hk, e⟩ := (mem_conjugate_level_iff X hb u _).1 hy'
    refine ⟨finHA X hb k, ⟨k, hk, rfl⟩, ?_⟩
    have hxy : ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
        HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) =
        PI.MassDataKppVolLemmas.piV X.B.I p.1 (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := by
      rw [← hyx]
      rfl
    rw [hxy, ← e]
    show PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb k) = _
    simp only [map_mul, map_inv]
    group
  · intro hx
    obtain ⟨k', ⟨k, hk, rfl⟩, hke⟩ := hx
    set y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J :=
      ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)
      with hy_def
    have hyK : y ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 := x.2
    obtain ⟨h, hKf, h1, h2⟩ := PI.MassDataKppVolLemmas.single_component_surjective X.B.I p.1 y hyK
    have hH : h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
      apply mem_stabT_of_comp X.B.I h
      intro v
      by_cases hv : v = p.1
      · subst hv; rw [h1]; exact (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)).2
      · rw [h2 v hv]; exact one_mem _
    have hK2u : h ∈ K2u X hb u := by
      apply mem_conjugate_level_of_local X hb hK hL u h hKf
      intro q
      by_cases hq : q = p
      · subst hq
        refine ⟨k, hk, ?_⟩
        rw [map_mul, map_mul, map_inv, h1]
        exact hke
      · refine ⟨1, hK.1, ?_⟩
        have hq1 : q.1 ≠ p.1 := fun e => hq (Subtype.ext e)
        rw [finHA_one, map_one, map_mul, map_mul, map_inv, h2 q.1 hq1, mul_one, inv_mul_cancel]
    rw [Subgroup.mem_subgroupOf]
    refine ⟨⟨h, hH⟩, ?_, ?_⟩
    · apply Subgroup.subset_closure
      exact hK2u
    · apply Subtype.ext
      exact h1

theorem unipotent_mem_localStabilizer (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    xuP X hb u p ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 := by
  have ha : finHA X hb (X.xu u) ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb (X.xu u)).2 (X.xu_K u)
  rw [Kf, Subgroup.mem_iInf] at ha
  exact ha p.1

theorem mem_K2Hp_iff_cong (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (u : D.what₂.Word) (p : TypX X) (x : KvH X u p.1) :
    x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1) ↔
      MassDataIdxSteps.LocCong X p ((xuP X hb u p)⁻¹ * ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
        HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) * xuP X hb u p) := by
  rw [mem_K2Hp_iff X hb hK hL u p x, MassDataIdxSteps.stImAloc_holds X hb p]
  have hxK : ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
      Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 := x.2
  have hA := unipotent_mem_localStabilizer X hb u p
  have hA' : HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p) ∈
      Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := hA
  have hX' : HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J
      ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
      Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := hxK
  have hmem : (xuP X hb u p)⁻¹ * ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
      HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) * xuP X hb u p ∈ MassDataIdxSteps.KvX X p := by
    show HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J _ ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    exact mul_mem (mul_mem (inv_mem hA') hX') hA'
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hmem, h⟩

end PIW.MassDataColumns
