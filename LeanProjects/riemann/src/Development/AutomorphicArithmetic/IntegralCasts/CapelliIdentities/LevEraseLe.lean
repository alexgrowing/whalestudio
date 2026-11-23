import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenStabilizerLinearMap
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsGoodWithoutBad

namespace UpperTheory.Reformulated.B.Grk2

open UpperTheory.Gal.CertificateRingHomMap

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : ℕ}

private theorem mem_lev (S : Finset (Plc E)) (Kw : (w : Plc E) → Subgroup (GLw n w)) (k : GUf E n) :
    k ∈ lev S Kw ↔ (sim k ∈ ZU ∧ ∀ w ∈ S, comp w k ∈ Kw w) ∧
      ∀ w : Plc E, (w ∉ S ∧ cj w ∉ S) → comp w k ∈ GlobalTheory.LFun.KGL w n := by
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

private theorem isOpen_stab (π : GlobalTheory.DefU.AutSub E n) (W : GlobalTheory.DefU.Wt E n)
    (f : GlobalTheory.DefU.algForms W) (hf : f ∈ π.finPart W) :
    IsOpen {u : GlobalTheory.UnitaryBC.finU E n | GlobalTheory.DefU.algRep W u f = f} := by
  obtain ⟨V, hV⟩ := π
  have h1 := hV.1
  have hv : ∀ v : W.Sp, f.1 v ∈ V := fun v => by
    have := (Submodule.mem_iInf _).1 hf v
    exact this
  have key := UpperTheory.isOpen_stabilizer_linear_map (fun u : GlobalTheory.UnitaryBC.finU E n => GlobalTheory.UnitaryBC.RU E n u.1) f.1
    (fun v => by
      obtain ⟨-, -, h, -⟩ := h1 _ (hv v)
      exact h)
  convert key using 2 with u
  ext u
  exact Subtype.ext_iff

open Classical in
private theorem lev_erase_le (S : Finset (Plc E)) (Kw : (w : Plc E) → Subgroup (GLw n w)) (w : Plc E)
    (hc : cj w ∉ S) (k : GUf E n) (hk : k ∈ lev (S.erase w) Kw) :
    comp w k ∈ GlobalTheory.LFun.KGL w n ∧ k ∈ lev S (Function.update Kw w (GlobalTheory.LFun.KGL w n)) := by
  rw [mem_lev] at hk
  obtain ⟨⟨h1, h2⟩, h3⟩ := hk
  have hw : comp w k ∈ GlobalTheory.LFun.KGL w n :=
    h3 w ⟨Finset.notMem_erase _ _, fun h => hc (Finset.mem_of_mem_erase h)⟩
  refine ⟨hw, (mem_lev _ _ _).2 ⟨⟨h1, fun v hv => ?_⟩, fun v hv => h3 v
    ⟨fun h => hv.1 (Finset.mem_of_mem_erase h), fun h => hv.2 (Finset.mem_of_mem_erase h)⟩⟩⟩
  by_cases e : v = w
  · subst e
    rw [Function.update_self]
    exact hw
  · rw [Function.update_of_ne e]
    exact h2 v (Finset.mem_erase.2 ⟨e, hv⟩)

end UpperTheory.Reformulated.B.Grk2

open UpperTheory.Gal.CertificateRingHomMap in
theorem UpperTheory.Reformulated.B.Grk2.pVecU_of :
    UpperTheory.Gal.CertificateRingHomMap.NbhdU → UpperTheory.Gal.CertificateRingHomMap.StepAt → UpperTheory.Gal.CertificateRingHomMap.SphType → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.VecU := by
  classical
  intro hN hS hT hL E _ _ _ n π W hne Up hUp w₀ hw₀ hU₀ J χ hJo hJc hJ
  obtain ⟨f₀, hf₀, hf₀ne⟩ := (Submodule.ne_bot_iff _).1 hne
  let O : Subgroup (GlobalTheory.UnitaryBC.finU E n) :=
    { carrier := {u | GlobalTheory.DefU.algRep W u f₀ = f₀}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  obtain ⟨S₀, Kw, hsh₀, hO⟩ := hN E n O (isOpen_stab π W f₀ hf₀) Up hUp w₀ hw₀ hU₀
  obtain ⟨S, ⟨hsh, f, hf, hfne, hfix⟩, hgood⟩ := UpperTheory.exists_good_without_bad
    (fun S : Finset (Plc E) => Shape Up w₀ S Kw ∧ ∃ f ∈ π.finPart W, f ≠ 0 ∧
      ∀ u : GlobalTheory.UnitaryBC.finU E n, ofU u ∈ lev S Kw → GlobalTheory.DefU.algRep W u f = f)
    (fun w => GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀ ∧ HasType π.V w (GlobalTheory.LFun.KGL w n) 1)
    (by
      rintro S w ⟨⟨s1, s2, s3, s4, s5⟩, f, hf, hfne, hfix⟩ hwS ⟨hw, hww, hty⟩
      have hc := (s5 w hwS hw).2
      obtain ⟨f', hf', hf'ne, hf'e⟩ := hS E n π W f hf hfne S Kw w hw hwS hc hfix _ 1
        (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2 hty
      refine ⟨⟨Finset.mem_erase.2 ⟨hww.symm, s1⟩,
        fun v hv => s2 v (Finset.mem_of_mem_erase hv),
        fun v hv => s3 v (Finset.mem_of_mem_erase hv),
        fun v hv => s4 v (Finset.mem_of_mem_erase hv),
        fun v hv h => ⟨(s5 v (Finset.mem_of_mem_erase hv) h).1,
          fun h' => (s5 v (Finset.mem_of_mem_erase hv) h).2 (Finset.mem_of_mem_erase h')⟩⟩,
        f', hf', hf'ne, fun u hu => ?_⟩
      obtain ⟨a, b⟩ := lev_erase_le S Kw w hc _ hu
      simpa using hf'e u b a)
    S₀ ⟨hsh₀, f₀, hf₀, hf₀ne, hO⟩
  obtain ⟨s1, s2, s3, s4, s5⟩ := hsh
  obtain ⟨f', hf', hf'ne, hf'e⟩ :=
    hS E n π W f hf hfne S Kw w₀ hw₀ s1 (s5 w₀ s1 hw₀).2 hfix J χ hJc hJ
  refine ⟨S, Function.update Kw w₀ J, ⟨s1, fun v hv => ?_, fun v hv => ?_, fun v hv e => ?_, s5⟩,
    Function.update_self _ _ _, fun w hw hap hsat => ?_, f', hf', hf'ne, hf'e⟩
  · by_cases e : v = w₀
    · subst e
      rw [Function.update_self]
      exact hJo
    · rw [Function.update_of_ne e]
      exact s2 v hv
  · by_cases e : v = w₀
    · subst e
      rw [Function.update_self]
      exact hJc
    · rw [Function.update_of_ne e]
      exact s3 v hv
  · rw [Function.update_of_ne e]
    exact s4 v hv e
  · obtain ⟨t1, t2⟩ := (hT E n π w hw).1 hsat
    obtain ⟨a1, a2⟩ := ((hL E n w₀ hw₀).2.1 w).1 hap
    obtain ⟨-, -, -, b1, b2, -⟩ := hL E n w hw
    refine ⟨fun h => hgood w h ⟨hw, a1, t1⟩, fun h => hgood _ h ⟨b1, fun e => a2 ?_, t2⟩⟩
    rw [← e, b2]
