import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uGrpHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uLeKfHolds

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

def GlueHA : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (t : ∀ p : TypX X, HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    ∃ h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J,
      (∀ p : TypX X, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) h = t p) ∧
      ∀ v, v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1) →
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h = 1

def TensInj : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (x y : Af X.B.I.F ⊗[X.B.I.F] X.B.I.E),
    (∀ v : HeightOneSpectrum (𝓞 X.B.I.F), tensMap (E := X.B.I.E) (evalV X.B.I.F v) x =
      tensMap (E := X.B.I.E) (evalV X.B.I.F v) y) → x = y

def LevelCongruenceLocal : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized → ∀ κ : X.B.I.Gf,
    κ ∈ X.B.I.Kset → (∀ p : TypX X, ∃ κ' ∈ X.K2,
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ) =
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ')) → κ ∈ X.K2

theorem tens_lin {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) (x : Fin X.B.I.n → X.B.I.E) (i : Fin X.B.I.n) :
    tensMap (E := X.B.I.E) (evalV X.B.I.F v) (lin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J h
      (ratV (Af X.B.I.F) x) i) =
    lin (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h)
      (ratV (Fv X.B.I.F v) x) i := by
  change tensMap (E := X.B.I.E) (evalV X.B.I.F v) (∑ j, ((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J h :
      GL (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j * inclR (Af X.B.I.F) (x j)) =
    ∑ j, ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
      (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h) : GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) i j * inclR (Fv X.B.I.F v) (x j)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, tensMap_inclR]
  rfl

theorem surjKH_of (hg : GlueHA) (hi : TensInj) : SurjKH := by
  intro D X w t htH htK
  classical
  obtain ⟨h, hT, hO⟩ := hg X t
  have hloc : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
        Hsub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (frameOf X w) ∧
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
        Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v := by
    intro v
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · have e := hT ⟨v, hv⟩
      simp only at e
      rw [e]
      exact ⟨htH ⟨v, hv⟩, htK ⟨v, hv⟩⟩
    · rw [hO v hv]
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))⟩
  refine ⟨h, ?_, ?_, hT⟩
  · unfold Hsub
    rw [mem_stabT]
    intro b
    funext i
    apply hi X
    intro v
    rw [tens_lin X v h]
    have hv := (hloc v).1
    unfold Hsub at hv
    rw [mem_stabT] at hv
    rw [hv b]
    simp only [ratV, tensMap_inclR]
  · exact Subgroup.mem_iInf.2 fun v => (hloc v).2

theorem conjugate_level_congruence_of (hl : LevelCongruenceLocal) : ConjugateLevelLocalCongruence := by
  intro D X hb hK hL w h _ hKf hp
  have hc : finHA X hb (X.xu w) ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    finHA_mem_Kf X hb (X.xu w) (X.xu_K w)
  obtain ⟨κ, hκ⟩ := PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb
    ((finHA X hb (X.xu w))⁻¹ * h * finHA X hb (X.xu w))
  have hκf : finHA X hb κ = (finHA X hb (X.xu w))⁻¹ * h * finHA X hb (X.xu w) := hκ
  have hκK : κ ∈ X.B.I.Kset := by
    refine (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb κ).1 ?_
    change finHA X hb κ ∈ _
    rw [hκf]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hKf) hc
  have hmem : κ ∈ X.K2 := by
    refine hl X hb hK hL κ hκK (fun p => ?_)
    obtain ⟨y, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, hy⟩ := hp p
    refine ⟨k, hk, ?_⟩
    rw [hκf]
    simp only [map_mul, map_inv] at hy ⊢
    rw [← hy]
    group
  exact ⟨finHA X hb κ, ⟨κ, hmem, rfl⟩, by rw [hκf]; group⟩

theorem global_product_of_local (hg : GlueHA) (hi : TensInj) (hl : LevelCongruenceLocal) : GlobProd :=
  globProd_of compH_holds compK_holds k2uGrp_holds (surjKH_of hg hi) (conjugate_level_congruence_of hl)

end MassDataLevelSSteps
