import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Topology
open Filter

namespace GlobalTheory.LatFixMod

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem eventually_keep_cong (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1,
      (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        actO S T p.1 p.2 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          actO S T p.1 p.2 u = u + N • l := by
  set L := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) with hLdef
  have hfg := GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT
  obtain ⟨G, hG, hGl, hgen⟩ := hfg
  have hev := GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hS hT ⟨G, hG, hGl, hgen⟩
  have hall := (Filter.eventually_all_finite hG).2 fun u hu =>
    hev.2 u (GlobalTheory.SplitScalar.latO_fin (hGl u hu)) N hN
  filter_upwards [hev.1, hall] with p hk hp
  refine ⟨hk, fun w hw => ?_⟩
  let U : AddSubgroup (WO S T) :=
    { carrier := {w | ∃ l ∈ L, actO S T p.1 p.2 w = w + N • l}
      zero_mem' := ⟨0, L.zero_mem, by
        have := GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)
        rw [zero_smul, zero_smul] at this
        rw [this, smul_zero, add_zero]⟩
      add_mem' := by
        rintro a b ⟨la, hla, ea⟩ ⟨lb, hlb, eb⟩
        refine ⟨la + lb, L.add_mem hla hlb, ?_⟩
        rw [GlobalTheory.LatNhds.actO_add, ea, eb, smul_add]
        abel
      neg_mem' := by
        rintro a ⟨la, hla, ea⟩
        refine ⟨-la, L.neg_mem hla, ?_⟩
        have h0 := GlobalTheory.LatNhds.actO_add p.1 p.2 a (-a)
        have hz : actO S T p.1 p.2 (0 : WO S T) = 0 := by
          have := GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)
          rw [zero_smul, zero_smul] at this
          rw [this]
        rw [add_neg_cancel, hz, ea] at h0
        rw [smul_neg]
        have : actO S T p.1 p.2 (-a) = -(a + N • la) := (neg_eq_of_add_eq_zero_right h0.symm).symm
        rw [this, neg_add] }
  refine hgen U (fun α hα u hu => ?_) w hw
  obtain ⟨l, hl, e⟩ := hp u hu
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l,
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩) _ hl, ?_⟩
  show actO S T p.1 p.2 _ = _
  rw [GlobalTheory.LatNhds.actO_smul, e, smul_add, smul_comm]

def KeepMod (S T : HSp D) (L : AddSubgroup (WO S T)) (N : ℕ) (x : GA D S) : Prop :=
  (∀ u ∈ L, actO S T x 1 u ∈ L) ∧ ∀ u ∈ L, ∃ l ∈ L, actO S T x 1 u = u + N • l

theorem exists_open_keep_cong : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N →
    ∃ J : Subgroup (Bridge.Gf S), IsOpen (J : Set (Bridge.Gf S)) ∧ ∀ x ∈ GfC S, fin S x ∈ J →
      (∀ u : WO S T, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
        actO S T x 1 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          actO S T x 1 u = u + N • l := by
  intro D S T ΛS ΛT hS hT N hN
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hev := eventually_keep_cong S T ΛS ΛT hS hT N hN
  have t1 : Tendsto (fun x : GA D S => ((x, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_id.prodMk continuous_const : Continuous fun x : GA D S => ((x, (1 : GA D T))))).tendsto 1
    exact this
  have t2 : Tendsto (fun x : GA D S => ((x⁻¹, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_inv.prodMk continuous_const : Continuous fun x : GA D S => ((x⁻¹, (1 : GA D T))))).tendsto 1
    rwa [inv_one, Prod.mk_one_one] at this
  have hx : ∀ᶠ x in 𝓝 (1 : GA D S),
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x ∧
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x⁻¹ :=
    (t1.eventually hev).and (t2.eventually hev)
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial k →
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k⁻¹ := by
    by_contra hne
    have hne' : ∀ n : ℕ, ∃ k, k ∈ GfC S ∧ GlobalTheory.Member.FinCong S n.factorial k ∧
        ¬ (KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧
          KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k⁻¹) :=
      fun n => by
        by_contra h
        exact hne ⟨n, fun k hk hc => by
          by_contra h'
          exact h ⟨k, hk, hc, h'⟩⟩
    choose k hk hkc hkne using hne'
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hx).exists
    exact hkne n hn
  obtain ⟨n, hn⟩ := key
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup S n.factorial).map (finHom S).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup S n.factorial_pos, fun x hxf hJ => ?_⟩
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hJ
  have e' : finHom S k' = finHom S x := congrArg Subtype.val e
  have hc : GlobalTheory.Member.FinCong S n.factorial x := by
    have := hk'.2
    unfold GlobalTheory.Member.FinCong at this ⊢
    rw [← e']
    exact this
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := hn x hxf hc
  refine ⟨fun u => ⟨h1 u, fun hu => ?_⟩, h2⟩
  have e2 := GlobalTheory.WeilVacMove.actO_inv_actO x (1 : GA D T) u
  rw [inv_one] at e2
  rw [← e2]
  exact h3 _ hu

end GlobalTheory.LatFixMod
