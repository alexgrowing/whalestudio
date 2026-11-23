import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.HerrClassUniq

theorem cocycle_eq {l : ℕ} [Fact l.Prime] {G V LL : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [T2Space LL]
    [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    (a : G → V → V) (c c' : G → V) (hc : Continuous c) (hc' : Continuous c')
    (ha : ∀ x, a 1 x = x)
    (hcc : ∀ g h, c (g * h) = c g + a g (c h)) (hcc' : ∀ g h, c' (g * h) = c' g + a g (c' h))
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1) (hker : ∀ h, lam h = 1 → c h = c' h) (hg₀ : c g₀ = c' g₀) :
    c = c' := by
  have h1 : c 1 = 0 := by
    have := hcc 1 1
    simpa [ha] using this
  have h1' : c' 1 = 0 := by
    have := hcc' 1 1
    simpa [ha] using this
  let S : Subgroup G :=
    { carrier := {g | c g = c' g}
      mul_mem' := fun {a b} ha hb => by
        change c (a * b) = c' (a * b)
        rw [hcc, hcc', show c a = c' a from ha, show c b = c' b from hb]
      one_mem' := by
        change c 1 = c' 1
        rw [h1, h1']
      inv_mem' := fun {a} ha => by
        change c a⁻¹ = c' a⁻¹
        have e1 := hcc a⁻¹ a
        have e2 := hcc' a⁻¹ a
        rw [inv_mul_cancel, h1, show c a = c' a from ha] at e1
        rw [inv_mul_cancel, h1'] at e2
        exact add_right_cancel (e1.symm.trans e2) }
  have hS : IsClosed (S : Set G) := by
    have : {g | c g = c' g} = ⋂ f : Module.Dual LL V, {g | f (c g) = f (c' g)} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      refine ⟨fun h f => by rw [h], fun h => ?_⟩
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff LL]
      intro f
      rw [map_sub, h f, sub_self]
    change IsClosed {g | c g = c' g}
    rw [this]
    refine isClosed_iInter fun f => ?_
    have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
    exact isClosed_eq (hf.comp hc) (hf.comp hc')
  funext g
  have hcl : IsClosed (lam '' (S : Set G)) := (hS.isCompact.image hlam).isClosed
  have hsub : Set.range (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) ⊆ lam '' (S : Set G) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨g₀ ^ n, S.zpow_mem (show g₀ ∈ S from hg₀) n, ?_⟩
    rw [map_zpow, h₀, ← ofAdd_zsmul]
    simp
  have hd : DenseRange (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) :=
    PadicInt.denseRange_intCast
  have hmem : lam g ∈ lam '' (S : Set G) := hcl.closure_subset_iff.2 hsub (hd (lam g))
  obtain ⟨x, hx, hxg⟩ := hmem
  have h2 : g * x⁻¹ ∈ S := hker _ (by rw [map_mul, map_inv, hxg, mul_inv_cancel])
  have h3 : g ∈ S := by simpa using S.mul_mem h2 hx
  exact h3

variable {l : ℕ} [Fact l.Prime]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem val_eq_of_Zf {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} (T : Lt K LL) (H : Subgroup ↥(GK K))
    (c c' : ↥(latticeCocycles (resLat T H))) (b : TW (RW LL) T) (g : ↥H) (e : Zf AI T H c b g = Zf AI T H c' b g) :
    (c : ↥H → T.V) g = (c' : ↥H → T.V) g := by
  unfold Zf at e
  exact congrArg Subtype.val ((GlobalTheory.WittTensorFixed.main l K LL T).2.2 (add_right_cancel e))

set_option maxHeartbeats 1000000 in

theorem cocycle_eq_lat {K LL : FinExt l} (T : Lt K LL) (H : Subgroup ↥(GK K)) (hH : IsClosed (H : Set ↥(GK K)))
    (c c' : ↥(latticeCocycles (resLat T H)))
    (lam : ↥H →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : ↥H)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1)
    (hker : ∀ h, lam h = 1 → (c : ↥H → T.V) h = (c' : ↥H → T.V) h)
    (hg₀ : (c : ↥H → T.V) g₀ = (c' : ↥H → T.V) g₀) : c = c' := by
  haveI := GlobalTheory.HerrClassMaps.compact_GK K
  haveI : CompactSpace ↥H := isCompact_iff_compactSpace.1 hH.isCompact
  haveI := T.mtop
  exact Subtype.ext (cocycle_eq (LL := ↥LL.1) (V := T.V) (fun (g : ↥H) (x : T.V) => T.ρ (g : ↥(GK K)) x) c c' c.2.1.1 c'.2.1.1
    (fun x => by simp) c.2.1.2 c'.2.1.2 lam hlam g₀ h₀ hker hg₀)

set_option maxHeartbeats 2000000 in

theorem class_of_values : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ := by
  intro D HW F l _ K s LL h T c b y z hyz g₀ hg₀ hb hk hz
  refine (cl_fit D HW F K s LL h T y z hyz b hb).elim fun cW hW => ?_
  refine (lam_exists D HW K s LL h).elim fun lam hl => ?_
  have e : c = cW := cocycle_eq_lat T _ hl.2.2.2.2 c cW lam hl.1 g₀ ((hl.2.2.1 g₀).2 hg₀)
    (fun g hg => val_eq_of_Zf (D.locA l) T _ c cW b g
      ((hk g ((hl.2.1 g).1 hg)).trans (hW.2.1 g ((hl.2.1 g).1 hg)).symm))
    (val_eq_of_Zf (D.locA l) T _ c cW b g₀ (hz.trans (hW.2.2 g₀ hg₀).symm))
  exact (congrArg Submodule.Quotient.mk e).trans hW.1

end GlobalTheory.NL.HerrClassUniq
