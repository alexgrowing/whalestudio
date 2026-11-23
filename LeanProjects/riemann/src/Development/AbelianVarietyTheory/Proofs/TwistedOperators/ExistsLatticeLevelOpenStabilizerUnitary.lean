import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariant
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix
open scoped Topology

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WeilLevelStab

open GlobalTheory.SplitScalar GlobalTheory.HeisOrtho GlobalTheory.Mem.CoefInv

variable {D : D7}

theorem actO_one_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  unfold actO
  rw [inv_one, GlobalTheory.AdelicLatMove.mt_one, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, Matrix.mul_one]

theorem actO_one_mul (S T : HSp D) (k k' : GA D T) (x : WO S T) :
    actO S T 1 (k * k') x = actO S T 1 k (actO S T 1 k' x) := by
  unfold actO
  rw [inv_one, GlobalTheory.AdelicLatMove.mt_one, GlobalTheory.AdelicLatMove.mt_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.mul_one, Matrix.mul_assoc]

theorem actO_nsmul (S T : HSp D) (g : GA D S) (h : GA D T) (c : ℕ) (x : WO S T) :
    actO S T g h (c • x) = c • actO S T g h x :=
  map_nsmul (GlobalTheory.LatLevel.actHom S T g h) c x

def MovesMod (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) (k : GA D T) : Prop :=
  ∀ x ∈ L, ∃ l ∈ L, actO S T 1 k x = x + c • l

theorem movesMod_one (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) : MovesMod S T L c 1 :=
  fun x _ => ⟨0, zero_mem _, by rw [actO_one_one, smul_zero, add_zero]⟩

theorem movesMod_mul {S T : HSp D} {L : AddSubgroup (WO S T)} {c : ℕ} {k k' : GA D T}
    (hk : MovesMod S T L c k) (hk' : MovesMod S T L c k') : MovesMod S T L c (k * k') := by
  intro x hx
  obtain ⟨l', hl', e'⟩ := hk' x hx
  obtain ⟨l, hl, e⟩ := hk x hx
  obtain ⟨l'', hl'', e''⟩ := hk l' hl'
  refine ⟨l + (l' + c • l''), add_mem hl (add_mem hl' (AddSubgroup.nsmul_mem _ hl'' c)), ?_⟩
  rw [actO_one_mul, e', GlobalTheory.LatNhds.actO_add, actO_nsmul, e, e'']
  simp only [smul_add]
  abel

def stabK (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) : Subgroup (GA D T) where
  carrier := {k | MovesMod S T L c k ∧ MovesMod S T L c k⁻¹}
  one_mem' := ⟨movesMod_one S T L c, by rw [inv_one]; exact movesMod_one S T L c⟩
  mul_mem' := fun ha hb => ⟨movesMod_mul ha.1 hb.1, by rw [_root_.mul_inv_rev]; exact movesMod_mul hb.2 ha.2⟩
  inv_mem' := fun ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem isOpen_stabK (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (c : ℕ) (hc : 0 < c) :
    IsOpen ((stabK S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) c : Subgroup (GA D T)) : Set (GA D T)) := by
  have h := eventually_mod ΛS ΛT hS hT c hc
  have ht : Filter.Tendsto (fun k : GA D T => ((1 : GA D S), k)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_const (y := (1 : GA D S))).prodMk continuous_id).tendsto (1 : GA D T)
    exact this
  have ti : Filter.Tendsto (fun k : GA D T => k⁻¹) (𝓝 1) (𝓝 1) := by
    have := (continuous_inv (G := GA D T)).tendsto 1
    rwa [inv_one] at this
  have h1 := ht.eventually h
  have h2 := ti.eventually h1
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [h1, h2] with k hk hk'
  exact ⟨hk, hk'⟩

theorem exists_level_stab_of_selfDual (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) :
    ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧
      (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧
      (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 →
        actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧
      (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
        actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧
          ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  set L := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hLdef
  obtain ⟨n, hn, hnU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).1 U hU
  obtain ⟨hdual, happrox, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  refine ⟨L.map (nsmulAddMonoidHom n), stabK S T L (2 * n * n), ?_,
    isOpen_stabK S T ΛS ΛT hS hT (2 * n * n) (by positivity), ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hnU u hu
  · intro x
    obtain ⟨ρ, hρ, u, hu, hf⟩ := happrox (x - realIdem D • x) (fin_part x)
    refine ⟨ρ, hρ, ?_⟩
    rintro _ ⟨l, hl, rfl⟩ -
    have hnl : n • l ∈ L := AddSubgroup.nsmul_mem _ hl n
    have e : x - ρ = (realIdem D • x + (x - realIdem D • x - ρ - u)) + u := by abel
    show ψ (symplO S T (x - ρ) (n • l)) = 1
    rw [e, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
      symplO_real_fin S T (real_part x) (latO_fin hnl), symplO_real_fin S T hf (latO_fin hnl), zero_add, zero_add]
    exact (hdual u (latO_fin hu)).1 hu _ hnl
  · rintro k ⟨hk, -⟩ - _ ⟨l, hl, rfl⟩ -
    obtain ⟨l', hl', e⟩ := hk l hl
    have hm : l + (2 * n * n) • l' ∈ L := add_mem hl (AddSubgroup.nsmul_mem _ hl' _)
    have e2 : actO S T 1 k (n • l) = n • (l + (2 * n * n) • l') := by rw [actO_nsmul, e]
    refine ⟨⟨_, hm, e2.symm⟩, ?_⟩
    show (actO S T 1 k (n • l)).map (infPart D) = 0
    rw [e2]
    exact latO_fin (AddSubgroup.nsmul_mem _ hm n)
  · rintro k ⟨hk, -⟩ hkf w hw
    have hw' : ∀ l ∈ L, ψ (symplO S T (n • w) l) = 1 := fun l hl => by
      rw [symplO_nsmul]
      exact hw _ ⟨l, hl, rfl⟩ (latO_fin (AddSubgroup.nsmul_mem _ hl n))
    have hff : (n • w - realIdem D • (n • w)).map (infPart D) = 0 := fin_part _
    have hfL : n • w - realIdem D • (n • w) ∈ L := GlobalTheory.LatVac.mem_of_char hψ hS hT hff fun u hu => by
      rw [GlobalTheory.SplitScalar.symplO_sub_left, symplO_real_fin S T (real_part _) (latO_fin hu), sub_zero]
      exact hw' u hu
    obtain ⟨l, hl, e⟩ := hk _ hfL
    have hreal := actO_real (one_mem (GfC S)) hkf (real_part (n • w))
    have e1 : actO S T 1 k w = w + 2 • (n • l) := by
      refine nsmul_cancel hn ?_
      rw [← actO_nsmul, show n • w = realIdem D • (n • w) + (n • w - realIdem D • (n • w)) by abel,
        GlobalTheory.LatNhds.actO_add, hreal, e, ← add_assoc, ← show n • w = realIdem D • (n • w) + (n • w - realIdem D • (n • w)) by abel]
      rw [smul_add, smul_smul, smul_smul]
      congr 2
      ring
    have hd : actO S T 1 k w - w = 2 • (n • l) := by rw [e1, add_sub_cancel_left]
    refine ⟨⟨2 • l, AddSubgroup.nsmul_mem _ hl 2, ?_⟩, ?_, ?_⟩
    · rw [hd]
      exact smul_comm n 2 l
    · rw [hd]
      exact latO_fin (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hl n) 2)
    · rw [hd, two_nsmul, symplOH_add_right, symplOH_add_self]
      exact hw _ ⟨l, hl, rfl⟩ (latO_fin (AddSubgroup.nsmul_mem _ hl n))

theorem exists_level_stab : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  intro D ψ S T hψ U hU
  exact exists_level_stab_of_selfDual ψ S T hψ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) U hU

end GlobalTheory.WeilLevelStab

end
