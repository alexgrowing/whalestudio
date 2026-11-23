import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bwdN_zorth : F0.z ∈ orth (VS D) (Xsp (lf D F0)) :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) F0.z x]
    have h := NMoveP.hT_f_X F0 (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]

theorem bwdN_znotX : F0.z ∉ Xsp (lf D F0) := by
  intro h
  have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 (bwdN_zorth (F0 := F0)) F0.z h
  rw [F0.z_norm, neg_eq_zero] at h0
  have hT := (D.mem u).A.T_prime.ne_zero
  exact hT (Nat.cast_eq_zero.1 h0)

variable (u u' F0 what₂)

set_option maxHeartbeats 1000000 in

theorem bwdN_holds : BwdN Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂
  obtain ⟨hΛ₂lat, hloc₂⟩ := hΛ₂
  obtain ⟨-, hT2, hφ⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hΛlat : Submodule.IsLattice D.host.E γ.lam := hrow.2.1.1
  have ht1 := fun p => (hT2 p).1
  have hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := fun p a =>
    BwdNP.unit_of_frame Zd p γ (ht1 p).1.2.1 a
  have hSDl : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p γ.lam) := fun p => (ht1 p).1.1
  have hSDl₂ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₂) := fun p => (hloc₂ p).1.1.1
  have hpr : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f := fun p => (ht1 p).1.2.1.1
  have hpr₂ : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => (hloc₂ p).1.1.2.1.1
  have hLset : ∀ p, (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f =
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => by
    have h := (hloc₂ p).2.1
    rw [hφ p] at h
    rw [← h]
    exact (Set.image_id _).symm
  have hSD := BwdNP.sd_of_loc Zd hΛlat hSDl
  have hSD₂ := BwdNP.sd_of_loc Zd hΛ₂lat hSDl₂
  set X := Xsp (lf D F0) with hXdef
  have hXiso : ∀ x ∈ X, ∀ y ∈ X, (VS D).hT x y = 0 := fun x hx y hy => NMoveP.hT_X_X F0 hx hy
  have hXX : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) X) → w ∈ X := fun {w} hw =>
    BwdNA.mem_of_orth_orth (VS D) X fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXo := BwdNA.X_le_orth (VS D) X hXiso
  have hL : ∀ x ∈ Λ₂, x ∈ orth (VS D) X → ∃ y ∈ γ.lam, y - x ∈ X := fun x hx hxo => by
    obtain ⟨w, hw, hxw⟩ := BwdNA.dual_sum (VS D) γ.lam hΛlat hSD (orth (VS D) X) x
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl (fun p => (hLset p).symm.subset) hx hxo hmΛ hmU)
    refine ⟨w, hw, ?_⟩
    have h2 := X.neg_mem (hXX hxw)
    rwa [neg_sub] at h2
  have hL' : ∀ y ∈ γ.lam, y ∈ orth (VS D) X → ∃ x ∈ Λ₂, x ∈ orth (VS D) X ∧ y - x ∈ X := fun y hy hyo => by
    obtain ⟨w, hw, hyw⟩ := BwdNA.dual_sum (VS D) Λ₂ hΛ₂lat hSD₂ (orth (VS D) X) y
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl₂ (fun p => (hLset p).subset) hy hyo hmΛ hmU)
    have hX1 := hXX hyw
    refine ⟨w, hw, ?_, hX1⟩
    have e : w = y - (y - w) := by abel
    rw [e]
    exact (orth (VS D) X).sub_mem hyo (hXo hX1)
  have hXm : ∀ x ∈ X, x ∈ Λ₂ ↔ x ∈ γ.lam := fun x hx =>
    ⟨BwdNP.memX Zd γ hpr₂ hpr hΛlat hu hx, BwdNP.memX Zd γ hpr hpr₂ hΛ₂lat hu hx⟩
  have hy := BwdNP.exists_y Zd γ hΛ₂lat hSD₂ hpr₂ hu bwdN_znotX
  have htr : ∃ c : D.host.E, IsIntegral ℤ c ∧ c + star c = 1 := by
    obtain ⟨c, hc⟩ := D.host.exists_trace_one
    refine ⟨(c : D.host.E), RingOfIntegers.isIntegral_coe c, ?_⟩
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host)]
    exact hc
  obtain ⟨n, hiso, hnX, hnz, hno, himg⟩ := BwdNA.main (VS D) X hXiso F0.z bwdN_zorth γ.lam Λ₂ hΛlat hΛ₂lat
    hSD hSD₂ hXm (BwdNP.z_mem Zd γ hΛlat hpr) (BwdNP.z_mem Zd γ hΛ₂lat hpr₂) hL hL' hy htr
  refine ⟨n, ⟨hiso, fun j x hx => ?_, hno, fun a => hnX _ (Submodule.subset_span ⟨a, rfl⟩), hnz⟩, himg⟩
  have hxX : x ∈ X := Submodule.span_mono (Set.image_subset_range _ _) hx
  rw [hnX x hxX, sub_self]
  exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
