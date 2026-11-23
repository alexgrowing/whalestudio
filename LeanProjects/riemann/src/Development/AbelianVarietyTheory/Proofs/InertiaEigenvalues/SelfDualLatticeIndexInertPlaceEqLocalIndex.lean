import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.LocKerMod

theorem relIndex_map_of_proj_left {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : AddSubgroup X)
    (φ P : X →+ X) (M : X →+ Y) (m : Y →+ Y) (hM : ∀ x, M (φ x) = m (M x)) (hK : ∀ x, M x = 0 → P x = 0)
    (hMP : ∀ x, M (P x) = M x) (hPA : ∀ a ∈ A, P a ∈ A) (hφ : ∀ a ∈ A, φ a - P (φ a) = a - P a) :
    (A.map φ).relIndex A = ((A.map M).map m).relIndex (A.map M) := by
  have e1 : (A.map M).map m = (A.map φ).map M := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun x => (hM x).symm
  rw [e1, ← AddSubgroup.relIndex_comap (H := (A.map φ).map M) M A, ← AddSubgroup.inf_relIndex_right (A.map φ),
    ← AddSubgroup.inf_relIndex_right (((A.map φ).map M).comap M)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  refine ⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩
  rintro ⟨⟨z, ⟨y, hy, rfl⟩, hzx⟩, hx⟩
  refine ⟨?_, hx⟩
  have h1 : P (φ y) = P x := by
    have := hK (φ y - x) (by rw [map_sub, hzx, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  have hy' : (x - P x) + P y ∈ A := add_mem (sub_mem hx (hPA x hx)) (hPA y hy)
  have hMy : M ((x - P x) + P y - y) = 0 := by
    rw [map_sub, map_add, map_sub, hMP, hMP]; abel
  have h2 : P ((x - P x) + P y) = P y := by
    have := hK _ hMy
    rwa [map_sub, sub_eq_zero] at this
  have h3 : P (φ ((x - P x) + P y)) = P (φ y) := by
    have := hK (φ ((x - P x) + P y) - φ y) (by rw [← map_sub, hM, hMy, map_zero])
    rwa [map_sub, sub_eq_zero] at this
  refine ⟨(x - P x) + P y, hy', ?_⟩
  calc φ ((x - P x) + P y) = (φ ((x - P x) + P y) - P (φ ((x - P x) + P y))) + P (φ ((x - P x) + P y)) := by abel
    _ = ((x - P x) + P y - P ((x - P x) + P y)) + P (φ y) := by rw [hφ _ hy', h3]
    _ = x := by rw [h2, h1]; abel

end GlobalTheory.LocKerMod

set_option maxHeartbeats 1000000 in
open GlobalTheory.LFun in

theorem GlobalTheory.LocKerMod.latIndex_embV_inert : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w →
    ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g := by
  intro D T v w h hi g
  let φ : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finMat D.sp.cm.sig T.gram (GlobalTheory.FinZeta.embV T v g)).mulVecLin.toAddMonoidHom
  let P : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun y i => singleAt D.host.F w 1 * y i) fun a b => funext fun i => mul_add _ _ _
  let M : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → w.adicCompletion D.host.E) :=
    AddMonoidHom.mk' (fun y i => compAt D.host.F w (y i)) fun a b => funext fun i => map_add _ _ _
  let m : (Fin T.rank → w.adicCompletion D.host.E) →+ (Fin T.rank → w.adicCompletion D.host.E) :=
    (locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom
  have hcomp : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (x : Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) i,
      compAt D.host.F u (φ x i) = ((locMat D.sp.cm.sig T.gram (rfl : u.under (𝓞 D.host.F) = _)
        (proj D.sp.cm.sig T.gram (u.under (𝓞 D.host.F)) (GlobalTheory.FinZeta.embV T v g))).1 *ᵥ
          fun j => compAt D.host.F u (x j)) i := by
    intro u x i
    rw [← finMat_map_compAt D.sp.cm.sig T.gram rfl]
    exact RingHom.map_mulVec (compAt D.host.F u) _ x i
  have hM : ∀ x, M (φ x) = m (M x) := by
    intro x
    funext i
    have := hcomp w x i
    subst h
    rw [proj_emb_self] at this
    exact this
  have hK : ∀ x, M x = 0 → P x = 0 := by
    intro x hx
    funext i
    have h0 : compAt D.host.F w (x i) = 0 := congrFun hx i
    show singleAt D.host.F w 1 * x i = 0
    rw [singleAt_mul, h0, mul_zero, singleAt_zero]
  have hMP : ∀ x, M (P x) = M x := by
    intro x
    funext i
    show compAt D.host.F w (singleAt D.host.F w 1 * x i) = compAt D.host.F w (x i)
    rw [map_mul, compAt_singleAt, one_mul]
  have hPA : ∀ a ∈ Formalism.L2.NTheta.LamHat T, P a ∈ Formalism.L2.NTheta.LamHat T := by
    intro a ha
    have e : P a = fun i => singleAt D.host.F w (compAt D.host.F w (a i)) := by
      funext i
      show singleAt D.host.F w 1 * a i = _
      rw [singleAt_mul, one_mul]
    rw [e]
    exact singleAt_mem_lamHat (compAt_mem_latAt w (hermitianSpaceBaseLattice_eq_frameLattice T ▸ ha))
  have hφ : ∀ a ∈ Formalism.L2.NTheta.LamHat T, φ a - P (φ a) = a - P a := by
    intro a _
    funext i
    show φ a i - singleAt D.host.F w 1 * φ a i = a i - singleAt D.host.F w 1 * a i
    refine compAt_ext fun u => ?_
    by_cases e : u = w
    · subst e
      simp only [map_sub, map_mul, compAt_singleAt, one_mul, sub_self]
    · have hu : u.under (𝓞 D.host.F) ≠ v := fun hu => e ((InertChart.under_eq_iff hi u).1 hu)
      simp only [map_sub, map_mul, compAt_singleAt_ne e, zero_mul, sub_zero]
      rw [hcomp u a i, GlobalTheory.FinZeta.embV, proj_emb_ne _ _ hu, map_one, Units.val_one, Matrix.one_mulVec]
  have hLM : (Formalism.L2.NTheta.LamHat T).map M = (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup := by
    ext y
    rw [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      show (fun i => compAt D.host.F w (a i)) ∈ GlobalTheory.LFun.latAt w (frameLat T)
      exact compAt_mem_latAt w (hermitianSpaceBaseLattice_eq_frameLattice T ▸ ha)
    · intro hy
      refine ⟨_, singleAt_mem_lamHat hy, ?_⟩
      funext i
      exact compAt_singleAt w (y i)
  unfold latIndex idxAt
  rw [relIndex_map_of_proj_left _ φ P M m hM hK hMP hPA hφ, hLM]
