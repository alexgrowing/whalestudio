import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.CompanionTheory.ThetaProd
open scoped Matrix

namespace GlobalTheory.CompanionTheory.JmThetaInv

section Ring

variable {A : Type} [CommRing A]

theorem thetaL_eq_one {h : ℕ} (d : Fin h → ℕ) {x : Levi A (fun a => Fin (d a))} (hx : thetaL d x = 1) : x = 1 := by
  funext b
  obtain ⟨c, rfl⟩ := Fin.rev_surjective b
  have h1 : thetaW A (d (Fin.rev c)) (x (Fin.rev c)) = 1 := congrFun hx c
  have h2 := GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW_ring _ (x (Fin.rev c))
  rw [h1, map_one] at h2
  exact h2.symm

theorem thetaL_surjective {h : ℕ} (d : Fin h → ℕ) : Function.Surjective (thetaL (A := A) d) := by
  intro y
  refine ⟨fun b => thetaW A (d b) (cast (by show GL (Fin (d (Fin.rev (Fin.rev b)))) A = _; rw [Fin.rev_rev]) (y (Fin.rev b))), ?_⟩
  funext a
  show thetaW A (d (Fin.rev a)) (thetaW A (d (Fin.rev a)) (cast _ (y (Fin.rev (Fin.rev a))))) = y a
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW_ring]
  have : ∀ (c : Fin h) (hc : c = a) (hh : GL (Fin (d (Fin.rev c))) A = GL (Fin (d (Fin.rev a))) A),
      cast hh (y c) = y a := by
    rintro c rfl hh
    rfl
  exact this _ (Fin.rev_rev a) _

theorem thetaW_mem_unipRad_iff {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (g : GL (Fin N) A) :
    thetaW A N g ∈ unipRad A (stdBlocks (fun a => d (Fin.rev a)) hd') ↔ g ∈ unipRad A (stdBlocks d hd) := by
  constructor
  · intro H
    have hp : g ∈ parab A (stdBlocks d hd) :=
      (thetaW_mem_parab_iff d hd hd' g).1 (unipRad_le_parab A _ H)
    refine (coe_mem_unipRad A (⟨g, hp⟩ : parab A (stdBlocks d hd))).2 (thetaL_eq_one d ?_)
    rw [← leviProj_thetaW d hd hd' ⟨g, hp⟩]
    exact (coe_mem_unipRad A _).1 H
  · intro H
    have hp : g ∈ parab A (stdBlocks d hd) := unipRad_le_parab A _ H
    have h1 : leviProj A (stdBlocks d hd) ⟨g, hp⟩ = 1 := (coe_mem_unipRad A _).1 H
    refine (coe_mem_unipRad A (⟨thetaW A N g, (thetaW_mem_parab_iff d hd hd' g).2 hp⟩ :
      parab A (stdBlocks (fun a => d (Fin.rev a)) hd'))).2 ?_
    rw [leviProj_thetaW d hd hd' ⟨g, hp⟩, h1, map_one]

theorem thetaW_leviEmb {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (g : Levi A (fun a => Fin (d a))) :
    thetaW A N (leviEmb A (stdBlocks d hd) g) =
      leviEmb A (stdBlocks (fun a => d (Fin.rev a)) hd') (thetaL d g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks (fun a => d (Fin.rev a)) hd').surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks (fun a => d (Fin.rev a)) hd').surjective j
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply, rev_stdBlocks d hd hd', rev_stdBlocks d hd hd', ← map_inv]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviEmb_apply_same]
    show _ = (thetaW A (d (Fin.rev a)) (g (Fin.rev a))).1 i j
    rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply]
    rfl
  · rw [leviEmb_apply_ne A _ _ (fun hh => hab (Fin.rev_injective hh).symm), leviEmb_apply_ne A _ _ hab]

end Ring

section Jacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem twKer_comp_thetaW {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    twKer (π.comp (thetaW k N)) (unipRad k (stdBlocks d hd)) 1 =
      twKer π (unipRad k (stdBlocks (fun a => d (Fin.rev a)) hd')) 1 := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨thetaW k N u, (thetaW_mem_unipRad_iff d hd hd' _).2 u.2⟩, v, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    have hu : thetaW k N (u : GL (Fin N) k) ∈ unipRad k (stdBlocks d hd) :=
      (thetaW_mem_unipRad_iff d hd hd' _).1 (by rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]; exact u.2)
    refine Submodule.subset_span ⟨⟨_, hu⟩, v, ?_⟩
    simp [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]

def jacCompThetaW {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    (jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d)) :=
  .mk (Submodule.quotEquivOfEq _ _ (twKer_comp_thetaW d hd hd' π)) fun g => by
    refine LinearMap.ext fun v => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply]
    rw [Submodule.quotEquivOfEq_mk, jac_mk, jac_mk, map_smul, Submodule.quotEquivOfEq_mk, deltaHalf_thetaL]
    simp only [MonoidHom.comp_apply, thetaW_leviEmb d hd hd' g]

theorem jm_comp_theta_eq_dual_reverse (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd (π.comp (thetaW k N)) = jm (dualRev hA x) (sum_dualRev hA x hd) π := by
  have hd' : ∑ a, (x (Fin.rev a)).1 = N := sum_dualRev hA x hd
  have T1 := piTensorRevEquiv (fun a => (x a).rep)
  have T2 := compEquiv (piTensorEquiv fun a => blockEquiv hA hGK x a) (revPi fun a => GL (Fin (x a).1) k)
  have T3 := equivOfEq (piTensor_comp_thetaL (k := k) (fun a => (x a).1) fun a => (dualRev hA x a).rep)
  have T := (T1.trans T2).trans T3
  unfold jm
  rw [jhMult_congr_right _ (jacCompThetaW (fun a => (x a).1) hd hd' π), jhMult_congr_left T]
  exact GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective (thetaL fun a => (x a).1) (thetaL_surjective _) _ _

theorem jm_comp_thetaW (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x y : Fin h → IrrGL k) (hy : y = fun a => dualCl (x (Fin.rev a))) (hd : ∑ a, (x a).1 = N)
    (hd' : ∑ a, (y a).1 = N) (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd (π.comp (thetaW k N)) = jm y hd' π := by
  rw [← dualRev_eq hA x] at hy
  subst hy
  exact jm_comp_theta_eq_dual_reverse hA hGK x hd π

end Jacquet

theorem jmTheta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.JmTheta k := by
  intro k _ _ _ _ hA N V _ _ π _ _ a b hd hd'
  refine jm_comp_thetaW hA (GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) _ _ ?_ hd hd' π
  funext i
  fin_cases i <;> rfl

end GlobalTheory.CompanionTheory.JmThetaInv

end
