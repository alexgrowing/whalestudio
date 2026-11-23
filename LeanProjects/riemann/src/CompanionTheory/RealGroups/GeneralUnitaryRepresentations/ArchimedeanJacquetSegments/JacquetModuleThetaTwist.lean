import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LocalLanglandsOfIrreducibleAdmissibleImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DualClassInvolutiveImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.CompanionTheory.ThetaProd

namespace CompanionTheory.RgGu.NR.JmTh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thetaL_surjective {h : ℕ} (d : Fin h → ℕ) : Function.Surjective (thetaL (A := k) d) := by
  intro m
  let P := Equiv.piCongrLeft (fun b => GL (Fin (d b)) k) (Fin.revPerm : Equiv.Perm (Fin h))
  refine ⟨fun b => thetaW k (d b) (P m b), ?_⟩
  funext a
  show thetaW k _ (thetaW k _ (P m (Fin.revPerm a))) = m a
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]
  exact Equiv.piCongrLeft_apply_apply (fun b => GL (Fin (d b)) k) Fin.revPerm m a

theorem mem_unipRad_iff' {h N : ℕ} {d : Fin h → ℕ} {e : (Σ a, Fin (d a)) ≃ Fin N} {g : GL (Fin N) k} :
    g ∈ unipRad k e ↔ ∃ hg : g ∈ parab k e, leviProj k e ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

theorem thetaL_eq_one {h : ℕ} (d : Fin h → ℕ) (m : Levi k fun a => Fin (d a)) (hm : thetaL d m = 1) : m = 1 := by
  have key : ∀ b, m (Fin.rev b) = 1 := fun b => by
    have h2 : thetaW k (d (Fin.rev b)) (m (Fin.rev b)) = 1 := congrFun hm b
    have := congrArg (thetaW k (d (Fin.rev b))) h2
    rwa [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW, map_one] at this
  funext a
  obtain ⟨b, rfl⟩ := Fin.revPerm.surjective a
  exact key b

theorem thetaW_mem_unipRad_iff {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (g : GL (Fin N) k) :
    thetaW k N g ∈ unipRad k (stdBlocks (fun a => d (Fin.rev a)) hd') ↔ g ∈ unipRad k (stdBlocks d hd) := by
  rw [mem_unipRad_iff', mem_unipRad_iff']
  constructor
  · rintro ⟨h1, h2⟩
    have hg : g ∈ parab k (stdBlocks d hd) := (thetaW_mem_parab_iff d hd hd' g).1 h1
    refine ⟨hg, thetaL_eq_one d _ ?_⟩
    rw [← leviProj_thetaW d hd hd' ⟨g, hg⟩]
    exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨(thetaW_mem_parab_iff d hd hd' g).2 h1, ?_⟩
    have := leviProj_thetaW (A := k) d hd hd' ⟨g, h1⟩
    rw [h2, map_one] at this
    exact this

theorem twKer_theta {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    twKer (π.comp (thetaW k N)) (unipRad k (stdBlocks d hd)) 1 =
      twKer π (unipRad k (stdBlocks (fun a => d (Fin.rev a)) hd')) 1 := by
  unfold twKer
  congr 1
  ext w
  constructor
  · rintro ⟨n, v, rfl⟩
    refine ⟨⟨thetaW k N n, (thetaW_mem_unipRad_iff (k := k) d hd hd' n).2 n.2⟩, v, ?_⟩
    simp
  · rintro ⟨n, v, rfl⟩
    have hn : thetaW k N (n : GL (Fin N) k) ∈ unipRad k (stdBlocks d hd) := by
      rw [← thetaW_mem_unipRad_iff d hd hd', GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]
      exact n.2
    refine ⟨⟨_, hn⟩, v, ?_⟩
    simp [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]

theorem leviProj_thetaW_leviEmb {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (m : Levi k fun a => Fin (d a)) :
    ∃ u ∈ unipRad k (stdBlocks (fun a => d (Fin.rev a)) hd'),
      thetaW k N (leviEmb k (stdBlocks d hd) m) = u * leviEmb k (stdBlocks (fun a => d (Fin.rev a)) hd') (thetaL d m) := by
  set e := stdBlocks d hd
  set e' := stdBlocks (fun a => d (Fin.rev a)) hd'
  have hx : thetaW k N (leviEmb k e m) ∈ parab k e' := (thetaW_mem_parab_iff d hd hd' _).2 (leviEmb_mem_parab k e m)
  have hy : leviEmb k e' (thetaL d m) ∈ parab k e' := leviEmb_mem_parab k e' _
  refine ⟨thetaW k N (leviEmb k e m) * (leviEmb k e' (thetaL d m))⁻¹, ?_, by group⟩
  rw [mem_unipRad_iff']
  refine ⟨(parab k e').mul_mem hx ((parab k e').inv_mem hy), ?_⟩
  have e1 : leviProj k e' ⟨_, hx⟩ = thetaL d m := by
    rw [leviProj_thetaW d hd hd' ⟨leviEmb k e m, leviEmb_mem_parab k e m⟩, leviProj_leviEmb]
  have e2 : leviProj k e' ⟨_, hy⟩ = thetaL d m := leviProj_leviEmb k e' _
  have : (⟨_, (parab k e').mul_mem hx ((parab k e').inv_mem hy)⟩ : parab k e') = ⟨_, hx⟩ * (⟨_, hy⟩)⁻¹ := rfl
  rw [this, map_mul, map_inv, e1, e2, mul_inv_cancel]

def jacTheta {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    (jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d)) :=
  .mk (Submodule.quotEquivOfEq _ _ (twKer_theta d hd hd' π)) fun m => by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    obtain ⟨u, hu, hm⟩ := leviProj_thetaW_leviEmb (k := k) d hd hd' m
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply, jac, jacU,
      twist_apply, LinearMap.smul_apply, jacquet_mk, LinearEquiv.map_smul, Submodule.quotEquivOfEq_mk,
      deltaHalf_thetaL, MonoidHom.inv_apply]
    congr 1
    rw [hm, map_mul, Module.End.mul_apply]
    refine (Submodule.Quotient.eq _).2 ?_
    refine Submodule.subset_span ⟨⟨u, hu⟩, π (leviEmb k (stdBlocks (fun a => d (Fin.rev a)) hd') (thetaL d m)) v, ?_⟩
    simp

theorem jm_congr {h N : ℕ} {y z : Fin h → IrrGL k} (hyz : y = z) (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm y hy π = jm z hz π := by
  subst hyz
  rfl

theorem jacquet_module_theta_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd (π.comp (thetaW k N)) = jm (dualRev hA x) (sum_dualRev hA x hd) π := by
  have hd' : ∑ a, (x (Fin.rev a)).1 = N := sum_dualRev hA x hd
  have T1 := piTensorRevEquiv (fun a => (x a).rep)
  have T2 := compEquiv (piTensorEquiv fun a => blockEquiv hA hGK x a) (revPi fun a => GL (Fin (x a).1) k)
  have T3 := equivOfEq (piTensor_comp_thetaL (k := k) (fun a => (x a).1) fun a => (dualRev hA x a).rep)
  have T := (T1.trans T2).trans T3
  unfold jm
  rw [jhMult_congr_right _ (jacTheta (fun a => (x a).1) hd hd' π), jhMult_congr_left T]
  exact GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective (thetaL fun a => (x a).1) (thetaL_surjective _) _ _

end CompanionTheory.RgGu.NR.JmTh

namespace CompanionTheory.RgGu.NR

open JmTh

theorem jmTheta (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZSeg.JmTheta k := by
  intro N V _ _ π _ _ a b hd hd'
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  have hGK : GKLocal k := GlobalTheory.T.local_langlands_of_irreducible_admissible hA
  rw [jacquet_module_theta_twist hA hGK ![a, b] hd π]
  refine jm_congr ?_ _ _ π
  rw [dualRev_eq hA]
  funext i
  fin_cases i <;> rfl

end CompanionTheory.RgGu.NR
