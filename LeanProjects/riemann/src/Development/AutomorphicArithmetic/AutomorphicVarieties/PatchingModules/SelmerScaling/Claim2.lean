import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PhDecDApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUPush
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefULift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlSel

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.claim2 :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ m : Fin S.k.g → S.U.N, S.DualM m → ∀ Φ ∈ S.Ph, ∃ α : Fin S.k.g → S.Tp, (∀ j b, (α j : S.Bh →+ S.F) b = Φ (b • m j) - S.rF b * Φ (m j)) ∧ Lifts S.h S.k fun j => S.alC (α j) := by
  intro l _ S m hm Φ hΦ
  obtain ⟨e, α, μ, hα, hμ, hΦd⟩ := phDec l S Φ hΦ
  let c : Fin e → Fin S.k.g → S.F := fun k j => μ k (m j)
  obtain ⟨u, ψ, hu, h1, h2⟩ := defUTest l S e α μ Φ hα hμ hΦd
  obtain ⟨u', hu', h1', h2'⟩ := defUConj l S.L S.G S.G0 S.h S.n S.x e u ψ
    (fun k => ∑ j, c k j • kapF S.h S.k j) hu
    (fun k => by rw [h1 k]; exact hm (μ k) (hμ k))
  obtain ⟨u'', ψ'', hu'', h1'', h2''⟩ := defUPush l S.L S.G S.G0 S.h S.n S.x S.k e u' ψ c hu' h1'
  have hL := defULift l S.L S.G S.G0 S.h S.n S.x S.k u'' ψ'' hu'' h1''
  refine ⟨fun j => ⟨∑ k, c k j • α k, Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hα k)⟩, ?_, ?_⟩
  · intro j b
    show (∑ k, c k j • α k) b = _
    rw [hΦd, add_sub_cancel_left, AddMonoidHom.finset_sum_apply]
    exact Finset.sum_congr rfl fun k _ => by simp [c, mul_comm]
  · have e2 : (fun j => S.alC (∑ k, c k j • α k)) = epC' S.h S.x u'' := by
      funext j
      rw [h2'' j, (alSel l S).2.2.1 (Fin e) (fun k => c k j) α]
      simp only [h2', h2]
    show Lifts S.h S.k (fun j => S.alC (∑ k, c k j • α k))
    rw [e2]
    exact hL
