import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotent

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem gpProj_mirUin_char : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m j : ℕ) (u : MirUin k (m + (j + 1)))
    (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
    (gpProj k m (j + 1) ⟨u, hh⟩).1 = 1 ∧ ∃ hv : (gpProj k m (j + 1) ⟨u, hh⟩).2 ∈ MirUin k (j + 1),
      mirChar k ψ j ⟨_, hv⟩ = mirChar k ψ (m + j) u := by
  intro k _ _ _ _ ψ m j u hh
  obtain ⟨h1, hv⟩ := GlobalTheory.CompanionTheory.GpUnip.gpProj_unip k m (j + 1) ⟨u, hh⟩ u.2
  refine ⟨h1, hv, ?_⟩
  obtain ⟨w', hw'⟩ := id (id hv : (((gpProj k m (j + 1) ⟨u, hh⟩).2 : Mir k (j + 1)) : GL (Fin (j + 1 + 1)) k) ∈ MirU k (j + 1))
  obtain ⟨w, hw⟩ := (u.2 : ((u : Mir k (m + j + 1)) : GL (Fin (m + j + 1 + 1)) k) ∈ MirU k (m + j + 1))
  rw [mirChar_eq k ψ j ⟨_, hv⟩ w' hw'.symm, mirChar_eq k ψ (m + j) u w hw.symm]
  have hent : ((((gpProj k m (j + 1) ⟨u, hh⟩).2 : Mir k (j + 1)) : GL (Fin (j + 1 + 1)) k) : Matrix _ _ k)
      (Fin.castSucc (Fin.last j)) (Fin.last (j + 1)) =
      (((u : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k) : Matrix _ _ k)
        (eGP m (j + 1) ⟨true, Fin.castSucc (Fin.last j)⟩) (eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩) := by
    show (leviProj k (eGP m (j + 1)) (hgpIncl k m (j + 1) ⟨u, hh⟩) true).val _ _ = _
    rw [leviProj_apply]
    rfl
  have e : eGP m (j + 1) ⟨true, Fin.castSucc (Fin.last j)⟩ = Fin.castSucc (Fin.last (m + j)) :=
    Fin.ext (by rw [blockIndex_true_val]; simp)
  rw [blockIndex_true_last, e, ← hw'] at hent
  have a1 := unip_apply_castSucc_last k (j + 1) w' (Fin.last j)
  have a2 := unip_apply_castSucc_last k (m + j + 1) w (Fin.last (m + j))
  have : w'.toAdd (Fin.last j) = w.toAdd (Fin.last (m + j)) := by
    rw [← a1, ← a2]
    refine hent.trans ?_
    exact congrArg (fun g : GL (Fin (m + j + 1 + 1)) k => (g : Matrix (Fin (m + j + 1 + 1)) (Fin (m + j + 1 + 1)) k)
      (Fin.castSucc (Fin.last (m + j))) (Fin.last (m + j + 1))) hw.symm
  rw [this]

end GlobalTheory.CompanionTheory.LeibPhi

end
