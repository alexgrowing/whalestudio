import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtDefs
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CuspidalTwistInjectiveImports

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decW_up (Δ : Segment k) : decW (up Δ) = nxt Δ :: decW Δ := by
  show List.ofFn (fun i : Fin (Δ.len + 1) => (up Δ).term (Fin.rev i)) = _
  rw [List.ofFn_succ]
  congr 1
  simp only [decW]
  congr 1
  funext i
  show Δ.first.nu (((Fin.rev i.succ : Fin (Δ.len + 1)) : ℕ) : ℂ) = Δ.first.nu (((Fin.rev i : Fin Δ.len) : ℕ) : ℂ)
  have h : ((Fin.rev i.succ : Fin (Δ.len + 1)) : ℕ) = ((Fin.rev i : Fin Δ.len) : ℕ) := by
    simp only [Fin.val_rev, Fin.val_succ]
    omega
  rw [h]

theorem nxt_not_mem (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) : nxt Δ ∉ decW Δ := by
  intro h
  rw [decW, List.mem_ofFn] at h
  obtain ⟨i, hi⟩ := h
  have h2 := GlobalTheory.T.cuspidal_twist_injective hA Δ.first Δ.isCusp_first _ _ hi
  have h3 := (Fin.rev i).isLt
  omega

theorem eq_decW_of_append (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (u P Q : List (IrrGL k))
    (h1 : decW Δ = P ++ Q) (h2 : u ++ [nxt Δ] = P ++ nxt Δ :: Q) : u = decW Δ := by
  rcases Q.eq_nil_or_concat' with rfl | ⟨Q', q, rfl⟩
  · rw [h1, List.append_nil]
    exact (List.append_inj' h2 rfl).1
  · exfalso
    have h3 : u ++ [nxt Δ] = (P ++ nxt Δ :: Q') ++ [q] := by simpa using h2
    have h4 := (List.append_inj' h3 rfl).2
    have hq : q = nxt Δ := by simpa using h4.symm
    apply nxt_not_mem hA Δ
    rw [h1, ← hq]
    simp

end CompanionTheory.Exh

end
