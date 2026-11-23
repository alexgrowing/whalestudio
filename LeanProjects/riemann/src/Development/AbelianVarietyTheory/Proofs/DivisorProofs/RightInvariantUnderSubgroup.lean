import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
open GlobalTheory.ThK.SplitInv

namespace GlobalTheory.ThK.SplitInv.TrivQuot

variable {H : Type} [Group H]

def rtL (k : H) : (H → ℂ) →ₗ[ℂ] (H → ℂ) := LinearMap.funLeft ℂ ℂ (fun g => g * k)

theorem rtL_apply (k : H) (φ : H → ℂ) : rtL k φ = rt k φ := rfl

theorem rStable_sup {G₀ : Subgroup H} {A B : Submodule ℂ (H → ℂ)} (hA : RStable G₀ A) (hB : RStable G₀ B) :
    RStable G₀ (A ⊔ B) := by
  intro φ hφ k hk
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hφ
  rw [← rtL_apply, map_add]
  exact Submodule.add_mem_sup (hA a ha k hk) (hB b hb k hk)

theorem rStable_inf {G₀ : Subgroup H} {A B : Submodule ℂ (H → ℂ)} (hA : RStable G₀ A) (hB : RStable G₀ B) :
    RStable G₀ (A ⊓ B) := fun φ hφ k hk => ⟨hA φ hφ.1 k hk, hB φ hφ.2 k hk⟩

theorem rStable_span_orbit (G₀ : Subgroup H) (a : H → ℂ) :
    RStable G₀ (Submodule.span ℂ {ψ | ∃ g ∈ G₀, ψ = rt g a}) := by
  intro φ hφ k hk
  rw [← rtL_apply]
  refine (Submodule.span_le (p := (Submodule.span ℂ {ψ | ∃ g ∈ G₀, ψ = rt g a}).comap (rtL k))).2 ?_ hφ
  rintro _ ⟨g, hg, rfl⟩
  exact Submodule.subset_span ⟨k * g, G₀.mul_mem hk hg, by rw [rtL_apply, rt_rt]⟩

theorem invariant_of_compRed_quotTriv :
    ∀ (H : Type) [Group H] (G₀ : Subgroup H) (S : Submodule ℂ (H → ℂ)), RStable G₀ S → CompRed G₀ S → QuotTriv G₀ S →
      ∀ φ ∈ S, ∀ k ∈ G₀, ∀ g, φ (g * k) = φ g := by
  intro H _ G₀ S hS hCR hQT x hx k hk
  suffices h : rt k x = x from fun g => congrFun h g
  by_contra hne
  set a₀ : H → ℂ := rt k x - x with ha₀
  have ha₀S : a₀ ∈ S := S.sub_mem (hS x hx k hk) hx
  set C : Submodule ℂ (H → ℂ) := Submodule.span ℂ {ψ | ∃ g ∈ G₀, ψ = rt g a₀} with hCdef
  have hCst : RStable G₀ C := rStable_span_orbit G₀ a₀
  have ha₀C : a₀ ∈ C := Submodule.subset_span ⟨1, G₀.one_mem, (rt_one a₀).symm⟩
  have hCS : C ≤ S := by
    rw [hCdef, Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact hS a₀ ha₀S g hg
  obtain ⟨C', hC'S, hC'st, hCC'inf, hCC'sup⟩ := hCR C hCS hCst
  let P : Set (Submodule ℂ (H → ℂ)) := {M | M ≤ C ∧ RStable G₀ M ∧ a₀ ∉ M}
  have hbot : (⊥ : Submodule ℂ (H → ℂ)) ∈ P := by
    refine ⟨bot_le, fun φ hφ k _ => ?_, ?_⟩
    · rw [Submodule.mem_bot] at hφ ⊢; subst hφ; rfl
    · rw [Submodule.mem_bot]; intro h0; apply hne; rw [← sub_eq_zero]; exact h0
  obtain ⟨M, -, hMmax⟩ := zorn_le_nonempty₀ P (fun c hcP hch y hy => by
    have hne' : c.Nonempty := ⟨y, hy⟩
    have hdir := hch.directedOn
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun φ hφ k hk => ?_, fun ha => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hφz⟩ := (Submodule.mem_sSup_of_directed hne' hdir).1 hφ
      exact le_sSup hz ((hcP hz).2.1 φ hφz k hk)
    · obtain ⟨z, hz, haz⟩ := (Submodule.mem_sSup_of_directed hne' hdir).1 ha
      exact (hcP hz).2.2 haz) ⊥ hbot
  obtain ⟨⟨hMC, hMst, ha₀M⟩, hMle⟩ := hMmax
  set N := M ⊔ C' with hN
  have hNst : RStable G₀ N := rStable_sup hMst hC'st
  have hNS : N ≤ S := sup_le (hMC.trans hCS) hC'S
  have hNC : N ⊓ C = M := by
    rw [hN, sup_inf_assoc_of_le C' hMC, inf_comm, hCC'inf, sup_bot_eq]
  have ha₀N : a₀ ∉ N := fun h => ha₀M (hNC ▸ ⟨h, ha₀C⟩)
  have hNneS : N ≠ S := fun h => ha₀N (h ▸ ha₀S)
  have hmaxN : ∀ N' : Submodule ℂ (H → ℂ), RStable G₀ N' → N ≤ N' → N' ≤ S → N' = N ∨ N' = S := by
    intro N' hN'st hNN' hN'S
    by_cases ha : a₀ ∈ N'
    · right
      refine le_antisymm hN'S ?_
      have hCN' : C ≤ N' := by
        rw [hCdef, Submodule.span_le]
        rintro _ ⟨g, hg, rfl⟩
        exact hN'st a₀ ha g hg
      rw [← hCC'sup]
      exact sup_le hCN' ((le_sup_right : C' ≤ N).trans hNN')
    · left
      have hC'N' : C' ≤ N' := (le_sup_right : C' ≤ N).trans hNN'
      have hMN' : M ≤ N' ⊓ C := le_inf ((le_sup_left : M ≤ N).trans hNN') hMC
      have hP : N' ⊓ C ∈ P := ⟨inf_le_right, rStable_inf hN'st hCst, fun h => ha h.1⟩
      have hle : N' ⊓ C ≤ M := hMle hP hMN'
      refine le_antisymm ?_ hNN'
      have e : N' = C' ⊔ C ⊓ N' := by
        rw [← sup_inf_assoc_of_le C hC'N', sup_comm, hCC'sup]
        exact (inf_eq_right.2 hN'S).symm
      rw [e, hN, sup_comm M C']
      exact sup_le_sup_left (by rw [inf_comm]; exact hle) C'
  exact ha₀N (hQT N hNS hNst hNneS hmaxN x hx k hk)

end GlobalTheory.ThK.SplitInv.TrivQuot
