import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMajorantFrameCompactSubgroupLeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsConjMemMajCptFrame
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.GoodPos

theorem goodPos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ g : GAd σ J, ∃ u ∈ GlobalTheory.StdPar.unip σ J Xf S, u ∈ infPts σ J ∧ ∃ (y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E)) (g₀ : GAd σ J),
        g = u * ι (GlobalTheory.CuspRep.infGL E d y) * g₀ ∧
        ∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K := by
  intro F E _ _ _ _ _ _ σ hCM n J hJ r Xf Yf hW K hK S l d h ι hι hd h1 h2 h3 g
  have hconj : ∀ a : GAd σ J, Continuous fun x : GAd σ J => a * x * a⁻¹ := fun a =>
    (continuous_const.mul continuous_id).mul continuous_const
  have hnorm : ∀ a x : GAd σ J, x ∈ infPts σ J → a * x * a⁻¹ ∈ infPts σ J := fun a x hx => by
    rw [mem_infPts_iff_forall] at hx ⊢
    intro v
    simp [map_mul, map_inv, hx v]
  set K1 : Subgroup (GAd σ J) := K.map (MulAut.conj g).toMonoidHom with hK1
  have hK1le : K1 ≤ infPts σ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnorm g x (hK.1.1 hx)
  have hK1c : IsCompact (K1 : Set (GAd σ J)) := by
    have : (K1 : Set (GAd σ J)) = (fun x => g * x * g⁻¹) '' (K : Set (GAd σ J)) := by
      ext x; simp [hK1, MulAut.conj_apply]
    rw [this]; exact hK.1.2.image (hconj g)
  obtain ⟨c, hc, hle⟩ := GlobalTheory.T.exists_majorantFrame_compact_subgroup_le F E σ hCM n J hJ K1 hK1le hK1c
  set K2 : Subgroup (GAd σ J) := (majCpt σ J c).map (MulAut.conj g⁻¹).toMonoidHom with hK2
  have hmc := (isMaxCpt_majCpt hCM hc).1
  have hK2le : K2 ≤ infPts σ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnorm g⁻¹ x (hmc.1 hx)
  have hK2c : IsCompact (K2 : Set (GAd σ J)) := by
    have : (K2 : Set (GAd σ J)) = (fun x => g⁻¹ * x * g⁻¹⁻¹) '' (majCpt σ J c : Set (GAd σ J)) := by
      ext x; simp [hK2, MulAut.conj_apply]
    rw [this]; exact hmc.2.image (hconj g⁻¹)
  have hKK2 : K ≤ K2 := fun x hx => ⟨g * x * g⁻¹, hle ⟨x, hx, rfl⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hK2K : K2 ≤ K := hK.2 ⟨hK2le, hK2c⟩ hKK2
  obtain ⟨u, hu, hui, y, hy⟩ := exists_conj_mem_majCpt_frame F E σ hCM n J hJ r Xf Yf hW c hc S l d h ι hι hd h1 h2 h3
  refine ⟨u, hu, hui, y, (u * ι (GlobalTheory.CuspRep.infGL E d y))⁻¹ * g, by group, fun k => hK2K ?_⟩
  refine ⟨_, hy k, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv, _root_.mul_inv_rev]
  group

end GlobalTheory.CompanionTheory.GoodPos
