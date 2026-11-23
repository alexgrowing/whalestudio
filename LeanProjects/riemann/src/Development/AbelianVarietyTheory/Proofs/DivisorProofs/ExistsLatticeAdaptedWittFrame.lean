import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdaptedLatticeFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameOrthogonalComplementBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeIntegralProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeProjectionCriterionStatement
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)

noncomputable section
namespace GlobalTheory.AdaptedWitt

theorem exists_isAdapted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ L₀ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L₀ → (∀ v, IsSelfDualAt σ J L₀ v) →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∃ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), GlobalTheory.EisLine.IsAdapted σ J X Y L a := by
  intro F E _ _ _ _ _ σ hcm _ n J hJ L₀ hL₀ hd r X Y hW
  obtain ⟨m, I, Q, hn, IX, IY, XI, YI, QX, QY, QI, hQ, h1, hG⟩ := GlobalTheory.T.witt_frame_orthogonal_complement_basis F E σ hcm n r J hJ X Y hW
  have YX : cT (σ : E →+* E) Y * J * X = 1 := by
    ext i j
    have h := congrArg (fun M => σ (M j i)) hW.xy
    simp only [Formalism.UG.cT, Matrix.mul_apply, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply,
      AlgHom.coe_toRingHom, sigma_sigma hcm, hJ.1] at h
    rw [Matrix.one_apply] at h ⊢
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, AlgHom.coe_toRingHom]
    have e : ∀ a b, X b j * J a b * σ (Y a i) = σ (Y a i) * J a b * X b j := fun a b => by ring
    simp only [Finset.sum_mul, e] at h
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  obtain ⟨L', hL', hd'⟩ := GlobalTheory.T.self_dual_lattice_projection_criterion F E σ n m r J hJ.2 L₀ hL₀ hd (GlobalTheory.T.self_dual_lattice_integral_projection F E σ n J hJ.2 L₀ hL₀ hd) X Y I Q hW.xx XI QX QI hG.2 hQ h1
  obtain ⟨L, hL, hdL, hs⟩ := HypAdapt.exists_lattice_hyp σ J hJ.2 hG.2 hL' hd' hW.xx hW.yy YX hW.xy XI YI QX QY QI hQ h1
  choose b δ hb hc using HypAdapt.exists_arch_frame_hyp σ J hcm hn hG (X := X) (Y := Y) (I := I) hW.xx hW.yy YX hW.xy IX IY XI YI rfl
  haveI := hL
  obtain ⟨a, -, ha⟩ := Frames.exists_isLatticeFrame_of_arch L b
  exact ⟨L, a, hL, hdL, hs, fun w => ⟨δ w, by rw [ha w]; exact hb w⟩, fun w => ⟨_, by rw [map_inv, ha w]; exact hc w⟩⟩

end GlobalTheory.AdaptedWitt
