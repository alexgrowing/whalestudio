import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem isClosed_support_smooth_ind {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {W₁ : Type}
    [AddCommGroup W₁] [Module ℂ W₁] {Q : Subgroup G} (σ : Representation ℂ Q W₁) (f : smoothPart (ind Q σ)) :
    IsClosed {g : G | f.1.1 g ≠ 0} := by
  have hT : IsOpen {g : G | ind Q σ g f.1 = f.1} := f.2
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro g hg
  have hg0 : f.1.1 g = 0 := by simpa using hg
  have hc : Continuous fun h : G => g⁻¹ * h := continuous_const.mul continuous_id
  have hm : {h : G | g⁻¹ * h ∈ {κ : G | ind Q σ κ f.1 = f.1}} ∈ 𝓝 g :=
    (hT.preimage hc).mem_nhds (by
      show ind Q σ (g⁻¹ * g) f.1 = f.1
      simp)
  filter_upwards [hm] with h hh
  have e : (ind Q σ (g⁻¹ * h) f.1).1 g = f.1.1 g := congrArg (fun F : indSpace Q σ => F.1 g) hh
  have e' : f.1.1 (g * (g⁻¹ * h)) = f.1.1 g := e
  rw [mul_inv_cancel_left] at e'
  simpa [e', hg0] using hg0

end GlobalTheory.CompanionTheory.BZRes
