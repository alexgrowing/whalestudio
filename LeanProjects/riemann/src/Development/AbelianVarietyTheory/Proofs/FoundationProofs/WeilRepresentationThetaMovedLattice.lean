import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorConjHeisenbergMovedLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosureStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.WeilTheta

theorem sd_of_moves (D : D7) {N : ℕ} (g : GA D N) (L : Lat D N) (h : Moves D (g : GL (Fin N) (AE D)) L) :
    SD D L := by
  obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  have : L = Lt g := by
    ext x
    rw [h x, (hLt g).1 x]
  rw [this]
  exact (hLt g).2

theorem om_mem_Th_moved : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h : GA D N) (g' h' : GA D N') (L₁ L₂ : Lat D N) (L₁' L₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → ∀ F ∈ Th D (tor0 D cc δ) L₁ L₁', W.Om g g' F ∈ Th D (tor0 D cc δ) L₂ L₂' := by
  intro D cc δ hC N N' e0 W g h g' h' L₁ L₂ L₁' L₂' h1 h1' h2 h2' F hF
  have hD := (GlobalTheory.InducedType.induced_type D).1
  have s1 := sd_of_moves D h L₁ h1
  have s1' := sd_of_moves D h' L₁' h1'
  have s2 := sd_of_moves D _ L₂ h2
  have s2' := sd_of_moves D _ L₂' h2'
  obtain ⟨hnice, -⟩ := GlobalTheory.ThetaTriple.klat_triples D cc δ hC N N'
  have n1 := hnice _ (Or.inr ⟨L₁, L₁', s1, s1', rfl⟩)
  have n2 := hnice _ (Or.inr ⟨L₂, L₂', s2, s2', rfl⟩)
  obtain ⟨hT, hW, -⟩ := GlobalTheory.T.thetaFunctions_all_levels_closure D cc δ hC N N'
  have hFT := hT L₁ L₁' s1 s1' F hF
  have hGT := W.maps g g' F hFT
  have hfix := ((n1.mem_ThSp F).1 hF).2
  refine (n2.mem_ThSp _).2 ⟨hGT.1, fun y hy => ?_⟩
  obtain ⟨z, hz, -⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D hD cc δ hC.1.1 N N' _ _ L₂ L₂' h2 h2' y hy
  have hWT : Wd D (tor0 D cc δ) y (W.Om g g' F) ∈ TT D (tor0 D cc δ) N N' := by
    rw [hz]; exact hW z _ hGT
  obtain ⟨x, hx, he⟩ := GlobalTheory.WeilEquiv.om_wd_moved D hD cc δ hC.1.1 N N' e0 W g⁻¹ (g * h) g'⁻¹ (g' * h')
    L₂ L₁ L₂' L₁' h2 h2' (by rwa [inv_mul_cancel_left]) (by rwa [inv_mul_cancel_left]) y hy _ hGT
  rw [← W.mul _ _ _ _ F hFT, inv_mul_cancel, inv_mul_cancel, W.one F hFT, hfix x hx] at he
  have h3 := congrArg (W.Om g g') he
  rwa [← W.mul _ _ _ _ _ hWT, mul_inv_cancel, mul_inv_cancel, W.one _ hWT] at h3

end GlobalTheory.WeilTheta
