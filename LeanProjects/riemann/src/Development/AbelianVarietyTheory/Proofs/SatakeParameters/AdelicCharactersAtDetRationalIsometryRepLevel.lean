import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryOneFiniteAdelicOfDetNormOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem mu_det_rat_y_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ k < D.R.m, ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → muT (k + 1) (Matrix.GeneralLinearGroup.det x.1) = muT (k + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) * (((t.O u μ).mt (k + 1) ((t.O u μ).dt i c) : ℂˣ) : ℂ) * muT (k + 1) (Matrix.GeneralLinearGroup.det κ.1) ∧ muT (k + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) ≠ 0 ∧ muT (k + 1) (Matrix.GeneralLinearGroup.det κ.1) ≠ 0) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ Xi muT H k hk i hi c x γ _ κ e
  have hJ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi
  have hyU : ((St i hi).y c).1 ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((St i hi).y c).2
  have hκU : κ.1 ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    ((((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2).1
  have hγU : ratA D.host.F γ ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    have e' : ratA D.host.F γ = x.1 * κ.1⁻¹ * (((St i hi).y c).1)⁻¹ := by rw [e]; group
    rw [e']
    exact mul_mem (mul_mem x.2 (inv_mem hκU)) (inv_mem hyU)
  have dγ := det_mem_normOne_of_mem_unitaryPoints hJ hγU
  have dy := det_mem_normOne_of_mem_unitaryPoints hJ hyU
  have dκ := det_mem_normOne_of_mem_unitaryPoints hJ hκU
  refine ⟨?_, H.mu_ne hk dγ, H.mu_ne hk dκ⟩
  rw [e, map_mul, map_mul, (H.mu_mul k hk).2 _ (mul_mem dγ dy) _ dκ, (H.mu_mul k hk).2 _ dγ _ dy, H.mu_cls k hk i hi c]

end GlobalTheory.TwV
