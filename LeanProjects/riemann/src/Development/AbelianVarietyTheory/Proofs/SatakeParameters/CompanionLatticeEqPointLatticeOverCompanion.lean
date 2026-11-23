import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOverVUnder
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatK
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatDlOfIsOrthCo
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LatCoCompan

open Formalism.L2.GlobalTheoryTheory.Comp in

theorem latCo_eq_latAd_compan : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (co : GL (Fin (D.R.N i)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → ∀ (a : 𝓞 D.host.E) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin (D.R.N i) → D.host.E)) = ⊤ → latCo D.sp (gramN D i hi) co a x.1 Lb = latAd (ratA D.host.F co * x.1) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Module.Finite (𝓞 D.host.E) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Submodule.span D.host.E ((compan (sp := D.sp) (gramN D i hi) a Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
  intro D i hi co hco a x Lb hfin hspan
  have horth : IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (toLE co) := by
    intro u v
    have h := hform_mulVec_rect (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
      (co.1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) u v
    rw [Matrix.mul_one] at h
    have hc : cT (D.sp.cm.sig : D.host.E →+* D.host.E) co.1 * co.1 = (gramN D i hi) := hco
    rw [hc] at h
    have e1 : hform (D.sp.cm.sig : D.host.E →+* D.host.E) 1 (co.1 *ᵥ u) (co.1 *ᵥ v) =
        ∑ b, (D.sp.cm.sig : D.host.E →+* D.host.E) ((co.1 *ᵥ u) b) * (co.1 *ᵥ v) b := by
      simp only [hform, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [e1] at h
    exact h
  have hJ : ∀ M : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E), IsLat M → IsLat (dl D.sp.cm.sig (gramN D i hi) M) :=
    fun M hM => GlobalTheory.OrthDual.isLat_dl D.sp.cm.sig (gramN D i hi) (toLE co) horth M hM
  have hLb : IsLat Lb := ⟨hfin, hspan⟩
  have hx : x.1 ∈ UPts D.sp.cm.sig (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := x.2
  have hC : IsLat (compan (sp := D.sp) (gramN D i hi) a Lb) := by
    by_cases ha : a = 0
    · subst ha; rw [GlobalTheory.SDCompan.compan_zero]; exact hLb
    · rw [GlobalTheory.SDCompan.compan_eq]; exact isLat_sup hLb (isLat_smul (hJ _ hLb) ha)
  refine ⟨?_, hC.1, hC.2⟩
  have hG : compan (sp := D.sp) (gramN D i hi) a (latAd x.1 Lb) = latAd x.1 (compan (sp := D.sp) (gramN D i hi) a Lb) := by
    by_cases ha : a = 0
    · subst ha; rw [GlobalTheory.SDCompan.compan_zero, GlobalTheory.SDCompan.compan_zero]
    · rw [GlobalTheory.SDCompan.compan_eq, GlobalTheory.SDCompan.compan_eq, GlobalTheory.SDCompan.latAd_eq, GlobalTheory.SDCompan.latAd_eq]
      exact (glob_companion D.sp.cm.sig (gramN D i hi) hJ hLb ha x.1 hx).symm
  unfold latCo
  rw [hG, latAd_rat]

end GlobalTheory.LatCoCompan
