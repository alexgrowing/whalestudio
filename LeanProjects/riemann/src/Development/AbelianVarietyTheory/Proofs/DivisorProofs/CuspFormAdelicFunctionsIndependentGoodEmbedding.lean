import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdIndepOfLawsM

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PhiIndep

open ReciprocityTheory.ChartRestriction.G.FD in

theorem bchar_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have ht : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular ht] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

open ReciprocityTheory.ChartRestriction.G.FD in

theorem indep_along {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp G : Type}
    (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : G → Σ k, Frame (X k).Ψ r)
    (honto : ∀ k, ∀ x ∈ (X k).dom, ∃ g, ∃ γ ∈ (X k).Γ, ∃ b ∈ Bor (X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩)
    (hχ : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) (ν : G → ℂ) (hν : ∀ g, ν g ≠ 0)
    {m : ℕ} (P : Fin m → FDSec X) (hS : ∀ i k, (X k).IsSec (la k) (P i k)) (h0 : ∀ i, P i ∈ offZero X)
    (hP : LinearIndependent ℂ P) (φ : Fin m → G → ℂ) (hφ : ∀ i g, φ i g = ν g * P i (dict g).1 (dict g).2) :
    LinearIndependent ℂ φ := by
  rw [Fintype.linearIndependent_iff] at hP ⊢
  intro c hc
  refine hP c ?_
  funext k x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases hx : x ∈ (X k).dom
  · obtain ⟨g, γ, hγ, b, hb, hg⟩ := honto k x hx
    have h := congrFun hc g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hφ] at h
    have hγx : lact γ x ∈ (X k).dom := dom_lact (X k) hx ((X k).Γ_stab γ hγ)
    have e : ∀ i, P i (dict g).1 (dict g).2 = bchar (la k) b * P i k x := by
      intro i
      rw [hg]
      show P i k (rmul (lact γ x) b) = _
      rw [(hS i k).2.1 _ hγx b hb, (hS i k).2.2 γ hγ x hx, hχ k γ hγ, one_mul]
    apply mul_left_cancel₀ (mul_ne_zero (hν g) (bchar_ne_zero (la k) hb))
    rw [mul_zero, Finset.mul_sum, ← h]
    exact Finset.sum_congr rfl fun i _ => by rw [e i]; ring
  · exact Finset.sum_eq_zero fun i _ => by rw [h0 i k x hx, mul_zero]

set_option maxHeartbeats 1000000 in

theorem phiJ_indep (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n) (m : ℕ) (b : Fin m → T.R j)
    (hs : ∀ k, b k ∈ sec (T.Q.Xo j) T.Q.c a n) (hb : LinearIndependent T.Q.c.F b) :
    LinearIndependent ℂ fun k => T.phiJ j σ a (b k) := by
  obtain ⟨th, hr, -, hD⟩ := h.dictU j hj σ hσ
  have hI := GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj σ hσ a n hd m b hs hb
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  refine indep_along (T.U j σ).X (laU (T.U j σ) a n) (T.dict j σ) hD.2.2.2.2.1 (h.chiTriv j hj σ hσ a n hd)
    (fun g => ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * (T.cE j σ (T.dict j σ g).1 * T.mu j σ g)) ?_
    (fun k => rdU (T.U j σ) (b k)) (fun i k => (h.unf j hj σ hσ).2.2.2.2.1 a n hd _ (hs i) k)
    (fun i => rdU_mem_offZero _ _) hI _ ?_
  · intro g
    refine mul_ne_zero hl (mul_ne_zero ?_ ?_)
    · exact norm_ne_zero_iff.1 (by rw [h.cUnit j hj σ hσ]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(h.muUnit j hj σ hσ).2.1]; exact one_ne_zero)
  · intro i g
    simp only [CoreJ.phiJ, Pi.smul_apply, smul_eq_mul, adel_muPin]
    ring

theorem phiC_indep_of (D : D7) (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {m : ℕ} (b : Fin m → T.R j)
    (H : LinearIndependent ℂ fun k => T.phiJ j σ a (b k)) :
    LinearIndependent ℂ fun k => phiC T hV a (b k) := by
  subst hV
  exact H

set_option maxHeartbeats 1000000 in

theorem phiC_indep : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := by
  intro D T κ h i σ hσ hV m b hb
  refine phiC_indep_of D T hV _ (fun k => (b k : T.R ((i : ℕ) + 1))) ?_
  exact phiJ_indep D T h _ (inR i) σ hσ _ (κ i).n (dom_wtA (κ i)) m _
    (fun k => cusp_le_sec _ _ _ _ _ (b k).2)
    (hb.map' (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype (Submodule.ker_subtype _))

end GlobalTheory.PhiIndep
