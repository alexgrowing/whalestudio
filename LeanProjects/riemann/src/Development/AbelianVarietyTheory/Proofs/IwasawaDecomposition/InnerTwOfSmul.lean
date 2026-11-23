import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates

noncomputable section

namespace GlobalTheory.Mem.SJ.Pair

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} {X : CxData A} {fc : DefSub A → DefFace Bs} {s : Bool}
  {R : Read D X fc s} {cr : Crd A fc}

theorem cjv_cjv (s : Bool) {n : ℕ} (x : Fin n → ℂ) : cjv s (cjv s x) = x := funext fun i => cj_cj s (x i)

theorem cpt_single {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} (i : Fin n) :
    (fun k => σ ((Pi.single i 1 : Fin n → K) k)) = (Pi.single i 1 : Fin n → ℂ) := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem sum_coord_jN (M : Seam R cr) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    ∑ i, M.cφ u φ i • D.jN u (R.eNu u (Pi.single i 1)) = φ := by
  have h : ∀ i, D.jN u (R.eNu u (Pi.single i 1)) = (M.cφ u).symm (Pi.single i 1) := fun i => by
    rw [← M.cφ_eq]
    exact congrArg _ (cpt_single D.what₂.embLL i)
  simp only [h, ← map_smul, ← map_sum]
  rw [LinearEquiv.symm_apply_eq]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem sum_coord_eMu (M : Seam R cr) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    ∑ i, M.cφ u φ i • D.eMu u (D.jN u (R.eNu u (Pi.single i 1))) = D.eMu u φ := by
  simp only [← map_smul, ← map_sum]
  rw [sum_coord_jN]

theorem sum_coord_heq (M : Seam R cr) (u w : D.what₂.Word) (hw : w = u)
    (b : Fin ((fc X.zs).Dc.a (R.wU u)) → (D.mem w).A.Mram)
    (hb : ∀ i, HEq (b i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) (φ : D.what₂.Mu u) :
    HEq (∑ i, M.cφ u φ i • b i) (D.eMu u φ) := by
  subst hw
  have : b = fun i => D.eMu w (D.jN w (R.eNu w (Pi.single i 1))) := funext fun i => eq_of_heq (hb i)
  subst this
  exact heq_of_eq (sum_coord_eMu M w φ)

theorem inner_tw_of_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) (x y : Tw s E) (κ₀ : ℂ) (v : E)
    (hx : Tw.out x = κ₀ • v) : ⟪x, y⟫_ℂ = cj s (starRingEnd ℂ κ₀ * ⟪v, Tw.out y⟫_ℂ) := by
  rw [Tw.inner_eq, hx, inner_smul_left]

end GlobalTheory.Mem.SJ.Pair

end
