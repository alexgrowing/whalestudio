import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

def cplx {D : D7} (V W : HSp D) {k : ℕ} (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (z : Mx D 1 k) :
    WO V W :=
  ∑ i, z 0 i • (B i).map (incA D)

section

variable {D : D7} (V W : HSp D) {k : ℕ} (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E)

theorem cplx_add (z z' : Mx D 1 k) : cplx V W B (z + z') = cplx V W B z + cplx V W B z' := by
  simp only [cplx, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem cplx_zero : cplx V W B 0 = 0 := by
  simp [cplx]

theorem continuous_cplx : Continuous (cplx V W B) := by
  unfold cplx
  refine continuous_finset_sum _ fun i _ => ?_
  exact (continuous_id.matrix_elem 0 i).smul continuous_const

theorem cplx_rat (c : Matrix (Fin 1) (Fin k) D.host.E) :
    cplx V W B (c.map (incA D)) = (∑ i, c 0 i • B i).map (incA D) := by
  ext p q
  simp [cplx, Matrix.sum_apply, map_sum, smul_eq_mul]

end

theorem symplO_eq_add {D : D7} (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  unfold symplOH
  linear_combination (-symplO S T x y) * h2

theorem meanX_heisO_rat {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b))
    (ψ : AddChar (AF D.host.F) ℂ) (F : WO V W → ℂ) (hF : IsThetaFunO ψ V W F) (w : WO V W) (hw : w ∈ ratL W V)
    (hwX : ∀ y, symplO V W w (emb V W P Q y) = 0) (x : WO V W) (hx : ∀ y, symplO V W x (emb V W P Q y) = 0) :
    meanX V W P Q μ 𝓨 (heisO ψ V W w F) x = ψ (symplO V W x w) * meanX V W P Q μ 𝓨 F x := by
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  obtain ⟨γ, rfl⟩ := hw
  unfold meanX
  rw [← integral_const_mul]
  congr 1
  funext y
  have hq := hF.quasi γ (emb V W P Q y + x)
  have er : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ) = ratW W V γ := rfl
  simp only [heisO]
  rw [er] at hwX ⊢
  rw [show emb V W P Q y + x + ratW W V γ = ratW W V γ + (emb V W P Q y + x) by abel, hq, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  congr 2
  rw [l1, l2, skew (ratW W V γ) (emb V W P Q y), hH0 _ _ (hwX y), skew (ratW W V γ) x, symplO_eq_add, skew (ratW W V γ) x]
  ring

theorem meanX_mul_star_rat {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b))
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (F F' : WO V W → ℂ) (hF : IsThetaFunO ψ V W F)
    (hF' : IsThetaFunO ψ V W F') (w : WO V W) (hw : w ∈ ratL W V)
    (hwX : ∀ y, symplO V W w (emb V W P Q y) = 0) (x : WO V W) :
    meanX V W P Q μ 𝓨 F (w + x) * star (meanX V W P Q μ 𝓨 F' (w + x)) =
      meanX V W P Q μ 𝓨 F x * star (meanX V W P Q μ 𝓨 F' x) := by
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  obtain ⟨γ, rfl⟩ := hw
  have er : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ) = ratW W V γ := rfl
  rw [er] at hwX ⊢
  have key : ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G →
      meanX V W P Q μ 𝓨 G (ratW W V γ + x) = ψ (-(symplOH V W (ratW W V γ) x)) * meanX V W P Q μ 𝓨 G x := by
    intro G hG
    unfold meanX
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [show emb V W P Q y + (ratW W V γ + x) = ratW W V γ + (emb V W P Q y + x) by abel, hG.quasi, l2,
      hH0 _ _ (hwX y), zero_add]
  rw [key F hF, key F' hF', star_mul]
  have hn : ψ (-(symplOH V W (ratW W V γ) x)) * star (ψ (-(symplOH V W (ratW W V γ) x))) = 1 := by
    have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ) x))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    norm_num
  linear_combination (meanX V W P Q μ 𝓨 F x * star (meanX V W P Q μ 𝓨 F' x)) * hn

end GlobalTheory.IsoMean

end
