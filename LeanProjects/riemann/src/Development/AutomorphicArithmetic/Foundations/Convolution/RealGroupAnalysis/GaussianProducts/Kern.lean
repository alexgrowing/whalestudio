import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private def eqv (F : Type) : (Fin 2 → F) × (Fin 2 → F) ≃ (Fin 4 → F) where
  toFun p := ![p.1 0, p.1 1, p.2 0, p.2 1]
  invFun x := (![x 0, x 1], ![x 2, x 3])
  left_inv p := by
    rcases p with ⟨a, b⟩
    refine Prod.ext ?_ ?_ <;> (ext i; fin_cases i <;> rfl)
  right_inv x := by ext i; fin_cases i <;> rfl

theorem UpperTheory.ConvolutionTheory.R2.G.kern :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (σ : Rw F → Matrix.SpecialLinearGroup (Fin 2) F), M.RowSec σ → ∀ φ : S4 F,
    Th φ.1 = ThRow 0 0 φ.1 + ∑' r : Rw F, ∑' ξ : Fin 2 → F, hat (W.Om (ratS F (σ r)) φ).1 (pt ξ) := by
  intro F E _ _ _ _ _ _ _ D W σ hσ φ
  have H := UpperTheory.ConvolutionTheory.R2.hatSt F E D W
  have hs : Summable (fun ξ : Fin 4 → F => hat φ.1 fun i => rt (ξ i)) :=
    (poisson_of_mem_schwartzBruhatPi (H.mem φ)).1.of_norm
  have hs2 : Summable (fun p : (Fin 2 → F) × (Fin 2 → F) => hat φ.1 ![rt (p.1 0), rt (p.1 1), rt (p.2 0), rt (p.2 1)]) := by
    have h := ((eqv F).summable_iff).2 hs
    refine h.congr fun p => ?_
    simp only [Function.comp]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hrowsum : Summable (fun r : Fin 2 → F => ThRow (rt (r 0)) (rt (r 1)) φ.1) := hs2.prod
  have hth : Th φ.1 = ∑' r : Fin 2 → F, ThRow (rt (r 0)) (rt (r 1)) φ.1 := by
    rw [H.th φ, Th, ← (eqv F).tsum_eq, ]
    have : (fun p : (Fin 2 → F) × (Fin 2 → F) => hat φ.1 fun i => rt ((eqv F) p i)) =
        fun p => hat φ.1 ![rt (p.1 0), rt (p.1 1), rt (p.2 0), rt (p.2 1)] := by
      funext p
      congr 1
      ext i
      fin_cases i <;> rfl
    rw [this, hs2.tsum_prod]
    rfl
  have hr : ∀ r : Rw F, ThRow (rt (r.1 0)) (rt (r.1 1)) φ.1 =
      ∑' ξ : Fin 2 → F, hat (W.Om (ratS F (σ r)) φ).1 (pt ξ) := by
    intro r
    have hv : (![0, 1] : Fin 2 → F) ᵥ* (σ r).1 = r.1 := by
      rw [← hσ r]
      ext j
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have h := H.row (σ r) ![0, 1] φ
    rw [hv] at h
    rw [← h]
    simp [ThRow, pt]
  rw [hth, hrowsum.tsum_eq_add_tsum_ite (0 : Fin 2 → F)]
  have h0 : ThRow (rt ((0 : Fin 2 → F) 0)) (rt ((0 : Fin 2 → F) 1)) φ.1 = ThRow 0 0 φ.1 := by simp
  rw [h0]
  refine congrArg _ ?_
  have h1 := tsum_subtype {r : Fin 2 → F | r ≠ 0} (fun r => ThRow (rt (r 0)) (rt (r 1)) φ.1)
  have h2 : ∑' r : Rw F, ∑' ξ : Fin 2 → F, hat (W.Om (ratS F (σ r)) φ).1 (pt ξ) =
      ∑' r : {r : Fin 2 → F | r ≠ 0}, ThRow (rt (r.1 0)) (rt (r.1 1)) φ.1 :=
    tsum_congr fun r => (hr r).symm
  rw [h2, h1]
  refine tsum_congr fun r => ?_
  by_cases h : r = 0
  · simp [h]
  · simp [h]
