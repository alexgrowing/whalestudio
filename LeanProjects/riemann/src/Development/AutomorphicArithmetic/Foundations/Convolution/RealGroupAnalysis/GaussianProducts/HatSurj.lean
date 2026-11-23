import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.GaussSchwartz
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatFock
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatInv

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.FourierHatSurjective

variable {F : Type} [Field F] [NumberField F]

private def rf {R : Type} [Neg R] (v : Fin 4 → R) : Fin 4 → R := Function.update v 1 (-v 1)

private theorem rf_rf {R : Type} [InvolutiveNeg R] (v : Fin 4 → R) : rf (rf v) = v := by
  funext i
  by_cases h : i = 1
  · subst h
    simp [rf]
  · simp [rf, h]

private theorem rf_ne {R : Type} [Neg R] (v : Fin 4 → R) {i : Fin 4} (h : i ≠ 1) : rf v i = v i := by
  simp [rf, h]

private theorem rf_one {R : Type} [Neg R] (v : Fin 4 → R) : rf v 1 = -v 1 := by
  simp [rf]

private def rfH (R : Type) [TopologicalSpace R] [AddGroup R] [IsTopologicalAddGroup R] :
    (Fin 4 → R) ≃ₜ (Fin 4 → R) where
  toFun := rf
  invFun := rf
  left_inv := rf_rf
  right_inv := rf_rf
  continuous_toFun := continuous_id.update 1 (continuous_apply 1).neg
  continuous_invFun := continuous_id.update 1 (continuous_apply 1).neg

private theorem fin_rf {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    (fun z => g (rf z)) ∈ finiteSchwartzBruhatPi F (ι := Fin 4) := by
  obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi F).1 hg
  exact (mem_finiteSchwartzBruhatPi F).2
    ⟨h1.comp_continuous (rfH _).continuous, h2.comp_homeomorph (rfH _)⟩

private theorem finPart_rf (v : V4 F) : finPartPi (rf v) = rf (finPartPi v) := by
  funext i
  by_cases h : i = 1
  · subst h
    rw [rf_one]
    change (finPartPi (rf v)) 1 = -(finPartPi v 1)
    simp only [GroundTheory.Heights₂.Theta.finPartPi_eq_adeleFinHom, rf_one, map_neg]
  · rw [rf_ne _ h]
    change (rf v i).2 = (v i).2
    rw [rf_ne _ h]

private theorem poly_rf [IsTotallyReal F] {p : V4 F → ℂ} (hp : p ∈ polyFn (F := F)) :
    (fun v => p (rf v)) ∈ polyFn (F := F) := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨i, w, rfl⟩ := hp
    by_cases h : i = 1
    · subst h
      have e : (fun v : V4 F => ((TR.pInf F (rf v 1) w : ℝ) : ℂ)) =
          (-1 : ℂ) • (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) := by
        funext v
        simp [rf_one]
      have hm : (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) ∈ polyFn (F := F) :=
        Algebra.subset_adjoin ⟨1, w, rfl⟩
      rw [e]
      exact Subalgebra.smul_mem _ hm _
    · have e : (fun v : V4 F => ((TR.pInf F (rf v i) w : ℝ) : ℂ)) =
          (fun v : V4 F => ((TR.pInf F (v i) w : ℝ) : ℂ)) := by
        funext v
        rw [rf_ne _ h]
      rw [e]
      exact Algebra.subset_adjoin ⟨i, w, rfl⟩
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add p q _ _ hp hq => exact add_mem hp hq
  | mul p q _ _ hp hq => exact mul_mem hp hq

private theorem gauss_rf [IsTotallyReal F] (δ : F) (v : V4 F) : gauss δ (rf v) = gauss δ v := by
  have h0 : rf v 0 = v 0 := rf_ne _ (by decide)
  have h2 : rf v 2 = v 2 := rf_ne _ (by decide)
  have h3 : rf v 3 = v 3 := rf_ne _ (by decide)
  simp only [gauss, h0, h2, h3, rf_one, neg_sq]

private theorem fock_rf [IsTotallyReal F] {δ : F} {χ : V4 F → ℂ} (hχ : χ ∈ FockFn δ) :
    (fun v => χ (rf v)) ∈ FockFn δ := by
  induction hχ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, poly_rf hp, _, fin_rf hg, ?_⟩
    funext v
    simp only [gauss_rf, finPart_rf]
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

private theorem fock_le [IsTotallyReal F] {δ : F} (hδ : ∀ e : F →+* ℝ, e δ < 0) {χ : V4 F → ℂ}
    (hχ : χ ∈ FockFn δ) : χ ∈ schwartzBruhatPi F (Fin 4) := by
  refine (Submodule.span_le.2 ?_) hχ
  rintro _ ⟨p, hp, g, hg, rfl⟩
  have h := pgMem F δ hδ Real.pi Real.pi_pos p hp g hg
  change _ ∈ schwartzBruhatPi F (Fin 4)
  simpa only [gauss_eq] using h

end UpperTheory.ConvolutionTheory.R2.G.FourierHatSurjective

open UpperTheory.ConvolutionTheory.R2.G.FourierHatSurjective in
theorem UpperTheory.ConvolutionTheory.R2.G.hatSurj :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ e : F →+* ℝ, e δ < 0) → ∀ χ ∈ FockFn δ, ∃ φ ∈ Fock δ, hat φ.1 = χ := by
  intro F _ _ _ δ hδ χ hχ
  have h1 := fock_rf hχ
  have h2 := hatFock F δ _ h1
  refine ⟨⟨hat fun v => χ (rf v), fock_le hδ h2⟩, h2, ?_⟩
  funext v
  exact (hatInv F ⟨fun v => χ (rf v), fock_le hδ h1⟩ v).trans (congrArg χ (rf_rf v))
