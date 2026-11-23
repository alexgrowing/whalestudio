import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMultiplicationFlatColumnsEvalStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.DetNe

theorem det_ne_zero_of_indep : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (u : Fin (S.D + 1) × Fin S.N → E), LinearIndependent E (fun k => word Φ.mul (fun q j => u ((col k).β q, j)) (Φ.ι (col k).x)) → S.det c col ≠ 0 := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc col u hind hdet
  obtain ⟨c', hspan, hval⟩ := GlobalTheory.T.hermitianMultiplicationFlat_columns_eval F A S hS E A' s δ Φ d b c hc
  set v : Fin d → A' := fun k => word Φ.mul (fun q j => u ((col k).β q, j)) (Φ.ι (col k).x) with hv
  set M : Matrix (Fin d) (Fin d) E := Matrix.of fun i k => c' i (v k) with hM
  have hMdet : M.det = 0 := by
    have h1 : aeval u (S.det c col) = 0 := by rw [hdet, map_zero]
    rw [Sys.det, AlgHom.map_det] at h1
    convert h1 using 2
    ext i k
    simp only [hM, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
    exact ((hval (col k) u).2 i).symm
  obtain ⟨a, ha, hMa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hMdet
  have hmem : ∀ k, v k ∈ Submodule.span E (Φ.ι '' S.V S.T) := fun k => (hval (col k) u).1
  set x : A' := ∑ k, a k • v k with hx
  have hxmem : x ∈ Submodule.span E (Φ.ι '' S.V S.T) :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hmem k)
  have hcx : ∀ i, c' i x = 0 := by
    intro i
    have := congrFun hMa i
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.of_apply, Pi.zero_apply] at this
    rw [hx, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hx0 : x = 0 := by
    rw [← hspan x hxmem]
    simp [hcx]
  have ha0 := (Fintype.linearIndependent_iff.mp hind) a hx0
  exact ha (funext ha0)

end GlobalTheory.HSShort.DetNe
