import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqMulFinrankMatrixAlgebraHomEqFinrankMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionFactorThroughTensorCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanOneTmulEqTopAlt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTRho

theorem span_one_tmul (k : Type) [Field k] (C O : Type) [CommRing C] [Ring O] [Algebra C O] [Algebra C k] :
    Submodule.span k (Set.range fun o : O => (1 : k) ⊗ₜ[C] o) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top
  | exact _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top
  | (apply _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top ..)

theorem finrank_homO_morita : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [IsAlgClosed k], (∀ n : ℕ, n.Coprime p → (n : k) ≠ 0) → ∀ (χ : 𝓞 D.F →+* k) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y] (σX : D.O →+* Module.End k X) (σY : D.O →+* Module.End k Y), (∀ c, σX (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → (∀ c, σY (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → D.m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO σX σY) = Module.finrank k X * Module.finrank k Y := by
  intro p _ D k _ _ hk χ X Y _ _ _ _ _ _ σX σY hX hY
  letI : Algebra (𝓞 D.F) k := χ.toAlgebra
  have hiso : Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
    obtain ⟨q, hq⟩ := CharP.exists k
    rcases CharP.char_is_prime_or_zero k q with hq' | rfl
    · by_cases hqp : q = p
      · subst hqp; exact GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charP q D k
      · exfalso
        exact hk q ((Nat.coprime_primes hq' (Fact.out)).2 hqp) (CharP.cast_eq_zero k q)
    · haveI : CharZero k := CharP.charP_to_charZero k
      exact GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charZero p D k
  obtain ⟨e⟩ := hiso
  obtain ⟨ρX, hρX⟩ := GlobalTheory.T.exists_action_factor_through_tensor_character k (𝓞 D.F) D.O _ e X σX hX
  obtain ⟨ρY, hρY⟩ := GlobalTheory.T.exists_action_factor_through_tensor_character k (𝓞 D.F) D.O _ e Y σY hY
  have heq : GlobalTheory.HTRho.homO σX σY = GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom := by
    ext T
    rw [GlobalTheory.HTRho.mem_homO, GlobalTheory.HTRho.mem_homO]
    constructor
    · intro h b
      have hb : b ∈ Submodule.span k (Set.range fun o : D.O => e ((1 : k) ⊗ₜ[𝓞 D.F] o)) := by
        have hr : (Set.range fun o : D.O => e ((1 : k) ⊗ₜ[𝓞 D.F] o)) =
            (e.toLinearMap) '' Set.range (fun o : D.O => (1 : k) ⊗ₜ[𝓞 D.F] o) := by
          rw [← Set.range_comp]; rfl
        rw [hr, Submodule.span_image, span_one_tmul, Submodule.map_top,
          LinearMap.range_eq_top.2 e.surjective]
        trivial
      induction hb using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨o, rfl⟩ := hz
        intro x; simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hρX, hρY]; exact h o x
      | zero => intro x; simp
      | add a b _ _ ha hb =>
        intro x
        have h1 := ha x
        have h2 := hb x
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, LinearMap.add_apply] at h1 h2 ⊢
        rw [h1, h2]
      | smul c a _ ha =>
        intro x
        have h1 := ha x
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul, LinearMap.smul_apply] at h1 ⊢
        rw [h1]
    · intro h o x
      have := h (e (1 ⊗ₜ o)) x
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hρX, hρY] using this
  rw [heq]
  exact GlobalTheory.T.sq_mul_finrank_matrixAlgebra_hom_eq_finrank_mul k D.m X Y ρX ρY

end GlobalTheory.HTRho
