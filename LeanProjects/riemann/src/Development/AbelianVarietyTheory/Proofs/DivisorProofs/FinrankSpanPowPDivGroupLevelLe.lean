import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelQuotientLePowCotangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualPrimePowConvPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDualStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

open Coalgebra Bialgebra WithConv

namespace GlobalTheory.SpanPow

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]

def annPowIdeal (h : (p : K) = 0) (G : PDivGroup p K) (r : ℕ) : Ideal (G.dual.A r) where
  carrier := {χ | ∀ a : G.A r, (show CartierDual K (G.A r) from χ) (a ^ p ^ r) = 0}
  add_mem' {χ ψ} hχ hψ a := by
    have e1 := hχ a
    have e2 := hψ a
    change (χ.ofConv + ψ.ofConv) (a ^ p ^ r) = 0
    rw [LinearMap.add_apply]
    change χ.ofConv (a ^ p ^ r) = 0 at e1
    change ψ.ofConv (a ^ p ^ r) = 0 at e2
    rw [e1, e2, add_zero]
  zero_mem' a := rfl
  smul_mem' c χ hχ a := by
    change (show CartierDual K (G.A r) from c * χ) (a ^ p ^ r) = 0
    rw [CartierDual.mul_apply, ← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]
    rcases subsingleton_or_nontrivial (G.A r ⊗[K] G.A r) with hs | hn
    · rw [Subsingleton.elim ((comul (R := K) a) ^ p ^ r) 0, map_zero]
    · haveI : CharP (G.A r ⊗[K] G.A r) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 (by
        rw [← map_natCast (algebraMap K (G.A r ⊗[K] G.A r)), h, map_zero])
      haveI : ExpChar (G.A r ⊗[K] G.A r) p := ExpChar.prime (Fact.out : p.Prime)
      have rep := Coalgebra.Repr.arbitrary K a
      rw [← rep.eq, sum_pow_char_pow, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Algebra.TensorProduct.tmul_pow, CartierDual.pair_tmul_tmul]
      have e := hχ (rep.right i)
      change χ.ofConv _ = 0 at e
      rw [e, mul_zero]

theorem frobKerIdeal_le_annPowIdeal (h : (p : K) = 0) (G : PDivGroup p K) (r : ℕ) :
    frobKerIdeal (p ^ r) K (G.dual.A r) ≤ annPowIdeal h G r := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨χ, hχ, rfl⟩ a
  have h1 := GlobalTheory.T.cartierDual_primePow_conv_pairing p K h G r r χ a
  have hχ' : χ.ofConv 1 = 0 := hχ
  change (χ ^ p ^ r).ofConv (a ^ p ^ r) = 0
  change (χ ^ p ^ r).ofConv (a ^ p ^ r) = χ.ofConv (mulBy K (G.A r) (p ^ r) a) ^ p ^ r at h1
  rw [h1, G.mulBy_pow_self r a, Algebra.algebraMap_eq_smul_one, map_smul, hχ', smul_zero,
    zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

end GlobalTheory.SpanPow

open GlobalTheory.SpanPow in
theorem GlobalTheory.finrank_span_pow_le : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ r : ℕ, Module.finrank K (Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r)) ≤ (p ^ r) ^ Module.finrank K G.dual.omega := by
  intro p _ K _ h G r
  set S := Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r) with hS
  let D := G.dual.A r
  let ev : D →ₗ[K] Module.Dual K S := S.subtype.dualMap ∘ₗ (CartierDual.toDual K (G.A r)).toLinearMap
  have hev : Function.Surjective ev :=
    (LinearMap.dualMap_surjective_of_injective S.injective_subtype).comp
      (CartierDual.toDual K (G.A r)).surjective
  let J := frobKerIdeal (p ^ r) K D
  have hle : J.restrictScalars K ≤ LinearMap.ker ev := by
    intro χ hχ
    have hT := frobKerIdeal_le_annPowIdeal h G r hχ
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun s => ?_
    obtain ⟨s, hs⟩ := s
    change χ.ofConv s = 0
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hT a
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  let φ : (D ⧸ J) →ₗ[K] Module.Dual K S :=
    (J.restrictScalars K).liftQ ev hle ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv K J).symm.toLinearMap
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hev y
    refine ⟨Ideal.Quotient.mk J x, ?_⟩
    rfl
  have h1 : Module.finrank K S ≤ Module.finrank K (D ⧸ J) := by
    have := LinearMap.finrank_range_le φ
    rw [LinearMap.range_eq_top.2 hφ, finrank_top, Subspace.dual_finrank_eq] at this
    exact this
  have h2 := GlobalTheory.T.finrank_frobeniusKernelQuotient_le_pow_cotangent (p ^ r) K D (pow_pos (Fact.out : p.Prime).pos r)
  have hfin := (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G.dual).1
  have h3 : Module.finrank K (Cot K D) ≤ Module.finrank K G.dual.omega := by
    have := LinearMap.finrank_range_le (G.dual.omegaLevel r)
    rwa [LinearMap.range_eq_top.2 (G.dual.omegaLevel_surjective r), finrank_top] at this
  exact h1.trans (h2.trans (Nat.pow_le_pow_right (pow_pos (Fact.out : p.Prime).pos r) h3))
