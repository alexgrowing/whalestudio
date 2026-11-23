import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem rat_valuation_le_one_eventually (x : ℚ) :
    ∀ᶠ w : HeightOneSpectrum ℤ in Filter.cofinite, w.valuation ℚ x ≤ 1 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

variable {p : ℕ} [Fact p.Prime]

theorem rat_mem_integers_eventually (x : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), algebraMap ℚ (Qv v) x ∈ v.1.adicCompletionIntegers ℚ := by
  have h := (Function.Injective.tendsto_cofinite (f := fun v : AwayP p => v.1) Subtype.val_injective).eventually
    (rat_valuation_le_one_eventually x)
  filter_upwards [h] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 x).trans_le hv

def starLin (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] : (R ⊗[ℚ] G.C) →ₗ[R] (R ⊗[ℚ] G.C) where
  toFun a := (starT G.star R a).unop
  map_add' x y := by rw [map_add, MulOpposite.unop_add]
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y =>
      rw [TensorProduct.smul_tmul', starT_tmul, starT_tmul, TensorProduct.smul_tmul', RingHom.id_apply]
    | add x y hx hy =>
      rw [smul_add, map_add, MulOpposite.unop_add, hx, hy, map_add, MulOpposite.unop_add, smul_add]

theorem starLin_apply (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (a : R ⊗[ℚ] G.C) :
    starLin G R a = (starT G.star R a).unop := rfl

theorem isIntV_star_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a →
      IsIntV G v (starT G.star (Qv v) a).unop := by
  intro p _ G
  have hs : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      ∀ ij : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
        algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr (G.star (Module.finBasis ℚ G.C ij.2)).unop ij.1)
          ∈ v.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun ij => rat_mem_integers_eventually _
  filter_upwards [hs] with v hv a ha i
  rw [← starLin_apply, ← (basV G v).sum_repr a, map_sum, map_sum, Finsupp.finset_sum_apply]
  refine sum_mem fun j _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine mul_mem (ha j) ?_
  have hb : basV G v j = (1 : Qv v) ⊗ₜ Module.finBasis ℚ G.C j := by
    simp [basV, Algebra.TensorProduct.basis_apply]
  rw [hb, starLin_apply, starT_tmul, basV, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Finsupp.mapRange_apply]
  exact hv (i, j)

end GlobalTheory.OrbFinAf
