import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HRSmulERight

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem incl_mem (o : 𝓞 E) : inclR (F := F) (Fv F v) (o : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨o, trivial, rfl⟩

theorem one_mem_oev : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  have h := incl_mem (F := F) (E := E) v 1
  simpa using h

theorem denseF (c ε : Fv F v) (hε : ε ≠ 0) :
    ∃ b : F, ∃ o ∈ v.adicCompletionIntegers F, algebraMap F (Fv F v) b - c = ε * o := by
  have hO : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v))) := Valued.isOpen_integer _
  have hU : IsOpen {k : Fv F v | (k - c) * ε⁻¹ ∈ v.adicCompletionIntegers F} :=
    hO.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap (v := v) (K := F)).exists_mem_open hU
    ⟨c, by simp [zero_mem]⟩
  refine ⟨b, _, hb, ?_⟩
  field_simp

theorem tmul_eq (c : Fv F v) (x : E) :
    c ⊗ₜ[F] x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c * inclR (F := F) (Fv F v) x := by
  simp [inclR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

theorem alg_alg (b : F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) b) = inclR (F := F) (Fv F v) (algebraMap F E b) := by
  rw [← IsScalarTower.algebraMap_apply]
  simp [inclR]

theorem approx (M : ℤ) (hM : M ≠ 0) (t : Fv F v ⊗[F] E) :
    ∃ e : E, ∃ w ∈ OEv (E := E) v, t - inclR (F := F) (Fv F v) e = (M : Fv F v ⊗[F] E) * w := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | tmul c x =>
    obtain ⟨m, hm, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {x}
    have hi : IsIntegral ℤ (m • x) := hint x (Finset.mem_singleton_self x)
    set o : 𝓞 E := ⟨m • x, hi⟩ with ho
    set mF : Fv F v := algebraMap F (Fv F v) (m : F) with hmF
    have hmF0 : mF ≠ 0 := (map_ne_zero _).2 (Int.cast_ne_zero.2 hm)
    have hMF0 : algebraMap F (Fv F v) (M : F) ≠ 0 := (map_ne_zero _).2 (Int.cast_ne_zero.2 hM)
    obtain ⟨b, u, hu, hb⟩ := denseF v (c / mF) (algebraMap F (Fv F v) (M : F)) hMF0
    refine ⟨algebraMap F E b * (m • x), (⟨-u, neg_mem hu⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (o : E),
      Submodule.smul_mem _ _ (incl_mem v o), ?_⟩
    have hb' : mF * algebraMap F (Fv F v) b - c = mF * (algebraMap F (Fv F v) (M : F) * u) := by
      rw [← hb]; field_simp
    have hb'' := congrArg (algebraMap (Fv F v) (Fv F v ⊗[F] E)) hb'
    simp only [map_sub, map_mul, hmF, alg_alg, map_intCast] at hb''
    have ho' : inclR (F := F) (Fv F v) (o : E) = (m : Fv F v ⊗[F] E) * inclR (F := F) (Fv F v) x := by
      rw [ho]; show inclR (F := F) (Fv F v) (m • x) = _; rw [zsmul_eq_mul, map_mul, map_intCast]
    have hs : (⟨-u, neg_mem hu⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (o : E) =
        -(algebraMap (Fv F v) (Fv F v ⊗[F] E) u * inclR (F := F) (Fv F v) (o : E)) := by
      rw [← neg_mul, ← map_neg, ← Algebra.smul_def]; rfl
    rw [hs, ho', tmul_eq, zsmul_eq_mul, map_mul, map_mul, map_intCast]
    linear_combination (-(inclR (F := F) (Fv F v) x)) * hb''
  | add t t' h1 h2 =>
    obtain ⟨e1, w1, hw1, he1⟩ := h1
    obtain ⟨e2, w2, hw2, he2⟩ := h2
    refine ⟨e1 + e2, w1 + w2, Submodule.add_mem _ hw1 hw2, ?_⟩
    rw [map_add]; linear_combination he1 + he2

def trV : Fv F v ⊗[F] E →ₗ[Fv F v] Fv F v :=
  (Algebra.TensorProduct.rid F (Fv F v) (Fv F v)).toLinearMap ∘ₗ LinearMap.baseChange (Fv F v) (Algebra.trace F E)

theorem trV_tmul (c : Fv F v) (x : E) : trV v (c ⊗ₜ[F] x) = Algebra.trace F E x • c := rfl

theorem trV_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : trV v x ∈ v.adicCompletionIntegers F := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨o, _, rfl⟩ := hx
    change trV v ((1 : Fv F v) ⊗ₜ[F] (o : E)) ∈ _
    rw [trV_tmul, Algebra.smul_def, mul_one]
    have hI : IsIntegral ℤ (Algebra.trace F E (o : E)) := Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
    set r : 𝓞 F := ⟨_, (mem_integralClosure_iff ℤ F).2 hI⟩ with hr
    have h1 : Algebra.trace F E (o : E) = (r : F) := rfl
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (r : F)
    rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers,
      show algebraMap F (Fv F v) (r : F) = ((r : F) : Fv F v) from rfl, this, HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one r
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul c x _ h =>
    change trV v ((c : Fv F v) • x) ∈ _
    rw [map_smul, smul_eq_mul]; exact mul_mem c.2 h

theorem trV_alg (c : Fv F v) :
    trV v (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap F (Fv F v) (Module.finrank F E : F) * c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, trV_tmul,
    ← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one, Algebra.smul_def]

theorem pow_unbdd {a b : WithZero (Multiplicative ℤ)} (ha : 1 < a) (hb : b ≠ 0) :
    ∃ k : ℕ, 1 < b * a ^ k := by
  obtain ⟨β, rfl⟩ := WithZero.ne_zero_iff_exists.1 hb
  have ha0 : a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
  obtain ⟨α, rfl⟩ := WithZero.ne_zero_iff_exists.1 ha0
  have hα : 0 < Multiplicative.toAdd α := by
    have h := WithZero.coe_lt_coe.1 (show ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < α from ha)
    exact Multiplicative.ofAdd_lt.1 h
  refine ⟨(Multiplicative.toAdd β).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_lt_coe,
    ← Multiplicative.toAdd_lt, toAdd_mul, toAdd_pow, toAdd_one]
  rw [nsmul_eq_mul]; push_cast
  have h3 : (|Multiplicative.toAdd β| + 1) * 1 ≤ (|Multiplicative.toAdd β| + 1) * Multiplicative.toAdd α :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  linarith [neg_abs_le (Multiplicative.toAdd β)]

theorem int_of_alg (c : Fv F v) (hc : algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ OEv (E := E) v) :
    c ∈ v.adicCompletionIntegers F := by
  by_contra hn
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hn
  have hpow : ∀ k : ℕ, algebraMap (Fv F v) (Fv F v ⊗[F] E) (c ^ k) ∈ OEv (E := E) v := by
    intro k
    induction k with
    | zero => rw [pow_zero, map_one]; exact one_mem_oev v
    | succ k ih => rw [pow_succ, map_mul]; exact oev_mul v ih hc
  have hd0 : algebraMap F (Fv F v) (Module.finrank F E : F) ≠ 0 :=
    (map_ne_zero _).2 (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  obtain ⟨k, hk⟩ := pow_unbdd hn ((Valuation.ne_zero_iff _).2 hd0)
  have := trV_mem v (hpow k)
  rw [trV_alg, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow] at this
  exact absurd this (not_le.2 hk)

end Gen

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
