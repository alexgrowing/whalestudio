import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SimpLemmas

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel

namespace Formalism.L2.SG.Pf.PCountEx

section ZM

end ZM

section Approx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)

theorem approxF (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0) (b : ∀ p, (A p).Fp) :
    ∃ f : F, (∀ p ∈ S, haveI := (A p).lf
        valuation (A p).Fp ((A p).ιF f - b p) ≤ valuation (A p).Fp ((A p).ιF (algebraMap (𝓞 F) F c))) ∧
      ∀ p ∉ S, (A p).ιF f ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) :=
  by apply _root_.UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.approxF <;> assumption

end Approx

section ApproxE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)

theorem iotaE_mem_O (p : HeightOneSpectrum (𝓞 F)) (e : 𝓞 E) : (A p).ιE (e : E) ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have h : IsIntegral ℤ ((A p).ιE (e : E)) := e.2.map (A p).ιE.toIntAlgHom
  exact h.tower_top

theorem alg_mem_O (p : HeightOneSpectrum (𝓞 F)) {t : (A p).Fp} (ht : t ∈ (haveI := (A p).lf; 𝒪[(A p).Fp])) :
    algebraMap (A p).Fp (A p).Ep t ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have h := isIntegral_algebraMap (R := 𝒪[(A p).Fp]) (A := (A p).Ep) (x := ⟨t, ht⟩)
  rw [IsScalarTower.algebraMap_apply 𝒪[(A p).Fp] (A p).Fp (A p).Ep] at h
  exact h

theorem exists_int_span : ∃ (n : ℕ) (e : Fin n → 𝓞 E), Submodule.span F (Set.range fun j => (e j : E)) = ⊤ := by
  let b := Module.finBasis F E
  have hm : ∀ i, ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ ((k : E) * b i) := fun i => by
    have hx : IsAlgebraic ℤ (b i) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (b i))
    obtain ⟨k, hk0, hk⟩ := hx.exists_integral_multiple
    exact ⟨k, hk0, by simpa [zsmul_eq_mul, Algebra.smul_def] using hk⟩
  choose k hk0 hk using hm
  refine ⟨Module.finrank F E, fun i => ⟨(k i : E) * b i, hk i⟩, ?_⟩
  rw [eq_top_iff]
  intro x _
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e1 : b.repr x i • b i = (b.repr x i * ((k i : F))⁻¹) • ((k i : E) * b i) := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀, map_intCast]
    have hk' : ((k i : ℤ) : E) ≠ 0 := by exact_mod_cast hk0 i
    field_simp
  rw [e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem approxE (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0) (a : ∀ p, (A p).Ep) :
    ∃ x : E, (∀ p ∈ S, ∃ o ∈ (A p).O,
        (A p).ιE x - a p = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, (A p).ιE x ∈ (A p).O := by
  obtain ⟨n, e, he⟩ := exists_int_span (F := F) (E := E)

  have hco : ∀ p, ∃ l : Fin n → (A p).Fp, ∑ j, l j • (A p).ιE (e j : E) = a p := by
    intro p
    have hsp : Submodule.span (A p).Fp (Set.range fun j => (A p).ιE (e j : E)) = ⊤ := by
      rw [eq_top_iff, ← (A p).span, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ Submodule.span F (Set.range fun j => (e j : E)) := by rw [he]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact Submodule.subset_span ⟨j, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | smul t y _ hy =>
        rw [Algebra.smul_def, map_mul, (A p).compat, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ hy
    have ha : a p ∈ Submodule.span (A p).Fp (Set.range fun j => (A p).ιE (e j : E)) := by rw [hsp]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun _).1 ha
  choose l hl using hco

  have hf := fun j : Fin n => approxF A S c hc (fun p => l p j)
  choose f hfS hfO using hf
  refine ⟨∑ j, algebraMap F E (f j) * (e j : E), fun p hp => ?_, fun q hq => ?_⟩
  · haveI := (A p).lf
    have hcF : (A p).ιF (algebraMap (𝓞 F) F c) ≠ 0 := by
      rw [map_ne_zero_iff _ (A p).ιF.injective, Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
      exact hc
    have hv0 : valuation (A p).Fp ((A p).ιF (algebraMap (𝓞 F) F c)) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact hcF
    refine ⟨∑ j, algebraMap (A p).Fp (A p).Ep
        (((A p).ιF (f j) - l p j) / (A p).ιF (algebraMap (𝓞 F) F c)) * (A p).ιE (e j : E), ?_, ?_⟩
    · refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ (alg_mem_O A p ?_) (iotaE_mem_O A p (e j))
      rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 hv0)]
      exact hfS j p hp
    · rw [← hl p, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, (A p).compat, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_div_cancel₀ _ hcF, ← sub_mul,
        map_sub]
  · haveI := (A q).lf
    rw [map_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [map_mul, (A q).compat]
    exact Subring.mul_mem _ (alg_mem_O A q (hfO j q hq)) (iotaE_mem_O A q (e j))

end ApproxE

end Formalism.L2.SG.Pf.PCountEx
