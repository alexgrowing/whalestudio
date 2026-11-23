import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
open GlobalTheory.BCT

namespace GlobalTheory.ConjRegroup

theorem finsum_fibres {H C : Type} (p : H → C) (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : C, ∑ᶠ x, Set.indicator {x | p x = c} a x := by
  classical
  have h1 : ∀ c : C, ∑ᶠ x, Set.indicator {x | p x = c} a x
      = ∑ x ∈ ha.toFinset, if c = p x then a x else 0 := by
    intro c
    rw [finsum_eq_sum_of_support_subset (s := ha.toFinset)]
    · refine Finset.sum_congr rfl fun x _ => ?_
      simp [Set.indicator_apply, eq_comm]
    · intro x hx
      have : a x ≠ 0 := fun h => hx (by simp [Set.indicator_apply, h])
      simpa using this
  simp_rw [h1]
  rw [finsum_sum_comm]
  · rw [finsum_eq_sum a ha]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [finsum_eq_single _ (p x)]
    · simp
    · intro c hc
      simp [hc]
  · intro x _
    refine (Set.finite_singleton (p x)).subset ?_
    intro c hc
    by_contra h
    exact hc (if_neg h)

theorem mk_eq_iff {H : Type} [Group H] (x y : H) :
    (Quot.mk _ x : TwCl (MonoidHom.id H)) = Quot.mk _ y ↔ ∃ g, y = g⁻¹ * x * g := by
  have he : Equivalence fun x y : H => ∃ g, y = g⁻¹ * x * (MonoidHom.id H) g := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  exact Quot.eq.trans he.eqvGen_iff

theorem conj_injective {H : Type} [Group H] (r : H) :
    Function.Injective fun δ : H ⧸ twCent (MonoidHom.id H) r =>
      Quotient.out δ * r * (Quotient.out δ)⁻¹ := by
  intro δ ε h
  rw [← QuotientGroup.out_eq' δ, ← QuotientGroup.out_eq' ε, QuotientGroup.eq]
  change (Quotient.out δ)⁻¹ * Quotient.out ε * r = r * ((Quotient.out δ)⁻¹ * Quotient.out ε)
  simp only at h
  calc (Quotient.out δ)⁻¹ * Quotient.out ε * r
      = (Quotient.out δ)⁻¹ * (Quotient.out ε * r * (Quotient.out ε)⁻¹) * Quotient.out ε := by group
    _ = r * ((Quotient.out δ)⁻¹ * Quotient.out ε) := by rw [← h]; group

theorem range_conj {H : Type} [Group H] (c : TwCl (MonoidHom.id H)) :
    Set.range (fun δ : H ⧸ twCent (MonoidHom.id H) c.rep =>
      Quotient.out δ * c.rep * (Quotient.out δ)⁻¹)
      = {x | (Quot.mk _ x : TwCl (MonoidHom.id H)) = c} := by
  have hc : (Quot.mk _ c.rep : TwCl (MonoidHom.id H)) = c := Quot.out_eq c
  ext x
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨δ, rfl⟩
    refine Eq.trans ?_ hc
    rw [mk_eq_iff]
    exact ⟨Quotient.out δ, by group⟩
  · intro h
    obtain ⟨g, hg⟩ := (mk_eq_iff x c.rep).1 (h.trans hc.symm)
    refine ⟨QuotientGroup.mk g, ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (twCent (MonoidHom.id H) c.rep) g
    have hk2 : (k : H) * c.rep = c.rep * k := k.2
    rw [hk]
    calc g * k * c.rep * (g * k)⁻¹ = g * (k * c.rep) * (g * k)⁻¹ := by group
      _ = g * c.rep * g⁻¹ := by rw [hk2]; group
      _ = x := by rw [hg]; group

theorem finsum_eq_finsum_classes {H : Type} [Group H] (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H), ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
      a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) := by
  rw [finsum_fibres (fun x => (Quot.mk _ x : TwCl (MonoidHom.id H))) a ha]
  refine finsum_congr fun c => ?_
  rw [← finsum_mem_def, ← range_conj c, finsum_mem_range (conj_injective (TwCl.rep c))]

end GlobalTheory.ConjRegroup
