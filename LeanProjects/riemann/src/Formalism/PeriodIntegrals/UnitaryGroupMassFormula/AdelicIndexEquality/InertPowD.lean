import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPowDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertQRG
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Hensel

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
open Formalism.MainNotions.S

theorem exists_nonfixed (I : AutInst) : ∃ θ : I.E, star θ ≠ θ := by
  by_contra h
  push_neg at h
  have htop : (⊥ : Subalgebra I.F I.E) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, ha⟩ := RingHom.mem_range.1 ((I.cm.fixed x).1 (h x))
    exact Algebra.mem_bot.2 ⟨a, ha⟩
  have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
  rw [I.cm.deg2] at h1
  exact absurd h1 (by norm_num)

theorem decompE (I : AutInst) (θ : I.E) (hθ : star θ ≠ θ) (e : I.E) :
    ∃ f g : I.F, e = f • (1 : I.E) + g • θ := by
  have hli : LinearIndependent I.F ![(1 : I.E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hθ
      have h' : s • (1 : I.E) = -(t • θ) := eq_neg_of_add_eq_zero_left hst
      have hθeq : algebraMap I.F I.E (-(t⁻¹ * s)) = θ := by
        rw [Algebra.algebraMap_eq_smul_one, neg_smul, mul_smul, h', smul_neg, neg_neg,
          smul_smul, inv_mul_cancel₀ ht, one_smul]
      exact (I.cm.fixed θ).2 (RingHom.mem_range.2 ⟨_, hθeq⟩)
    refine ⟨?_, ht⟩
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact hst.resolve_right one_ne_zero
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [I.cm.deg2])
  have he : e ∈ Submodule.span I.F (Set.range ![(1 : I.E), θ]) := by
    rw [hsp]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun I.F).1 he
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp

theorem decompV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (θ : I.E) (hθ : star θ ≠ θ)
    (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    ∃ p q : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v, x = p ⊗ₜ 1 + q ⊗ₜ θ := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a e =>
    obtain ⟨f, g, rfl⟩ := decompE I θ hθ e
    exact ⟨f • a, g • a, by rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨p, q, rfl⟩ := hx
    obtain ⟨p', q', rfl⟩ := hy
    exact ⟨p + p', q + q', by simp only [TensorProduct.add_tmul]; abel⟩

theorem incL_apply (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :
    incL I v p = p ⊗ₜ 1 := rfl

theorem sigV_incL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :
    sigV I v (incL I v p) = incL I v p := by
  rw [incL_apply]
  simp [sigV]

theorem fixed_incL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (hv : IsFieldAt I v)
    (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) (hx : sigV I v x = x) :
    ∃ p, x = incL I v p := by
  obtain ⟨θ, hθ⟩ := exists_nonfixed I
  obtain ⟨p, q, rfl⟩ := decompV I v θ hθ x
  refine ⟨p, ?_⟩
  haveI : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) := ⟨hv.exists_pair_ne⟩
  have hsig : I.cm.sig θ = star θ := rfl
  have hs : sigV I v (p ⊗ₜ 1 + q ⊗ₜ θ) = p ⊗ₜ 1 + q ⊗ₜ star θ := by
    simp [sigV, hsig]
  have hq : q ⊗ₜ[I.F] (θ - star θ) = 0 := by
    rw [TensorProduct.tmul_sub, sub_eq_zero]
    have h2 := hx
    rw [hs] at h2
    exact (add_left_cancel h2).symm
  have hu : θ - star θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hq1 : incL I v q = 0 := by
    rw [incL_apply]
    calc q ⊗ₜ[I.F] (1 : I.E)
        = (q ⊗ₜ[I.F] (θ - star θ)) * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] (θ - star θ)⁻¹) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hu]
      _ = 0 := by rw [hq, zero_mul]
  have hq0 : q = 0 := (incL I v).injective (hq1.trans (map_zero _).symm)
  rw [hq0, TensorProduct.zero_tmul, add_zero, incL_apply]

theorem trace_integral' : TraceInt := by
  intro I v hv α hα
  haveI : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) := ⟨hv.exists_pair_ne⟩
  have hinv : ∀ y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E, sigV I v (sigV I v y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      have h1 : ∀ e' : I.E, I.cm.sig e' = star e' := fun _ => rfl
      simp [sigV, h1]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  obtain ⟨τ, hτ⟩ := fixed_incL I v hv (α + sigV I v α) (by rw [map_add, hinv, add_comm])
  by_cases hτi : τ ∈ v.adicCompletionIntegers I.F
  · exact ⟨τ, hτi, hτ⟩

  have key : ∀ r₀ : v.adicCompletion I.F, α = incL I v r₀ →
      ∃ t ∈ v.adicCompletionIntegers I.F, α + sigV I v α = incL I v t := by
    rintro r₀ rfl
    have h1 : incL I v (r₀ * r₀) = incL I v 1 := by
      rw [map_mul, map_one, ← hα, sigV_incL]
    have hr0 : r₀ * r₀ = 1 := (incL I v).injective h1
    have hmem : r₀ ∈ v.adicCompletionIntegers I.F := by
      rcases ValuationSubring.mem_or_inv_mem (v.adicCompletionIntegers I.F) r₀ with h | h
      · exact h
      · rwa [inv_eq_of_mul_eq_one_right hr0] at h
    exact ⟨r₀ + r₀, add_mem hmem hmem, by rw [sigV_incL, map_add]⟩
  have hdom : ∀ x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E, x * y = 0 → x = 0 ∨ y = 0 := by
    intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl hx
    · obtain ⟨b, hb⟩ := hv.mul_inv_cancel hx
      right
      calc y = (x * b) * y := by rw [hb, one_mul]
        _ = b * (x * y) := by ring
        _ = 0 := by rw [hxy, mul_zero]
  have hτinv : τ⁻¹ ∈ v.adicCompletionIntegers I.F :=
    (ValuationSubring.mem_or_inv_mem _ τ).resolve_left hτi
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact hτi (zero_mem _)
  set s : v.adicCompletionIntegers I.F := ⟨τ⁻¹ * τ⁻¹, mul_mem hτinv hτinv⟩ with hs
  have hsK : (s : v.adicCompletion I.F) = τ⁻¹ * τ⁻¹ := rfl
  have hsm : s ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers I.F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hτi
    have h1 : ((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) * s = 1 := by
      rw [← hu, Units.inv_mul]
    have h3 := congrArg (v.adicCompletionIntegers I.F).subtype h1
    rw [map_mul, map_one] at h3
    change (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) :
      v.adicCompletion I.F) * (τ⁻¹ * τ⁻¹) = 1 at h3
    have hw : (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) :
        v.adicCompletion I.F) = τ * τ := by
      field_simp at h3
      linear_combination h3
    have hτeq : τ = (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) :
        v.adicCompletion I.F) * τ⁻¹ := by
      rw [hw]
      field_simp
    rw [hτeq]
    exact mul_mem (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F)).2 hτinv
  haveI : HenselianLocalRing (v.adicCompletionIntegers I.F) := inferInstance
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian
    (Polynomial.X ^ 2 + (Polynomial.C s - Polynomial.X)) (by monicity!) 0
    (by simpa using hsm) (by simp)
  have ha2 : a ^ 2 + (s - a) = 0 := by simpa using ha
  have haK : (a : v.adicCompletion I.F) ^ 2 + (τ⁻¹ * τ⁻¹ - a) = 0 := by
    have h := congrArg (v.adicCompletionIntegers I.F).subtype ha2
    rw [map_add, map_pow, map_sub, map_zero] at h
    exact h
  have hr : (τ * a) * (τ - τ * a) = 1 := by
    have e1 : (a : v.adicCompletion I.F) - a ^ 2 = τ⁻¹ * τ⁻¹ := by linear_combination -haK
    calc (τ * a) * (τ - τ * a) = τ * τ * ((a : v.adicCompletion I.F) - a ^ 2) := by ring
      _ = τ * τ * (τ⁻¹ * τ⁻¹) := by rw [e1]
      _ = 1 := by field_simp
  have e2 : incL I v (τ * a) * incL I v (τ - τ * a) = 1 := by
    rw [← map_mul, hr, map_one]
  have e3 : incL I v (τ * a) + incL I v (τ - τ * a) = α + sigV I v α := by
    rw [← map_add, show τ * a + (τ - τ * a) = τ by ring, hτ]
  have hprod : (α - incL I v (τ * a)) * (α - incL I v (τ - τ * a)) = 0 := by
    linear_combination (-α) * e3 + e2 - hα
  rcases hdom _ _ hprod with h | h
  · exact key _ (sub_eq_zero.1 h)
  · exact key _ (sub_eq_zero.1 h)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
