import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pTfMulL :
    TfAdm → TfAct → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K) → TfMulL := by
  intro hAdm hAc hIff X M M' _ _ _ T L' Kw hF hAp t r hr hr'
  funext g₀
  set Φ : X → ℂ := fun y => T.tf r (y⁻¹ * g₀) with hΦ
  have hTy : T.IsTy Φ := by
    intro k hk g
    have hki : k⁻¹ ∈ T.K := T.K.inv_mem hk
    simp only [hΦ, mul_inv_rev, mul_assoc]
    rw [((hAdm X M T r hr).2 k⁻¹ hki (g⁻¹ * g₀)).1, smul_eq_mul]
    congr 2
    have e : (⟨T.L.pr k⁻¹, T.fact.2 _ hki⟩ : T.J) = (⟨T.L.pr k, T.fact.2 _ hk⟩ : T.J)⁻¹ :=
      Subtype.ext (map_inv _ _)
    rw [e, map_inv, inv_inv]
  have key := hAc X M M' T L' Kw hF hAp t 1 ⟨fun g => by group, map_one _⟩ ℂ Φ hTy 1
  have lhs : conv T.K₀ (T.tf (L'.loc t)) (T.tf r) g₀ = Formalism.UG.hAct T.K₀ (T.tf (L'.loc t * 1)) Φ 1 := by
    simp [conv, Formalism.UG.hAct, hΦ, smul_eq_mul]
  rw [lhs, key]
  have memKrK : ∀ y, y ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K → L'.pr y ∈ Kw := by
    intro y hy
    rw [DoubleCoset.mem_doubleCoset] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    simp only [map_mul, hr', mul_one]
    exact Kw.mul_mem (hF.2 a ha) (hF.2 b hb)
  simp only [hΦ, one_mul, smul_eq_mul]
  rw [finsum_eq_single _ ((L'.pr g₀ : M' ⧸ Kw)) ?_]
  · obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul Kw (L'.pr g₀)
    rw [hw]
    have h1 : (L'.pr g₀ * w ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw) ↔
        L'.pr g₀ ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw := by
      simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
      constructor
      · rintro ⟨a, ha, b, hb, e⟩
        refine ⟨a, ha, b * (w : M')⁻¹, Kw.mul_mem hb (Kw.inv_mem w.2), ?_⟩
        calc L'.pr g₀ = L'.pr g₀ * w * (w : M')⁻¹ := by group
          _ = a * t * b * (w : M')⁻¹ := by rw [e]
          _ = a * t * (b * (w : M')⁻¹) := by group
      · rintro ⟨a, ha, b, hb, e⟩
        exact ⟨a, ha, b * w, Kw.mul_mem hb w.2, by rw [e]; group⟩
    have h2 : ((L'.loc (L'.pr g₀ * w))⁻¹ * g₀ ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K) ↔
        (L'.loc (L'.pr g₀))⁻¹ * g₀ ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K := by
      have hwK : L'.loc w ∈ T.K := hF.1 w w.2
      have e : (L'.loc (L'.pr g₀ * w))⁻¹ * g₀ = (L'.loc w)⁻¹ * ((L'.loc (L'.pr g₀))⁻¹ * g₀) := by
        rw [map_mul, mul_inv_rev, mul_assoc]
      rw [e]
      simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
      constructor
      · rintro ⟨a, ha, b, hb, e2⟩
        refine ⟨L'.loc w * a, T.K.mul_mem hwK ha, b, hb, ?_⟩
        calc (L'.loc (L'.pr g₀))⁻¹ * g₀
            = L'.loc w * ((L'.loc w)⁻¹ * ((L'.loc (L'.pr g₀))⁻¹ * g₀)) := by group
          _ = L'.loc w * (a * r * b) := by rw [e2]
          _ = L'.loc w * a * r * b := by group
      · rintro ⟨a, ha, b, hb, e2⟩
        exact ⟨(L'.loc w)⁻¹ * a, T.K.mul_mem (T.K.inv_mem hwK) ha, b, hb, by rw [e2]; group⟩
    have hprm : ∀ m, T.L.pr ((L'.loc m)⁻¹ * g₀) = T.L.pr g₀ := by
      intro m
      rw [map_mul, map_inv, hAp.1, inv_one, one_mul]
    simp only [TyLev.tf, dosetInd, Set.indicator_apply, Pi.one_apply, hprm, h1, h2,
      hIff X M' L' T.K Kw hF t r hr' g₀]
    split_ifs <;> simp_all
  · intro x hx
    have hy : (L'.loc (Quotient.out x))⁻¹ * g₀ ∉ DoubleCoset.doubleCoset r (T.K : Set X) T.K := by
      intro hm
      apply hx
      have hh := memKrK _ hm
      rw [map_mul, map_inv, L'.pr_loc] at hh
      rw [← QuotientGroup.out_eq' x]
      exact QuotientGroup.eq.2 hh
    simp [TyLev.tf, dosetInd, Set.indicator_apply, hy]
