import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPointStatement

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField

theorem etSpan_holds : ETSpanStatement := by
  intro E _ _ Y _ _ _ R' hR' r y z hgen a
  set X : Submodule (𝓞 E) Y := Submodule.span (𝓞 E) (Set.range fun b => y b + R' • z b) with hX

  have hdec : ∀ a : Y, ∃ x ∈ X, ∃ t : Y, a = x + R' • t := by
    intro a
    obtain ⟨u, hu, t, rfl⟩ := hgen a
    have hspan : Submodule.span (𝓞 E) (Set.range y) ≤
        X ⊔ LinearMap.range (R' • LinearMap.id : Y →ₗ[𝓞 E] Y) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_sup]
      refine ⟨y b + R' • z b, Submodule.subset_span ⟨b, rfl⟩, R' • (-z b), ⟨-z b, rfl⟩, ?_⟩
      rw [smul_neg, add_neg_cancel_right]
    obtain ⟨x, hx, w, ⟨t', rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hspan hu)
    refine ⟨x, hx, t' + t, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_add, add_assoc]

  let Xz : Submodule ℤ Y := X.restrictScalars ℤ
  let I : Ideal ℤ := Ideal.span {(R' : ℤ)}
  have hfg : (⊤ : Submodule ℤ (Y ⧸ Xz)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule ℤ (Y ⧸ Xz)) ≤ I • ⊤ := by
    intro m _
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective Xz m
    obtain ⟨x, hx, t, rfl⟩ := hdec b
    have hx' : Submodule.Quotient.mk (p := Xz) x = 0 :=
      (Submodule.Quotient.mk_eq_zero Xz).2 ((Submodule.restrictScalars_mem ℤ X x).2 hx)
    rw [Submodule.Quotient.mk_add, hx', zero_add, Submodule.Quotient.mk_smul, ← Nat.cast_smul_eq_nsmul ℤ]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤ hfg hle
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.mem_span_singleton, zero_sub, dvd_neg] at hs1
    have h1 : ((R' : ℤ)) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg R') hs1
    omega
  have hsa : s • a ∈ X := by
    have h0 : s • Submodule.Quotient.mk (p := Xz) a = 0 := hs _ Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.restrictScalars_mem ℤ X _).1 h0
  refine ⟨s.natAbs, Int.natAbs_pos.2 hs0, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℤ]
  rcases Int.natAbs_eq s with h | h
  · rw [← h]
    exact hsa
  · have : ((s.natAbs : ℤ)) = -s := by omega
    rw [this, neg_smul]
    exact X.neg_mem hsa

end Formalism.MainNotions.ModuliIntegralCharts.H1
