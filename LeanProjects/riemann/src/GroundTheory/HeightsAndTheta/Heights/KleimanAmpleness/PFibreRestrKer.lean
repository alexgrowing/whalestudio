import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsFibreRestrKer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFibreSectionsFlat
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrQuotTorsionFree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

open scoped Pointwise nonZeroDivisors

noncomputable section

universe u w

section FibreCharts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_secs_iff_forall_sub {Q : SubSystem S x Ω} {y : Ω} : y ∈ Q.secs ↔ ∀ I, y ∈ Q.sub I := by
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]

theorem algebraMap_mul_mem_chart {I : Chart x} (M : Submodule (chartRing S x I) Ω) (d : S) {v : Ω}
    (hv : v ∈ M) : algebraMap S Ω d * v ∈ M := by
  have := M.smul_mem (⟨algebraMap S Ω d, Subalgebra.algebraMap_mem _ d⟩ : chartRing S x I) hv
  rwa [chartRing_smul_def] at this

theorem idealMod_le_idealMod {J J' : Ideal (Poly S N)} (h : J ≤ J') (I : Chart x) :
    idealMod (x := x) J I ≤ idealMod (x := x) J' I := by
  refine Submodule.span_mono ?_
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  exact ⟨f, s, e, h hf, hs, hfe, hse, rfl⟩

theorem mem_twist_idealSys_of_algebraMap_mul_mem {qq : Ideal (Poly S N)} [hq : qq.IsPrime]
    (hle : primeOf (S := S) x ≤ qq) (hconst : ∀ s : S, (C s : Poly S N) ∈ qq → s = 0)
    (Q : LineBundle S x) (I : Chart x) {s₀ : S} (hs₀ : s₀ ≠ 0) {v : Ω} (hv : v ∈ Q.sub I)
    (hsv : algebraMap S Ω s₀ * v ∈ (Q.twist (idealSys x qq)).sub I) :
    v ∈ (Q.twist (idealSys x qq)).sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line] at hsv ⊢
  obtain ⟨Q', hQ'⟩ := Q.invertible I
  have key : ∀ q' ∈ Q', v * q' ∈ (idealSys x qq).sub I := by
    intro q' hq'
    have hA : v * q' ∈ (1 : Submodule (chartRing S x I) Ω) := by
      rw [← hQ']
      exact Submodule.mul_mem_mul hv hq'
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp hA
    have hmemA : v * q' ∈ chartRing S x I := by
      rw [← hb]
      exact b.2
    refine mem_idealMod_of_algebraMap_mul_mem hq (fun p d hp hp0 => hle ((mem_primeOf_of_isHomogeneous x hp).mpr hp0))
      I (fun h => hs₀ (hconst s₀ h)) hmemA ?_
    have : algebraMap S Ω s₀ * v * q' ∈ (idealSys x qq).sub I * Q.sub I * Q' :=
      Submodule.mul_mem_mul hsv hq'
    rw [mul_assoc ((idealSys x qq).sub I), hQ', mul_one, mul_assoc] at this
    exact this
  have h1 : (1 : Ω) ∈ Q.sub I * Q' := by
    rw [hQ']
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hall : ∀ y ∈ Q.sub I * Q', v * y ∈ (idealSys x qq).sub I * Q.sub I := by
    intro y hy
    refine Submodule.mul_induction_on (C := fun y => v * y ∈ (idealSys x qq).sub I * Q.sub I) hy ?_ ?_
    · intro g hg q' hq'
      rw [show v * (g * q') = (v * q') * g by ring]
      exact Submodule.mul_mem_mul (key q' hq') hg
    · intro a b ha hb
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
  simpa using hall 1 h1

theorem exists_mul_sub_mem_of_mem_twist_fibre {F : Type u} [Field F] [Algebra S F] [Algebra F Ω]
    [IsScalarTower S F Ω] (Q : SubSystem S x Ω) {qq : Ideal (Poly S N)}
    (hhom : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq) (𝔪 : Ideal S) {b : F}
    (hb : ∀ a ∈ 𝔪, ∃ d : S, b * algebraMap S F a = algebraMap S F d) (I : Chart x) {t : Ω}
    (ht : t ∈ (Q.twist (idealSys x (qq ⊔ 𝔪.map (C : S →+* Poly S N)))).sub I) :
    ∃ u ∈ (Q.twist (idealSys x qq)).sub I, algebraMap F Ω b * (t - u) ∈ Q.sub I := by
  let D : Submodule (chartRing S x I) Ω :=
    { carrier := {t | ∃ u ∈ (Q.twist (idealSys x qq)).sub I, algebraMap F Ω b * (t - u) ∈ Q.sub I}
      add_mem' := by
        rintro t₁ t₂ ⟨u₁, hu₁, h₁⟩ ⟨u₂, hu₂, h₂⟩
        refine ⟨u₁ + u₂, Submodule.add_mem _ hu₁ hu₂, ?_⟩
        rw [show algebraMap F Ω b * (t₁ + t₂ - (u₁ + u₂)) =
          algebraMap F Ω b * (t₁ - u₁) + algebraMap F Ω b * (t₂ - u₂) by ring]
        exact Submodule.add_mem _ h₁ h₂
      zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩
      smul_mem' := by
        rintro c t ⟨u, hu, h⟩
        refine ⟨c • u, Submodule.smul_mem _ c hu, ?_⟩
        have := Submodule.smul_mem _ c h
        rw [chartRing_smul_def] at this
        rw [chartRing_smul_def, chartRing_smul_def,
          show algebraMap F Ω b * ((c : Ω) * t - (c : Ω) * u) = (c : Ω) * (algebraMap F Ω b * (t - u)) by ring]
        exact this }
  suffices hle : (Q.twist (idealSys x (qq ⊔ 𝔪.map (C : S →+* Poly S N)))).sub I ≤ D from hle ht
  rw [SubSystem.twist_sub_eq_mul_of_line]
  refine Submodule.mul_le.mpr fun r hr y hy => ?_
  refine Submodule.span_induction (p := fun r _ => r * y ∈ D) ?_ ?_ ?_ ?_ hr
  · rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := Submodule.mem_sup.mp hf
    have hsplit : f₁ + f₂ = homogeneousComponent e f₁ + homogeneousComponent e f₂ := by
      rw [← map_add, homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hfe), if_pos rfl]
    have hg₂ : ∀ m, coeff m (homogeneousComponent e f₂) ∈ 𝔪 := by
      intro m
      rw [coeff_homogeneousComponent]
      split_ifs
      · exact (mem_map_C_iff.mp hf₂) m
      · exact 𝔪.zero_mem
    have hg₂h := homogeneousComponent_isHomogeneous e f₂
    refine ⟨aeval x (homogeneousComponent e f₁) / aeval x s * y, ?_, ?_⟩
    · rw [SubSystem.twist_sub_eq_mul_of_line]
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨_, s, e, hhom f₁ hf₁ e, hs,
        homogeneousComponent_isHomogeneous e f₁, hse, rfl⟩) hy
    · have hA : algebraMap F Ω b * (aeval x (homogeneousComponent e f₂) / aeval x s) ∈ chartRing S x I := by
        choose d hd using hb
        have : algebraMap F Ω b * (aeval x (homogeneousComponent e f₂) / aeval x s) =
            ∑ m ∈ (homogeneousComponent e f₂).support,
              algebraMap S Ω (d _ (hg₂ m)) * (aeval x (monomial m (1 : S)) / aeval x s) := by
          conv_lhs => rw [(homogeneousComponent e f₂).as_sum]
          rw [map_sum, Finset.sum_div, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [aeval_monomial, aeval_monomial, map_one, one_mul,
            IsScalarTower.algebraMap_apply S F Ω (d _ (hg₂ m)), ← hd, map_mul,
            ← IsScalarTower.algebraMap_apply S F Ω]
          ring
        rw [this]
        refine Subalgebra.sum_mem _ fun m hm => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
        exact ⟨monomial m 1, s, e, hs, isHomogeneous_monomial _ (by
          rw [Finsupp.degree_eq_weight_one]; exact hg₂h (mem_support_iff.mp hm)), hse, rfl⟩
      have : algebraMap F Ω b * (aeval x (f₁ + f₂) / aeval x s * y -
          aeval x (homogeneousComponent e f₁) / aeval x s * y) =
          (⟨_, hA⟩ : chartRing S x I) • y := by
        rw [chartRing_smul_def, hsplit, map_add]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ hy
  · exact ⟨0, Submodule.zero_mem _, by simp⟩
  · intro a a' _ _ ha ha'
    rw [add_mul]
    exact D.add_mem ha ha'
  · intro c a _ ha
    have := D.smul_mem c ha
    rw [chartRing_smul_def] at this ⊢
    rw [mul_assoc]
    exact this

theorem secs_sup_smul_le_secs_fibre (Q : SubSystem S x Ω) (qq : Ideal (Poly S N)) (𝔪 : Ideal S) :
    (Q.twist (idealSys x qq)).secs ⊔ 𝔪 • Q.secs ≤
      (Q.twist (idealSys x (qq ⊔ 𝔪.map (C : S →+* Poly S N)))).secs := by
  refine sup_le (fun y hy => ?_) (Submodule.smul_le.mpr fun a ha y hy => ?_)
  · rw [mem_secs_iff_forall_sub] at hy ⊢
    intro I
    have := hy I
    rw [SubSystem.twist_sub_eq_mul_of_line] at this ⊢
    exact Submodule.mul_le.mpr (fun a ha b hb =>
      Submodule.mul_mem_mul (idealMod_le_idealMod le_sup_left I ha) hb) this
  · rw [mem_secs_iff_forall_sub] at hy ⊢
    intro I
    rw [SubSystem.twist_sub_eq_mul_of_line, Algebra.smul_def]
    refine Submodule.mul_mem_mul (Submodule.subset_span ⟨C a, 1, 0, Ideal.mem_sup_right
      (Ideal.mem_map_of_mem _ ha), one_mem _, isHomogeneous_C _ _, isHomogeneous_one _ _, by simp⟩) (hy I)

end FibreCharts

theorem FibreRestrKer.proof (hS : SurjectiveClosed.Statement.{u, w}) : FibreRestrKer.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x L 𝔪 h𝔪 qq hq hconst e hsub

  have hhom : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq := fun p hp d => by
    refine mem_of_map_mem_map (F := F) hq hconst ?_
    rw [← homogeneousComponent_map_eq]
    exact hsub.homog _ (Ideal.mem_map_of_mem _ hp) d
  have hle : primeOf (S := S) x ≤ qq := fun p hp => by
    rw [← sum_homogeneousComponent p]
    refine qq.sum_mem fun d _ => mem_of_map_mem_map (F := F) hq hconst (hsub.le ?_)
    have hd := homogeneousComponent_isHomogeneous d p
    rw [mem_primeOf_of_isHomogeneous x (hd.map _), aeval_map_algebraMap]
    exact (mem_primeOf_of_isHomogeneous x hd).mp (homogeneousComponent_mem_primeOf x hp d)

  by_cases h0 : 𝔪 = ⊥
  · subst h0
    refine Eventually.of_forall fun c => ?_
    rw [Ideal.map_bot, sup_bot_eq, Submodule.bot_smul, sup_bot_eq]
  obtain ⟨a₀, ha₀, ha₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have := hq
  obtain ⟨c₀, hc₀⟩ := hS S Ω N x L qq hhom
  filter_upwards [eventually_ge_atTop c₀.toNat] with c hc
  have hcc : c₀ ≤ (c : ℤ) := by omega
  let Q : LineBundle S x := L.tensorProd (twistBundle S x (c : ℤ))
  have hQ : Q.toSubSystem = L.toSubSystem.twist (twistSys S x (c : ℤ)) := rfl
  rw [← hQ]
  refine le_antisymm (fun t ht => ?_) (secs_sup_smul_le_secs_fibre Q.toSubSystem qq 𝔪)

  have h𝔪0 : (𝔪 : FractionalIdeal S⁰ F) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr h0
  let K : Submodule S F := ((Q.toSubSystem.twist (idealSys x qq)).secs ⊔ 𝔪 • Q.toSubSystem.secs).comap
    ((LinearMap.toSpanSingleton F Ω t).restrictScalars S)
  suffices hK : (((𝔪 : FractionalIdeal S⁰ F) * (𝔪 : FractionalIdeal S⁰ F)⁻¹ : FractionalIdeal S⁰ F) :
      Submodule S F) ≤ K by
    have h1 := hK (by rw [mul_inv_cancel₀ h𝔪0]; exact FractionalIdeal.one_mem_one _)
    simpa [K] using h1
  rw [FractionalIdeal.coe_mul]
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  obtain ⟨a', ha', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
  have hb' : ∀ a ∈ 𝔪, ∃ d : S, b * algebraMap S F a = algebraMap S F d := by
    intro a ha
    obtain ⟨d, hd⟩ := (FractionalIdeal.mem_one_iff _).mp ((FractionalIdeal.mem_inv_iff h𝔪0).mp hb _
      ((FractionalIdeal.mem_coeIdeal _).mpr ⟨a, ha, rfl⟩))
    exact ⟨d, hd.symm⟩
  have hbΩ : ∀ a ∈ 𝔪, ∃ d : S, algebraMap S Ω a * algebraMap F Ω b = algebraMap S Ω d := by
    intro a ha
    obtain ⟨d, hd⟩ := hb' a ha
    refine ⟨d, ?_⟩
    rw [IsScalarTower.algebraMap_apply S F Ω a, IsScalarTower.algebraMap_apply S F Ω d, ← hd, map_mul,
      mul_comm]

  have hdec : ∀ I, ∃ u ∈ (Q.twist (idealSys x qq)).sub I, algebraMap F Ω b * (t - u) ∈ Q.sub I :=
    fun I => exists_mul_sub_mem_of_mem_twist_fibre (F := F) Q.toSubSystem hhom 𝔪 hb' I
      (mem_secs_iff_forall_sub.mp ht I)
  choose u hu hbu using hdec

  obtain ⟨d₀, hd₀⟩ := hbΩ a₀ ha₀
  have hcompat : ∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 →
      algebraMap F Ω b * (t - u I₁) - algebraMap F Ω b * (t - u I₂) ∈
        ((L.twist (twistSys S x (c : ℤ))).twist (idealSys x qq)).sub I₂ := by
    intro I₁ I₂ h
    refine mem_twist_idealSys_of_algebraMap_mul_mem hle hconst Q I₂ ha₀0
      (Submodule.sub_mem _ (Q.mono I₁ I₂ h _ (hbu I₁)) (hbu I₂)) ?_
    rw [show algebraMap S Ω a₀ * (algebraMap F Ω b * (t - u I₁) - algebraMap F Ω b * (t - u I₂)) =
      algebraMap S Ω d₀ * (u I₂ - u I₁) by rw [← hd₀]; ring]
    exact algebraMap_mul_mem_chart _ d₀ (Submodule.sub_mem _ (hu I₂)
      ((Q.toSubSystem.twist (idealSys x qq)).mono I₁ I₂ h _ (hu I₁)))
  obtain ⟨τ, hτ, hτs⟩ := hc₀ c hcc (fun I => algebraMap F Ω b * (t - u I)) (fun I => hbu I) hcompat

  obtain ⟨d', hd'⟩ := hbΩ a' ha'
  change (algebraMap S F a' * b) • t ∈ (Q.toSubSystem.twist (idealSys x qq)).secs ⊔ 𝔪 • Q.toSubSystem.secs
  have hsplit : (algebraMap S F a' * b) • t =
      (algebraMap S Ω a' * (algebraMap F Ω b * t) - a' • τ) + a' • τ := by
    rw [sub_add_cancel, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply S F Ω a', mul_assoc]
  rw [hsplit]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
    (Submodule.mem_sup_right (Submodule.smul_mem_smul ha' hτ))
  rw [mem_secs_iff_forall_sub]
  intro I
  rw [show algebraMap S Ω a' * (algebraMap F Ω b * t) - a' • τ = algebraMap S Ω d' * u I -
      algebraMap S Ω a' * (τ - algebraMap F Ω b * (t - u I)) by rw [Algebra.smul_def, ← hd']; ring]
  exact Submodule.sub_mem _ (algebraMap_mul_mem_chart _ d' (hu I)) (algebraMap_mul_mem_chart _ a' (hτs I))

end

end GroundTheory.Heights₂.Heights.Kleiman
