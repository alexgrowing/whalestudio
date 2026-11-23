import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeAway
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnW
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ChartIdeal

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

abbrev idealChart (J : Ideal (Poly k N)) (I : Chart x) : Ideal (chartRing k x I) :=
  (idealMod (x := x) J I).comap (Algebra.linearMap (chartRing k x I) Ω)

theorem idealMod_le_range (J : Ideal (Poly k N)) (I : Chart x) :
    idealMod (x := x) J I ≤ LinearMap.range (Algebra.linearMap (chartRing k x I) Ω) := by
  rw [idealMod, Submodule.span_le]
  rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
  exact ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩

theorem idealMod_mono {J J' : Ideal (Poly k N)} (h : J ≤ J') (I : Chart x) :
    idealMod (x := x) J I ≤ idealMod (x := x) J' I := by
  refine Submodule.span_mono ?_
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  exact ⟨f, s, e, h hf, hs, hfe, hse, rfl⟩

theorem idealMod_mul_le (J J' : Ideal (Poly k N)) (I : Chart x) :
    idealMod (x := x) J I * idealMod (x := x) J' I ≤ idealMod (x := x) (J * J') I := by
  rw [idealMod, idealMod, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨f, s, e, hf, hs, hfe, hse, rfl⟩, _, ⟨f', s', e', hf', hs', hfe', hse', rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨f * f', s * s', e + e', Ideal.mul_mem_mul hf hf', mul_mem hs hs',
    hfe.mul hfe', hse.mul hse', ?_⟩
  simp only [map_mul, div_mul_div_comm]

theorem idealChart_mul_le (J J' : Ideal (Poly k N)) (I : Chart x) :
    idealChart J I * idealChart J' I ≤ idealChart (x := x) (J * J') I :=
  Ideal.mul_le.mpr fun a ha b hb => by
    have := idealMod_mul_le (x := x) J J' I (Submodule.mul_mem_mul ha hb)
    simpa using this

theorem idealChart_top (I : Chart x) : idealChart (x := x) (⊤ : Ideal (Poly k N)) I = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  refine Submodule.subset_span ⟨1, 1, 0, Submodule.mem_top, one_mem _, isHomogeneous_one _ _,
    isHomogeneous_one _ _, ?_⟩
  simp

theorem idealChart_prod_le {ι : Type*} (s : Finset ι) (P : ι → Ideal (Poly k N)) (I : Chart x) :
    ∏ i ∈ s, idealChart (P i) I ≤ idealChart (x := x) (∏ i ∈ s, P i) I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Ideal.one_eq_top, idealChart_top, le_refl]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (Ideal.mul_mono_right ih).trans (idealChart_mul_le _ _ I)

theorem idealChart_pow_le (P : Ideal (Poly k N)) (I : Chart x) (n : ℕ) :
    idealChart P I ^ n ≤ idealChart (x := x) (P ^ n) I := by
  induction n with
  | zero => simp only [pow_zero, Ideal.one_eq_top, idealChart_top, le_refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono_left ih).trans (idealChart_mul_le _ _ I)

theorem twist_idealSys_le (F : SubSystem k x Ω) (pp : Ideal (Poly k N)) (I : Chart x) :
    (F.twist (idealSys x pp)).sub I ≤ idealChart pp I • F.sub I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨q, hq, y, hy, rfl⟩
  obtain ⟨a, rfl⟩ := idealMod_le_range pp I hq
  exact Submodule.smul_mem_smul (show a ∈ idealChart pp I from hq) hy

end ChartIdeal

section Algebra

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

theorem le_sup_mul_smul {G F : Submodule A M} {P Q : Ideal A} (hP : F ≤ G ⊔ P • F)
    (hQ : F ≤ G ⊔ Q • F) : F ≤ G ⊔ (P * Q) • F := by
  calc F ≤ G ⊔ P • F := hP
    _ ≤ G ⊔ P • (G ⊔ Q • F) := sup_le_sup_left (Submodule.smul_mono le_rfl hQ) _
    _ ≤ G ⊔ (P * Q) • F := by
      rw [Submodule.smul_sup, Submodule.mul_smul, ← sup_assoc]
      exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _

theorem le_sup_prod_smul {ι : Type*} {G F : Submodule A M} (s : Finset ι) (P : ι → Ideal A)
    (h : ∀ i ∈ s, F ≤ G ⊔ P i • F) : F ≤ G ⊔ (∏ i ∈ s, P i) • F := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact le_sup_mul_smul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem le_sup_pow_smul {G F : Submodule A M} {P : Ideal A} (h : F ≤ G ⊔ P • F) (n : ℕ) :
    F ≤ G ⊔ (P ^ n) • F := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
  | succ n ih => rw [pow_succ]; exact le_sup_mul_smul ih h

end Algebra

theorem StepThree.proof (hAway : StepThree.Away.Statement.{u, w})
    (hOnW : StepThree.OnW.Statement.{u, w}) : StepThree.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK
  classical
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly k N) T.J
  choose! c₀ hc₀ using hOnW k Ω N x T hK
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg T.J (IsNoetherian.noetherian _)
  set s := hfin.toFinset
  refine ⟨∑ p ∈ s, |c₀ p|, fun b hb I => ?_⟩
  have hc : 0 ≤ ∑ p ∈ s, |c₀ p| := Finset.sum_nonneg fun p _ => abs_nonneg _
  set F := (T.L.pow b).twist (twistSys k x (∑ p ∈ s, |c₀ p|))
  set G := Submodule.span (chartRing k x I) (F.secs : Set Ω)
  refine le_antisymm (Submodule.span_le.mpr fun z hz => ?_) ?_
  · exact (Submodule.mem_iInf _).mp hz I
  have h1 : ∀ p ∈ s, F.sub I ≤ G ⊔ idealChart p I • F.sub I := fun p hp => by
    have hp' := hfin.mem_toFinset.mp hp
    refine (hc₀ p hp' b _ hb ?_ I).trans (sup_le_sup_left (twist_idealSys_le F p I) _)
    exact (le_abs_self _).trans (Finset.single_le_sum (fun q _ => abs_nonneg (c₀ q)) hp)
  have h2 := le_sup_pow_smul (le_sup_prod_smul s _ h1) (n * b)
  have hrad : ∏ p ∈ s, p ≤ T.J.radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact le_sInf fun q hq => Ideal.prod_le_inf.trans (Finset.inf_le (hfin.mem_toFinset.mpr hq))
  have h3 : (∏ p ∈ s, idealChart p I) ^ (n * b) ≤ idealChart T.J I ^ b := by
    rw [pow_mul]
    refine Ideal.pow_right_mono ?_ b
    refine (Ideal.pow_right_mono (idealChart_prod_le s (fun p => p) I) n).trans
      ((idealChart_pow_le _ I n).trans ?_)
    exact Submodule.comap_mono (idealMod_mono ((Ideal.pow_right_mono hrad n).trans hn) I)
  have h4 := hAway k Ω N x T b _ hc I
  exact h2.trans (sup_le le_rfl ((Submodule.smul_mono_left h3).trans h4))

end

end GroundTheory.Heights₂.Heights.Kleiman
