import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CmpCMemMIff
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorThird

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain WithZero

section CRT

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem exists_prime_to_le (P : HeightOneSpectrum R) (d : R) (hd : d ≠ 0) :
    ∃ s : R, s ∉ P.asIdeal ∧ ∀ v : HeightOneSpectrum R, v ≠ P → v.intValuation s ≤ v.intValuation d := by
  classical
  have hI : (Ideal.span {d} : Ideal R) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  let S : Finset (HeightOneSpectrum R) := (Ideal.finite_factors hI).toFinset ∪ {P}
  let n : HeightOneSpectrum R → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal R)).factors
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => if v = P then 1 else n v) (fun v _ => v.prime)
    (fun v _ v' _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then 1 else 0)
  refine ⟨y, ?_, fun v hv => ?_⟩
  · intro hyP
    have h1 := hy P (Finset.mem_union_right _ (Finset.mem_singleton_self P))
    simp only [↓reduceIte, pow_one] at h1
    have h2 : (1 : R) ∈ P.asIdeal := by
      have := P.asIdeal.sub_mem hyP h1
      simpa using this
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · by_cases hvd : v.asIdeal ∣ Ideal.span {d}
    · have hvS : v ∈ S := Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 hvd)
      have h1 := hy v hvS
      simp only [if_neg hv, sub_zero] at h1
      rw [v.intValuation_if_neg hd]
      exact (v.intValuation_le_pow_iff_mem y (n v)).2 h1
    · have h3 : v.intValuation d = 1 := by
        apply le_antisymm (v.intValuation_le_one d)
        by_contra hlt
        exact hvd ((v.intValuation_lt_one_iff_dvd d).1 (lt_of_not_ge hlt))
      rw [h3]
      exact v.intValuation_le_one y

end CRT

variable {D : D7}

theorem exists_den (u : D.what₂.Word) (x : ((D.fm u).lat 0).V) :
    ∃ d : 𝓞 D.what₂.LL, d ≠ 0 ∧ d • x ∈ ((D.fm u).lat 0).L :=
  _root_.UpperTheory.Reformulated.B.ExistsDenominatorThird.exists_den u x

theorem locWBack_proved (T : ∀ u : D.what₂.Word, Forms0 D u) : LocWBack T := by
  intro u w x hx
  have key : ∀ (r : 𝓞 D.what₂.LL) (v : ((D.fm u).lat 0).V), r • v = (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) • v :=
    fun r v => (algebraMap_smul D.what₂.LL r v).symm
  obtain ⟨d, hd0, hdL⟩ := exists_den u x
  obtain ⟨s, hsP, hsv⟩ := exists_prime_to_le (D.plEq w) d hd0
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ Submodule.zero_mem _)
  have hsL : s • x ∈ ((D.fm u).lat 0).L := by
    refine (((T u).val0).lat (s • x)).2 ?_
    intro w' c B hB
    by_cases hw : w' = w
    · subst hw
      have hsint : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ∈ intW D.what₂.places w' := by
        show (0 : WithTop ℤ) ≤ D.what₂.places.val w' _
        rw [val_nonneg_iff, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact (D.plEq w').intValuation_le_one s
      obtain ⟨P, hP, hPx⟩ := hx c B hB
      refine ⟨D.what₂.embLL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s) • P, intSpan_smul w' _ _ hsint hP, fun t => ?_⟩
      rw [key, LinearMap.map_smulₛₗ, LinearMap.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hPx t]
    · have hne : D.plEq w' ≠ D.plEq w := fun h => hw (D.plEq.injective h)
      have hdne : algebraMap (𝓞 D.what₂.LL) D.what₂.LL d ≠ 0 := by
        simpa using hd0
      set q : D.what₂.LL := algebraMap (𝓞 D.what₂.LL) D.what₂.LL s / algebraMap (𝓞 D.what₂.LL) D.what₂.LL d with hq
      have hqint : q ∈ intW D.what₂.places w' := by
        show (0 : WithTop ℤ) ≤ D.what₂.places.val w' _
        rw [val_nonneg_iff, hq, map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        have hdv : (D.plEq w').intValuation d ≠ 0 := (D.plEq w').intValuation_ne_zero d hd0
        rw [div_le_one₀ (zero_lt_iff.2 hdv)]
        exact hsv _ hne
      have hsx : s • x = q • (d • x) := by
        rw [key, key, smul_smul, hq, div_mul_cancel₀ _ hdne]
      obtain ⟨P, hP, hPx⟩ := (((T u).val0).lat (d • x)).1 hdL w' c B hB
      refine ⟨D.what₂.embLL q • P, intSpan_smul w' _ q hqint hP, fun t => ?_⟩
      rw [hsx, LinearMap.map_smulₛₗ, LinearMap.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hPx t]

  have hsu : (D.plEq w).intValuation s = 1 := by
    apply le_antisymm ((D.plEq w).intValuation_le_one s)
    by_contra hlt
    exact hsP (((D.plEq w).intValuation_lt_one_iff_mem s).1 (lt_of_not_ge hlt))
  have hsne : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by simpa using hs0
  have htint : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ ∈ intW D.what₂.places w := by
    show (0 : WithTop ℤ) ≤ D.what₂.places.val w _
    rw [val_nonneg_iff, map_inv₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hsu, inv_one]
  have hx' : x = (⟨_, htint⟩ : intW D.what₂.places w) • (s • x) := by
    rw [Subring.smul_def, key, smul_smul, inv_mul_cancel₀ hsne, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsL)

theorem locWCrit_proved (T : ∀ u : D.what₂.Word, Forms0 D u) : LocWCrit T :=
  locWCrit_of T (locWBack_proved T)

end Formalism.L2.G.Cmp
