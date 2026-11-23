import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.WeilBound.CoreStatements.RationalSupMetrics.AevalCoordProd

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

private theorem isMultiHomog_mul_rational_sup_metrics {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {f g : MRing ι}
    {d e : K → ℕ} (hf : IsMultiHomog f d) (hg : IsMultiHomog g e) : IsMultiHomog (f * g) (d + e) := by
  classical
  intro m hm k
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf a ha k, hg b hb k]

theorem MultiProjectiveCoordinates.exists_form_with_valuation : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), Birational y → IsRelevant (mCoordIdeal y) → ∀ (a : K → ℤ) (s : Ω), ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜), aeval z h ≠ 0 → ∃ w, HasVal y a s z w := by
  intro K _ ι _ Ω _ y hbir hrel a s
  classical
  choose i hi using hrel
  have hev : ∀ f : MRing ι, eval (fun _ => (1 : Ω)) (mConeMap y f) = aeval y f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => simp [mConeMap]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]; simp [mConeMap]
  have hy : ∀ k, y ⟨k, i k⟩ ≠ 0 := by
    intro k hk
    apply hi k
    show _ ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, hk]
  let mon : (K → ℕ) → ((Σ k, ι k) →₀ ℕ) := fun e =>
    Finsupp.equivFunOnFinite.symm (fun p => if p = ⟨p.1, i p.1⟩ then e p.1 else 0)
  have hmon_homog : ∀ e, IsMultiHomog (monomial (mon e) (1 : ℤ) : MRing ι) e := by
    intro e m hm k
    have hm' := support_monomial_subset hm
    rw [Finset.mem_singleton] at hm'
    subst hm'
    simp [mon]
  have hmon_ne : ∀ e, aeval y (monomial (mon e) (1 : ℤ) : MRing ι) ≠ 0 := by
    intro e
    rw [aeval_monomial, map_one, one_mul, Finsupp.prod]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ ?_
    rw [Finsupp.mem_support_iff] at hp
    by_cases hpe : p = ⟨p.1, i p.1⟩
    · rw [hpe]
      exact hy _
    · exact absurd (by simp [mon, hpe]) hp
  obtain ⟨Mp, hMph, hMpn⟩ : ∃ M : MRing ι, IsMultiHomog M (fun k => (a k).toNat) ∧ aeval y M ≠ 0 :=
    ⟨monomial (mon fun k => (a k).toNat) 1, hmon_homog (fun k => (a k).toNat), hmon_ne (fun k => (a k).toNat)⟩
  obtain ⟨Mn, hMnh, hMnn⟩ : ∃ M : MRing ι, IsMultiHomog M (fun k => (-a k).toNat) ∧ aeval y M ≠ 0 :=
    ⟨monomial (mon fun k => (-a k).toNat) 1, hmon_homog (fun k => (-a k).toNat), hmon_ne (fun k => (-a k).toNat)⟩
  clear hmon_homog hmon_ne
  obtain ⟨d, g0, h0, hg0, hh0, hy0, hgy0⟩ := hbir (s * aeval y Mn / aeval y Mp)
  have hH : IsMultiHomog (h0 * Mn) (d + fun k => (-a k).toNat) := isMultiHomog_mul_rational_sup_metrics hh0 hMnh
  have hG : IsMultiHomog (g0 * Mp) (d + fun k => (a k).toNat) := isMultiHomog_mul_rational_sup_metrics hg0 hMph
  refine ⟨h0 * Mn, ⟨⟨_, hH⟩, ?_⟩, ?_⟩
  · intro hmem
    have hk : mConeMap y (h0 * Mn) = 0 := RingHom.mem_ker.mp hmem
    have hz := congrArg (eval fun _ => (1 : Ω)) hk
    rw [hev, map_zero, map_mul] at hz
    exact mul_ne_zero hy0 hMnn hz
  · intro 𝕜 _ z hz
    refine ⟨aeval z (g0 * Mp) / aeval z (h0 * Mn), _, _, g0 * Mp, h0 * Mn, hG, hH, ?_, ?_, hz, ?_⟩
    · intro k
      simp only [Pi.add_apply]
      push_cast
      omega
    · rw [map_mul, map_mul, hgy0]
      field_simp
    · rw [div_mul_cancel₀ _ hz]
