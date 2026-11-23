import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BanachHol

noncomputable section

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

def ehat {G : Type} (E : ℂ → G → ℂ) (s₀ : ℂ) : ℕ → ℂ → G → ℂ
  | 0 => E
  | j + 1 => fun z g => dslope (fun w => ehat E s₀ j w g) s₀ z

section Core

variable {G : Type} [Group G] [TopologicalSpace G] [LocallyCompactSpace G] (hDS : DslopeFam) (Γ : Subgroup G)
  (Λ : Set ((G → ℂ) → ℂ)) (T : (G → ℂ) → G → ℂ) (I1 : G → ℂ) (s₀ : ℂ) (B : Set ℂ) (hB : IsOpen B) (hs : s₀ ∈ B)
  (E : ℂ → G → ℂ) (cz : ℂ → ℂ) (k₀ : ℕ) (d1 : ℂ → ℂ)

def PJ (j : ℕ) : Prop :=
  ContinuousOn (fun y : ℂ × G => ehat E s₀ j y.1 y.2) (B ×ˢ univ) ∧ (∀ g, DifferentiableOn ℂ (ehat E s₀ j · g) B) ∧
    (∀ z ∈ B, ∀ g, E z g = (z - s₀) ^ j * ehat E s₀ j z g) ∧
    (∀ z ∈ B, ∀ γ ∈ Γ, ∀ g, ehat E s₀ j z (γ * g) = ehat E s₀ j z g) ∧
    ∀ z ∈ B, ∀ g, T (ehat E s₀ j z) g = cz (z - s₀) * ehat E s₀ j z g

include hB hs in
theorem eventually_mem_ne : ∀ᶠ z in 𝓝[≠] s₀, z ∈ B ∧ z ≠ s₀ := by
  have h1 : ∀ᶠ z in 𝓝[≠] s₀, z ∈ B := nhdsWithin_le_nhds (hB.mem_nhds hs)
  have h2 : ∀ᶠ z in 𝓝[≠] s₀, z ≠ s₀ := self_mem_nhdsWithin
  exact h1.and h2

theorem lam_zero' {l : (G → ℂ) → ℂ}
    (hlin : ∀ (a : ℂ) (F F' : G → ℂ), Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) →
      (∀ γ ∈ Γ, ∀ g, F' (γ * g) = F' g) → l (a • F + F') = a * l F + l F') : l 0 = 0 := by
  have h := hlin 1 0 0 continuous_zero continuous_zero (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [one_smul, add_zero, one_mul] at h
  simpa using h

theorem lam_smul' {l : (G → ℂ) → ℂ}
    (hlin : ∀ (a : ℂ) (F F' : G → ℂ), Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) →
      (∀ γ ∈ Γ, ∀ g, F' (γ * g) = F' g) → l (a • F + F') = a * l F + l F') (a : ℂ) (F : G → ℂ) (hF : Continuous F)
    (hi : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) : l (fun g => a * F g) = a * l F := by
  have h := hlin a F 0 hF continuous_zero hi (fun _ _ _ => rfl)
  rw [lam_zero' Γ hlin, add_zero, add_zero] at h
  rw [← h]
  congr 1

include hB hs in
theorem lam_limit {j : ℕ} (hj : j ≤ k₀) (hP : PJ Γ T s₀ B E cz j) (l : (G → ℂ) → ℂ)
    (hlin : ∀ (a : ℂ) (F F' : G → ℂ), Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) →
      (∀ γ ∈ Γ, ∀ g, F' (γ * g) = F' g) → l (a • F + F') = a * l F + l F')
    (hcont : ContinuousAt (fun z => l (ehat E s₀ j z)) s₀) (hd1 : ContinuousAt d1 s₀)
    (hloc : ∃ H : ℂ → ℂ, ContinuousAt H s₀ ∧ H s₀ = l I1 ∧ ∀ᶠ z in 𝓝[≠] s₀, l (E z) = (z - s₀) ^ k₀ * d1 z * H z) :
    l (ehat E s₀ j s₀) = (0 : ℂ) ^ (k₀ - j) * d1 s₀ * l I1 := by
  obtain ⟨H, hHc, hH0, hHe⟩ := hloc
  have hev : ∀ᶠ z in 𝓝[≠] s₀, l (ehat E s₀ j z) = (z - s₀) ^ (k₀ - j) * d1 z * H z := by
    filter_upwards [hHe, eventually_mem_ne s₀ B hB hs] with z hz hzB
    have hcg : Continuous (ehat E s₀ j z) :=
      hP.1.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hzB.1, trivial⟩)
    have hig : ∀ γ ∈ Γ, ∀ g, ehat E s₀ j z (γ * g) = ehat E s₀ j z g := hP.2.2.2.1 z hzB.1
    have hEz : E z = fun g => (z - s₀) ^ j * ehat E s₀ j z g := funext (hP.2.2.1 z hzB.1)
    rw [hEz, lam_smul' Γ hlin _ _ hcg hig] at hz
    have hne : (z - s₀) ^ j ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzB.2)
    apply mul_left_cancel₀ hne
    rw [hz, ← mul_assoc, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]
  have h1 : Tendsto (fun z => l (ehat E s₀ j z)) (𝓝[≠] s₀) (𝓝 (l (ehat E s₀ j s₀))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hca : ContinuousAt (fun z => (z - s₀) ^ (k₀ - j) * d1 z * H z) s₀ :=
    (((continuousAt_id.sub continuousAt_const).pow _).mul hd1).mul hHc
  have h2 := hca.tendsto.mono_left (nhdsWithin_le_nhds (s := {s₀}ᶜ))
  simp only [sub_self] at h2
  rw [← hH0]
  exact tendsto_nhds_unique (h1.congr' hev) h2

include hB hs in
theorem vanish {j : ℕ} (hj : j < k₀) (hP : PJ Γ T s₀ B E cz j) (hd1 : ContinuousAt d1 s₀) (hcz0 : cz 0 ≠ 0)
    (hΛlin : ∀ l ∈ Λ, ∀ (a : ℂ) (F F' : G → ℂ), Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) →
      (∀ γ ∈ Γ, ∀ g, F' (γ * g) = F' g) → l (a • F + F') = a * l F + l F')
    (hΛcont : ∀ l ∈ Λ, ∀ F : ℂ → G → ℂ, ContinuousOn (fun y : ℂ × G => F y.1 y.2) (B ×ˢ univ) →
      (∀ g, DifferentiableOn ℂ (F · g) B) → (∀ z ∈ B, ∀ γ ∈ Γ, ∀ g, F z (γ * g) = F z g) → ContinuousAt (fun z => l (F z)) s₀)
    (hΛloc : ∀ l ∈ Λ, ∃ H : ℂ → ℂ, ContinuousAt H s₀ ∧ H s₀ = l I1 ∧
      ∀ᶠ z in 𝓝[≠] s₀, l (E z) = (z - s₀) ^ k₀ * d1 z * H z)
    (hTsing : ∀ F, Continuous F → (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) → (∀ l ∈ Λ, l F = 0) → ∀ g, T F g = 0) :
    ∀ g, ehat E s₀ j s₀ g = 0 := by
  have hFc : Continuous (ehat E s₀ j s₀) :=
    hP.1.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hs, trivial⟩)
  have hFi := hP.2.2.2.1 s₀ hs
  have hl : ∀ l ∈ Λ, l (ehat E s₀ j s₀) = 0 := by
    intro l hl
    rw [lam_limit Γ T I1 s₀ B hB hs E cz k₀ d1 hj.le hP l (hΛlin l hl)
      (hΛcont l hl _ hP.1 hP.2.1 hP.2.2.2.1) hd1 (hΛloc l hl), zero_pow (Nat.sub_ne_zero_of_lt hj),
      zero_mul, zero_mul]
  intro g
  have h1 := hTsing _ hFc hFi hl g
  have h2 := hP.2.2.2.2 s₀ hs g
  rw [h1, sub_self] at h2
  exact (mul_eq_zero.mp h2.symm).resolve_left hcz0

include hB hs in
theorem step {j : ℕ} (hDS : DslopeFam) (hP : PJ Γ T s₀ B E cz j) (hvan : ∀ g, ehat E s₀ j s₀ g = 0)
    (hcz : Continuous cz)
    (hTlin : ∀ (a : ℂ) (F F' : G → ℂ), Continuous F → Continuous F' → ∀ g, T (fun x => a * F x + F' x) g = a * T F g + T F' g)
    (hT0 : ∀ g, T (fun _ => 0) g = 0)
    (hTcont : ∀ F : ℂ → G → ℂ, ContinuousOn (fun y : ℂ × G => F y.1 y.2) (B ×ˢ univ) → (∀ g, DifferentiableOn ℂ (F · g) B) →
      ∀ g, ContinuousOn (fun z => T (F z) g) B) :
    PJ Γ T s₀ B E cz (j + 1) := by
  obtain ⟨hc1, hd1'⟩ := hDS G B s₀ (ehat E s₀ j) hB hs hP.1 hP.2.1 hvan
  have hrel : ∀ z ∈ B, z ≠ s₀ → ∀ g, ehat E s₀ (j + 1) z g = (z - s₀)⁻¹ * ehat E s₀ j z g := by
    intro z _ hne g
    show dslope (fun w => ehat E s₀ j w g) s₀ z = _
    rw [dslope_of_ne _ hne, slope_def_field, hvan g, sub_zero, div_eq_inv_mul]
  have hgen : ∀ z ∈ B, z ≠ s₀ → ∀ g, T (ehat E s₀ (j + 1) z) g = cz (z - s₀) * ehat E s₀ (j + 1) z g := by
    intro z hz hne g
    have hFc : Continuous (ehat E s₀ j z) :=
      hP.1.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hz, trivial⟩)
    have key : T (ehat E s₀ (j + 1) z) g = (z - s₀)⁻¹ * T (ehat E s₀ j z) g := by
      have h := hTlin ((z - s₀)⁻¹) (ehat E s₀ j z) (fun _ => 0) hFc continuous_const g
      rw [hT0 g, add_zero] at h
      rw [← h]
      congr 1
      funext x
      rw [hrel z hz hne x]
      simp
    rw [key, hP.2.2.2.2 z hz g, hrel z hz hne g]
    ring
  refine ⟨hc1, hd1', ?_, ?_, ?_⟩
  · intro z hz g
    by_cases hne : z = s₀
    · subst hne
      rw [hP.2.2.1 z hz g, hvan g, sub_self, mul_zero, zero_pow (Nat.succ_ne_zero j), zero_mul]
    · rw [hP.2.2.1 z hz g, hrel z hz hne g, pow_succ, mul_assoc, ← mul_assoc (z - s₀),
        mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_mul]
  · intro z hz γ hγ g
    by_cases hne : z = s₀
    · subst hne
      show dslope (fun w => ehat E z j w (γ * g)) z z = dslope (fun w => ehat E z j w g) z z
      rw [dslope_same, dslope_same]
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hB.mem_nhds hz] with w hw
      exact hP.2.2.2.1 w hw γ hγ g
    · rw [hrel z hz hne, hrel z hz hne, hP.2.2.2.1 z hz γ hγ g]
  · intro z hz g
    by_cases hne : z = s₀
    · subst hne
      have hA : ContinuousOn (fun w => T (ehat E z (j + 1) w) g) B := hTcont _ hc1 hd1' g
      have hBc : ContinuousAt (fun w => cz (w - z) * ehat E z (j + 1) w g) z :=
        ((hcz.comp (continuous_id.sub continuous_const)).continuousAt).mul
          ((hd1' g).continuousOn.continuousAt (hB.mem_nhds hz))
      have hlim1 := (hA.continuousAt (hB.mem_nhds hz)).tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
      have hlim2 := hBc.tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
      have heq : (fun w => T (ehat E z (j + 1) w) g) =ᶠ[𝓝[≠] z] (fun w => cz (w - z) * ehat E z (j + 1) w g) := by
        filter_upwards [eventually_mem_ne z B hB hz] with w hw
        exact hgen w hw.1 hw.2 g
      exact tendsto_nhds_unique (hlim1.congr' heq) hlim2
    · exact hgen z hz hne g

include hB hs in
theorem core (hDS : DslopeFam) (hcz : Continuous cz) (hcz0 : cz 0 ≠ 0) (hd1 : ContinuousAt d1 s₀)
    (hΛlin : ∀ l ∈ Λ, ∀ (a : ℂ) (F F' : G → ℂ), Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) →
      (∀ γ ∈ Γ, ∀ g, F' (γ * g) = F' g) → l (a • F + F') = a * l F + l F')
    (hΛcont : ∀ l ∈ Λ, ∀ F : ℂ → G → ℂ, ContinuousOn (fun y : ℂ × G => F y.1 y.2) (B ×ˢ univ) →
      (∀ g, DifferentiableOn ℂ (F · g) B) → (∀ z ∈ B, ∀ γ ∈ Γ, ∀ g, F z (γ * g) = F z g) → ContinuousAt (fun z => l (F z)) s₀)
    (hΛloc : ∀ l ∈ Λ, ∃ H : ℂ → ℂ, ContinuousAt H s₀ ∧ H s₀ = l I1 ∧
      ∀ᶠ z in 𝓝[≠] s₀, l (E z) = (z - s₀) ^ k₀ * d1 z * H z)
    (hTsing : ∀ F, Continuous F → (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) → (∀ l ∈ Λ, l F = 0) → ∀ g, T F g = 0)
    (hTlin : ∀ (a : ℂ) (F F' : G → ℂ), Continuous F → Continuous F' → ∀ g, T (fun x => a * F x + F' x) g = a * T F g + T F' g)
    (hI1c : Continuous I1) (hI1i : ∀ γ ∈ Γ, ∀ g, I1 (γ * g) = I1 g) (hTI : ∀ g, T I1 g = cz 0 * I1 g)
    (hTcont : ∀ F : ℂ → G → ℂ, ContinuousOn (fun y : ℂ × G => F y.1 y.2) (B ×ˢ univ) → (∀ g, DifferentiableOn ℂ (F · g) B) →
      ∀ g, ContinuousOn (fun z => T (F z) g) B)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (B ×ˢ univ)) (hEh : ∀ g, DifferentiableOn ℂ (E · g) B)
    (hEi : ∀ z ∈ B, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g)
    (hTE : ∀ z ∈ B, ∀ g, T (E z) g = cz (z - s₀) * E z g) :
    ∃ Ek : ℂ → G → ℂ, ContinuousOn (fun y : ℂ × G => Ek y.1 y.2) (B ×ˢ univ) ∧ (∀ g, DifferentiableOn ℂ (Ek · g) B) ∧
      (∀ z ∈ B, ∀ g, E z g = (z - s₀) ^ k₀ * Ek z g) ∧ ∀ g, Ek s₀ g = d1 s₀ * I1 g := by
  have hT0 : ∀ g, T (fun _ => 0) g = 0 :=
    hTsing (fun _ => 0) continuous_const (fun _ _ _ => rfl) (fun l hl => lam_zero' Γ (hΛlin l hl))
  have hP0 : PJ Γ T s₀ B E cz 0 :=
    ⟨hEc, hEh, fun z _ g => by rw [pow_zero, one_mul]; rfl, hEi, hTE⟩
  have hall : ∀ j, j ≤ k₀ → PJ Γ T s₀ B E cz j := by
    intro j
    induction j with
    | zero => intro _; exact hP0
    | succ i ih =>
      intro hi
      have hPi := ih (Nat.le_of_succ_le hi)
      have hv := vanish Γ Λ T I1 s₀ B hB hs E cz k₀ d1 hi hPi hd1 hcz0 hΛlin hΛcont hΛloc hTsing
      exact step Γ T s₀ B hB hs E cz hDS hPi hv hcz hTlin hT0 hTcont
  have hPk := hall k₀ le_rfl
  refine ⟨ehat E s₀ k₀, hPk.1, hPk.2.1, hPk.2.2.1, ?_⟩
  have hFc : Continuous (ehat E s₀ k₀ s₀) :=
    hPk.1.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hs, trivial⟩)
  have hFi := hPk.2.2.2.1 s₀ hs
  have hl : ∀ l ∈ Λ, l (fun x => (-d1 s₀) * I1 x + ehat E s₀ k₀ s₀ x) = 0 := by
    intro l hl
    have h1 := lam_limit Γ T I1 s₀ B hB hs E cz k₀ d1 le_rfl hPk l (hΛlin l hl)
      (hΛcont l hl _ hPk.1 hPk.2.1 hPk.2.2.2.1) hd1 (hΛloc l hl)
    have h2 := hΛlin l hl (-d1 s₀) I1 (ehat E s₀ k₀ s₀) hI1c hFc hI1i hFi
    rw [Nat.sub_self, pow_zero, one_mul] at h1
    calc l (fun x => (-d1 s₀) * I1 x + ehat E s₀ k₀ s₀ x) = l ((-d1 s₀) • I1 + ehat E s₀ k₀ s₀) := rfl
      _ = 0 := by rw [h2, h1]; ring
  have hz := hTsing (fun x => (-d1 s₀) * I1 x + ehat E s₀ k₀ s₀ x)
    (show Continuous (fun x => (-d1 s₀) * I1 x + ehat E s₀ k₀ s₀ x) from (continuous_const.mul hI1c).add hFc)
    (fun γ hγ g => by
      show -d1 s₀ * I1 (γ * g) + ehat E s₀ k₀ s₀ (γ * g) = -d1 s₀ * I1 g + ehat E s₀ k₀ s₀ g
      rw [hI1i γ hγ g, hFi γ hγ g]) hl
  intro g
  have h3 := hTlin (-d1 s₀) I1 (ehat E s₀ k₀ s₀) hI1c hFc g
  rw [hz g, hTI g, hPk.2.2.2.2 s₀ hs g, sub_self] at h3
  have h4 : cz 0 * (ehat E s₀ k₀ s₀ g - d1 s₀ * I1 g) = 0 := by linear_combination -h3
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h hcz0
  · exact sub_eq_zero.mp h

end Core

end PositivityTheory.Rg.Sw.AbsSt.Vac
