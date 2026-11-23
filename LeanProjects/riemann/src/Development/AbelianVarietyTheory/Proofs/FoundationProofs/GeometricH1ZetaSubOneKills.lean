import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmallTracesSubgroupGaloisTowerTopStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteGaloisApproximationStatement

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.TateGeo

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem cong_refl' (k : ℕ) (x : Ω) : Cong p k x x :=
  ⟨0, isIntegral_zero, by simp⟩

theorem cong_symm' {k : ℕ} {x y : Ω} (h : Cong p k x y) : Cong p k y x := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨-z, hz.neg, by rw [mul_neg, ← e]; ring⟩

theorem cong_trans' {k : ℕ} {x y w : Ω} (h1 : Cong p k x y) (h2 : Cong p k y w) : Cong p k x w := by
  obtain ⟨z, hz, e⟩ := h1
  obtain ⟨z', hz', e'⟩ := h2
  exact ⟨z + z', hz.add hz', by rw [mul_add, ← e, ← e']; ring⟩

theorem cong_add' {k : ℕ} {x y x' y' : Ω} (h1 : Cong p k x y) (h2 : Cong p k x' y') :
    Cong p k (x + x') (y + y') := by
  obtain ⟨z, hz, e⟩ := h1
  obtain ⟨z', hz', e'⟩ := h2
  exact ⟨z + z', hz.add hz', by rw [mul_add, ← e, ← e']; ring⟩

theorem cong_mul_left' {k : ℕ} {x y : Ω} (a : Ω) (ha : IsInt p a) (h : Cong p k x y) :
    Cong p k (a * x) (a * y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨a * z, ha.mul hz, by rw [← mul_sub, e]; ring⟩

theorem cong_sum' {k : ℕ} {ι : Type*} (s : Finset ι) (f f' : ι → Ω)
    (h : ∀ i ∈ s, Cong p k (f i) (f' i)) : Cong p k (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cong_refl' (p := p) k (0 : Ω)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact cong_add' (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cong_of_eq' {k : ℕ} {x y : Ω} (h : x = y) : Cong p k x y := h ▸ cong_refl' k x

theorem mem_geoTop_iff (T : Tower p Ω) (g : Gal p Ω) :
    g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n ↔
      (∀ x : Ω, IsAlgZp p x → g x = x) ∧ ∀ n, g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := by
  rw [Subgroup.mem_inf, Subgroup.mem_iInf]
  refine and_congr Iff.rfl (forall_congr' fun n => ?_)
  rw [Gn, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  rfl

theorem exists_moved (T : Tower p Ω) {g : Gal p Ω} (hg : g ∉ Ggeo p Ω ⊓ ⨅ n, Gn T n) :
    ∃ a : Ω, g a ≠ a ∧ ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, h a = a := by
  rw [mem_geoTop_iff] at hg
  by_contra hno
  push_neg at hno
  apply hg
  refine ⟨fun x hx => ?_, fun n => ⟨?_, ?_⟩⟩
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno x hne
    exact hx' (((mem_geoTop_iff T h).mp hh).1 x hx)
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno _ hne
    exact hx' (((mem_geoTop_iff T h).mp hh).2 n).1
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno _ hne
    exact hx' (((mem_geoTop_iff T h).mp hh).2 n).2

theorem uniform_lc_on (hΩ : IsClo p Ω) (T : Tower p Ω) {k : ℕ} {c : Gal p Ω → Ω}
    (hc : IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c) :
    ∃ S₀ : Finset Ω, ∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n,
      (∀ x ∈ S₀, h x = g x) → Cong p k (c h) (c g) := by
  classical
  set H := Ggeo p Ω ⊓ ⨅ n, Gn T n with hH
  have hS : ∀ g : Gal p Ω, ∃ S : Finset Ω,
      (g ∈ H → ∀ h ∈ H, (∀ x ∈ S, h x = g x) → Cong p k (c h) (c g)) ∧
      (g ∉ H → ∀ h ∈ H, ¬ ∀ x ∈ S, h x = g x) := by
    intro g
    by_cases hg : g ∈ H
    · obtain ⟨S, hS⟩ := hc.2 g hg
      exact ⟨S, fun _ => hS, fun h => (h hg).elim⟩
    · obtain ⟨a, hga, ha⟩ := exists_moved T hg
      refine ⟨{a}, fun h => (hg h).elim, fun _ h hh hagree => ?_⟩
      have := hagree a (Finset.mem_singleton_self a)
      rw [ha h hh] at this
      exact hga this.symm
  choose S hS1 hS2 using hS
  obtain ⟨F, hF⟩ := GlobalTheory.T.finite_galois_approximation p Ω hΩ S
  refine ⟨F.biUnion S, fun g hg h hh hgh => ?_⟩
  obtain ⟨g0, hg0F, hg0⟩ := hF g
  have hg0H : g0 ∈ H := by
    by_contra hn
    exact hS2 g0 hn g hg hg0
  have h1 : Cong p k (c g) (c g0) := hS1 g0 hg0H g hg hg0
  have h2 : Cong p k (c h) (c g0) := hS1 g0 hg0H h hh (fun x hx => by
    rw [hgh x (Finset.mem_biUnion.mpr ⟨g0, hg0F, hx⟩), hg0 x hx])
  exact cong_trans' h2 (cong_symm' h1)

theorem uniform_lc_on_int (hΩ : IsClo p Ω) (T : Tower p Ω) {k : ℕ} {c : Gal p Ω → Ω}
    (hc : IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c) :
    ∃ S₁ : Finset Ω, (∀ s ∈ S₁, IsInt p s) ∧ ∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n,
      ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, (∀ x ∈ S₁, h x = g x) → Cong p k (c h) (c g) := by
  classical
  obtain ⟨S₀, hS₀⟩ := uniform_lc_on hΩ T hc
  have hm : ∀ x : Ω, ∃ a : O0 p, a ≠ 0 ∧ IsInt p (a • x) := fun x => by
    obtain ⟨a, ha, hi⟩ := (hΩ.alg.isAlgebraic x).exists_integral_multiple
    exact ⟨a, ha, hi⟩
  choose a ha hai using hm
  refine ⟨S₀.image (fun x => a x • x), ?_, fun g hg h hh hgh => hS₀ g hg h hh fun x hx => ?_⟩
  · intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
    exact hai x
  · have e := hgh (a x • x) (Finset.mem_image_of_mem _ hx)
    rw [Algebra.smul_def, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes] at e
    have hne : algebraMap (O0 p) Ω (a x) ≠ 0 := by
      intro h0
      exact ha x (hΩ.inj (by rw [h0, map_zero]))
    exact mul_left_cancel₀ hne e

theorem h1_killed_by_zeta_sub_one_geo : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ c : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (c (g * h)) (c g + g (c h))) →
  Cob1 k (Ggeo p Ω ⊓ ⨅ n, Gn T n) (fun g => (T.ζ j - 1) * c g) := by
  intro p _ hp2 Ω _ _ hΩ T k j hj c hc hcoc
  classical
  set H := Ggeo p Ω ⊓ ⨅ n, Gn T n with hHdef
  obtain ⟨S₁, hS₁int, hS₁⟩ := uniform_lc_on_int hΩ T hc
  obtain ⟨y, E, hy, hEH, hu, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hΩ T H inf_le_right S₁ j hj
  set x : Ω := ∑ g ∈ E, g y * c g with hx
  have hxint : IsInt p x := by
    refine IsIntegral.sum _ fun g hg => ?_
    exact (IsIntegral.map g.toAlgHom hy).mul (hc.1 g (hEH g hg))
  refine ⟨-x, hxint.neg, fun h hh => ?_⟩
  have hσex : ∀ g ∈ E, ∃ g' ∈ E, (h * g) y = g' y ∧ ∀ s ∈ S₁, (h * g) s = g' s := fun g hg => by
    obtain ⟨g', ⟨hg'E, h1, h2⟩, -⟩ := hu (h * g) (H.mul_mem hh (hEH g hg))
    exact ⟨g', hg'E, h1, h2⟩
  choose! σ hσE hσy hσS using hσex
  have hσinj : Set.InjOn σ E := by
    intro g1 hg1 g2 hg2 he
    have ey : g1 y = g2 y := by
      have := (hσy g1 hg1).trans ((congrArg (fun f : Gal p Ω => f y) he).trans (hσy g2 hg2).symm)
      simpa using this
    have es : ∀ s ∈ S₁, g1 s = g2 s := fun s hs => by
      have := (hσS g1 hg1 s hs).trans ((congrArg (fun f : Gal p Ω => f s) he).trans (hσS g2 hg2 s hs).symm)
      simpa using this
    exact (hu g1 (hEH g1 hg1)).unique ⟨hg1, rfl, fun _ _ => rfl⟩ ⟨hg2, ey, es⟩
  have himg : E.image σ = E :=
    Finset.eq_of_subset_of_card_le (fun g' hg' => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hg'
      exact hσE g hg) (by rw [Finset.card_image_of_injOn hσinj])
  have hperm : ∑ g ∈ E, σ g y * c (σ g) = x := by
    rw [hx, ← Finset.sum_image (f := fun g' => g' y * c g') hσinj, himg]
  have hhx : h x = ∑ g ∈ E, h (g y) * h (c g) := by
    rw [hx, map_sum]; simp only [map_mul]
  have hζ : h (T.ζ j) = T.ζ j := (((mem_geoTop_iff T h).mp hh).2 j).1
  have hsumh : ∑ g ∈ E, h (g y) = T.ζ j - 1 := by
    rw [← map_sum, hsum, map_sub, map_one, hζ]
  have step : ∀ g ∈ E, Cong p k (h (g y) * h (c g)) (σ g y * c (σ g) - h (g y) * c h) := by
    intro g hg
    have hgH := hEH g hg
    have c1 : Cong p k (h (c g)) (c (h * g) - c h) := by
      obtain ⟨z, hz, e⟩ := hcoc h hh g hgH
      exact ⟨-z, hz.neg, by rw [mul_neg, ← e]; ring⟩
    have c2 : Cong p k (c (h * g)) (c (σ g)) :=
      hS₁ (σ g) (hEH _ (hσE g hg)) (h * g) (H.mul_mem hh hgH) (hσS g hg)
    have c3 : Cong p k (c (h * g) - c h) (c (σ g) - c h) := by
      obtain ⟨z, hz, e⟩ := c2
      exact ⟨z, hz, by rw [← e]; ring⟩
    have := cong_mul_left' (h (g y)) (IsIntegral.map h.toAlgHom (IsIntegral.map g.toAlgHom hy))
      (cong_trans' c1 c3)
    refine cong_trans' this (cong_of_eq' ?_)
    have ey : h (g y) = σ g y := by rw [← hσy g hg]; rfl
    rw [ey]; ring
  have total := cong_sum' E _ _ step
  rw [← hhx, Finset.sum_sub_distrib, hperm, ← Finset.sum_mul, hsumh] at total
  obtain ⟨z, hz, e⟩ := total
  refine ⟨z, hz, ?_⟩
  show (T.ζ j - 1) * c h - (h (-x) - -x) = _
  rw [map_neg, ← e]; ring

end GlobalTheory.K5.TateGeo
