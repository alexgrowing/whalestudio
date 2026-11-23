import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
open scoped Topology

noncomputable section

namespace GlobalTheory.StableMinFix

variable {V G : Type} [AddCommGroup V] [Module ℂ V] [Group G]

def fixImg (ρ : G →* Module.End ℂ V) (B : V → V → ℂ) (K₀ : Subgroup G) (s : Finset V) (Z : Submodule ℂ V) :
    Submodule ℂ (s → ℂ) :=
  Submodule.span ℂ ((fun z (i : s) => B z i) '' {z | z ∈ Z ∧ ∀ k ∈ K₀, ρ k z = z})

theorem fixImg_mono (ρ : G →* Module.End ℂ V) (B : V → V → ℂ) (K₀ : Subgroup G) (s : Finset V)
    {Z₁ Z : Submodule ℂ V} (h : Z₁ ≤ Z) : fixImg ρ B K₀ s Z₁ ≤ fixImg ρ B K₀ s Z :=
  Submodule.span_mono (Set.image_mono fun _ hz => ⟨h hz.1, hz.2⟩)

theorem exists_minimal_simple_mod_radical : ∀ {V G : Type} [AddCommGroup V] [Module ℂ V] [Group G] (ρ : G →* Module.End ℂ V)
    (B : V → V → ℂ) (D : Submodule ℂ V),
    (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x + y) z = B x z + B y z) →
    (∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B (c • x) y = c * B x y) →
    (∀ x ∈ D, ∀ y ∈ D, B y x = starRingEnd ℂ (B x y)) →
    (∀ g, ∀ x ∈ D, ∀ y ∈ D, B (ρ g x) (ρ g y) = B x y) →
    (∀ x ∈ D, B x x = 0 → ∀ y ∈ D, B y x = 0) →
    ∀ (U : Submodule ℂ V), U ≤ D → ∀ (K₀ : Subgroup G) (P : Submodule ℂ V), P ≤ U →
    (∀ g, ∀ x ∈ P, ρ g x ∈ P) →
    (∀ Z : Submodule ℂ V, Z ≤ U → (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) →
      ∀ u ∈ U, ∃ z ∈ Z, ∀ y ∈ Z, B y (u - z) = 0) →
    (∀ Z : Submodule ℂ V, Z ≤ U → (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) → (∃ z ∈ Z, B z z ≠ 0) →
      ∃ a ∈ Z, (∀ k ∈ K₀, ρ k a = a) ∧ B a a ≠ 0) →
    (∃ s : Finset V, (↑s ⊆ (D : Set V)) ∧ ∀ y ∈ U, (∀ k ∈ K₀, ρ k y = y) →
      ∃ z ∈ Submodule.span ℂ (s : Set V), B (y - z) (y - z) = 0) →
    (∃ z ∈ P, B z z ≠ 0) →
    ∃ Z : Submodule ℂ V, Z ≤ P ∧ (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) ∧ (∃ z ∈ Z, B z z ≠ 0) ∧
      ∀ Z₁ : Submodule ℂ V, Z₁ ≤ Z → (∀ g, ∀ x ∈ Z₁, ρ g x ∈ Z₁) →
        (∀ z ∈ Z₁, B z z = 0) ∨ ∀ z ∈ Z, ∃ z₁ ∈ Z₁, B (z - z₁) (z - z₁) = 0 := by
  intro V G _ _ _ ρ B D hadd hsmul hconj hinv hrad U hUD K₀ P hPU hPst hcompl hfix hdim hP
  classical
  obtain ⟨s, hsD, hs⟩ := hdim
  have hsD' : ∀ i : s, (i : V) ∈ D := fun i => hsD (Finset.mem_coe.2 i.2)
  have hzl : ∀ y ∈ D, B 0 y = 0 := by
    intro y hy
    have h := hsmul 0 0 D.zero_mem y hy
    rwa [zero_smul, zero_mul] at h
  have hzr : ∀ y ∈ D, B y 0 = 0 := by
    intro y hy
    rw [hconj 0 D.zero_mem y hy, hzl y hy, map_zero]
  have haddr : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B z (x + y) = B z x + B z y := by
    intro x hx y hy z hz
    rw [hconj _ (D.add_mem hx hy) z hz, hadd x hx y hy z hz, map_add, ← hconj x hx z hz, ← hconj y hy z hz]
  have hsub : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x - y) z = B x z - B y z := by
    intro x hx y hy z hz
    have h := hadd x hx ((-1 : ℂ) • y) (D.smul_mem _ hy) z hz
    rw [hsmul _ y hy z hz, neg_one_smul, ← sub_eq_add_neg] at h
    rw [h]; ring
  have hsubr : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B z (x - y) = B z x - B z y := by
    intro x hx y hy z hz
    rw [hconj _ (D.sub_mem hx hy) z hz, hsub x hx y hy z hz, map_sub, ← hconj x hx z hz, ← hconj y hy z hz]
  have hsmulr : ∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B y (c • x) = starRingEnd ℂ c * B y x := by
    intro c x hx y hy
    rw [hconj _ (D.smul_mem c hx) y hy, hsmul c x hx y hy, map_mul, ← hconj x hx y hy]
  have hspanD : Submodule.span ℂ (s : Set V) ≤ D := Submodule.span_le.2 hsD

  have hker : ∀ y ∈ U, (∀ k ∈ K₀, ρ k y = y) → (∀ i ∈ s, B y i = 0) → B y y = 0 := by
    intro y hyU hyfix hyi
    have hyD := hUD hyU
    obtain ⟨z, hz, hyz⟩ := hs y hyU hyfix
    have hzD : z ∈ D := hspanD hz
    have h1 : B y (y - z) = 0 := hrad _ (D.sub_mem hyD hzD) hyz y hyD
    have hvan : ∀ w ∈ Submodule.span ℂ (s : Set V), B y w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact hyi x (Finset.mem_coe.1 hx)
      | zero => exact hzr y hyD
      | add x w hx hw ihx ihw => rw [haddr x (hspanD hx) w (hspanD hw) y hyD, ihx, ihw, add_zero]
      | smul c x hx ih => rw [hsmulr c x (hspanD hx) y hyD, ih, mul_zero]
    have h3 := hsubr y hyD z hzD y hyD
    rw [h1, hvan z hz, sub_zero] at h3
    exact h3.symm

  have hmemW : ∀ Z : Submodule ℂ V, Z ≤ D → ∀ f ∈ fixImg ρ B K₀ s Z,
      ∃ z ∈ Z, (∀ k ∈ K₀, ρ k z = z) ∧ (fun i : s => B z i) = f := by
    intro Z hZD f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      exact ⟨z, hz.1, hz.2, rfl⟩
    | zero => exact ⟨0, Z.zero_mem, fun k _ => map_zero _, funext fun i => hzl _ (hsD' i)⟩
    | add f g _ _ ihf ihg =>
      obtain ⟨x, hx, hxf, rfl⟩ := ihf
      obtain ⟨w, hw, hwf, rfl⟩ := ihg
      exact ⟨x + w, Z.add_mem hx hw, fun k hk => by rw [map_add, hxf k hk, hwf k hk],
        funext fun i => hadd x (hZD hx) w (hZD hw) i (hsD' i)⟩
    | smul c f _ ih =>
      obtain ⟨x, hx, hxf, rfl⟩ := ih
      exact ⟨c • x, Z.smul_mem c hx, fun k hk => by rw [map_smul, hxf k hk],
        funext fun i => hsmul c x (hZD hx) i (hsD' i)⟩

  have hex : ∃ n, ∃ Z : Submodule ℂ V, (Z ≤ P ∧ (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) ∧ ∃ z ∈ Z, B z z ≠ 0) ∧
      Module.finrank ℂ (fixImg ρ B K₀ s Z) = n := ⟨_, P, ⟨le_rfl, hPst, hP⟩, rfl⟩
  obtain ⟨Z, ⟨hZP, hZst, hZnz⟩, hZn⟩ := Nat.find_spec hex
  have hZU : Z ≤ U := hZP.trans hPU
  have hZD : Z ≤ D := hZU.trans hUD
  refine ⟨Z, hZP, hZst, hZnz, ?_⟩
  intro Z₁ hZ₁ hZ₁st
  by_cases h : ∀ z ∈ Z₁, B z z = 0
  · exact Or.inl h
  right
  push_neg at h
  obtain ⟨z0, hz0, hz0nz⟩ := h
  have hZ₁D : Z₁ ≤ D := hZ₁.trans hZD
  let Z₂ : Submodule ℂ V :=
    { carrier := {z | z ∈ Z ∧ ∀ y ∈ Z₁, B y z = 0}
      add_mem' := fun {x w} hx hw => ⟨Z.add_mem hx.1 hw.1, fun y hy => by
        rw [haddr x (hZD hx.1) w (hZD hw.1) y (hZ₁D hy), hx.2 y hy, hw.2 y hy, add_zero]⟩
      zero_mem' := ⟨Z.zero_mem, fun y hy => hzr y (hZ₁D hy)⟩
      smul_mem' := fun c x hx => ⟨Z.smul_mem c hx.1, fun y hy => by
        rw [hsmulr c x (hZD hx.1) y (hZ₁D hy), hx.2 y hy, mul_zero]⟩ }
  have hmem2 : ∀ x, x ∈ Z₂ ↔ x ∈ Z ∧ ∀ y ∈ Z₁, B y x = 0 := fun x => Iff.rfl
  have hZ₂U : Z₂ ≤ U := fun x hx => hZU ((hmem2 x).1 hx).1
  have hZ₂st : ∀ g, ∀ x ∈ Z₂, ρ g x ∈ Z₂ := by
    intro g x hx
    rw [hmem2] at hx ⊢
    refine ⟨hZst g x hx.1, fun y hy => ?_⟩
    have hy' : ρ g⁻¹ y ∈ Z₁ := hZ₁st _ _ hy
    have e : ρ g (ρ g⁻¹ y) = y := by
      show (ρ g * ρ g⁻¹) y = y
      rw [← map_mul, mul_inv_cancel, map_one]; rfl
    have h4 := hinv g (ρ g⁻¹ y) (hZ₁D hy') x (hZD hx.1)
    rw [e] at h4
    rw [h4]
    exact hx.2 _ hy'
  have hZ₂rad : ∀ z ∈ Z₂, B z z = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨a, haZ₂, hafix, haa⟩ := hfix Z₂ hZ₂U hZ₂st hne
    rw [hmem2] at haZ₂
    have haD : a ∈ D := hZD haZ₂.1
    have hmin := Nat.find_min' hex ⟨Z₁, ⟨hZ₁.trans hZP, hZ₁st, z0, hz0, hz0nz⟩, rfl⟩
    rw [← hZn] at hmin
    have hlt : fixImg ρ B K₀ s Z₁ < fixImg ρ B K₀ s Z := by
      refine lt_of_le_of_ne (fixImg_mono ρ B K₀ s hZ₁) ?_
      intro heq
      have hψa : (fun i : s => B a i) ∈ fixImg ρ B K₀ s Z₁ :=
        heq ▸ Submodule.subset_span ⟨a, ⟨haZ₂.1, hafix⟩, rfl⟩
      obtain ⟨b, hbZ₁, hbfix, hbeq⟩ := hmemW Z₁ hZ₁D _ hψa
      have hbD : b ∈ D := hZ₁D hbZ₁
      have hab : B (a - b) (a - b) = 0 := by
        refine hker (a - b) (U.sub_mem (hZU haZ₂.1) (hZU (hZ₁ hbZ₁)))
          (fun k hk => by rw [map_sub, hafix k hk, hbfix k hk]) (fun i hi => ?_)
        have h5 := congrFun hbeq ⟨i, hi⟩
        dsimp only at h5
        rw [hsub a haD b hbD i (hsD (Finset.mem_coe.2 hi)), h5, sub_self]
      apply haa
      have e1 := hrad _ (D.sub_mem haD hbD) hab a haD
      rw [hsubr a haD b hbD a haD] at e1
      have e2 : B a b = 0 := by rw [hconj b hbD a haD, haZ₂.2 b hbZ₁, map_zero]
      rw [e2, sub_zero] at e1
      exact e1
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  intro z hz
  obtain ⟨z₁, hz₁, horth⟩ := hcompl Z₁ (hZ₁.trans hZU) hZ₁st z (hZU hz)
  exact ⟨z₁, hz₁, hZ₂rad _ ((hmem2 _).2 ⟨Z.sub_mem hz (hZ₁ hz₁), horth⟩)⟩

end GlobalTheory.StableMinFix

end
