import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormOrthogonalDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrbitOrthogonalComplementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianInvariantFormOrthogonalSplitStatement
open scoped Topology

namespace GlobalTheory.UnitaryRep

theorem radical_orthogonal : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V → V → ℂ) (D : Submodule ℂ V),
    (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x + y) z = B x z + B y z) →
    (∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B (c • x) y = c * B x y) →
    (∀ x ∈ D, ∀ y ∈ D, B y x = starRingEnd ℂ (B x y)) →
    (∀ x ∈ D, 0 ≤ (B x x).re) →
    ∀ x ∈ D, B x x = 0 → ∀ y ∈ D, B y x = 0 := by
  intro V _ _ B D hadd hsmul hherm hpos x hx hxx y hy
  have hadd2 : ∀ u ∈ D, ∀ v ∈ D, ∀ w ∈ D, B u (v + w) = B u v + B u w := by
    intro u hu v hv w hw
    rw [hherm (v + w) (D.add_mem hv hw) u hu, hadd v hv w hw u hu, map_add, ← hherm v hv u hu,
      ← hherm w hw u hu]
  have hsmul2 : ∀ c : ℂ, ∀ u ∈ D, ∀ v ∈ D, B u (c • v) = starRingEnd ℂ c * B u v := by
    intro c u hu v hv
    rw [hherm (c • v) (D.smul_mem c hv) u hu, hsmul c v hv u hu, map_mul, ← hherm v hv u hu]
  have key : ∀ a : ℂ, B (y + a • x) (y + a • x) =
      B y y + a * B x y + starRingEnd ℂ a * B y x + a * starRingEnd ℂ a * B x x := by
    intro a
    have hax : a • x ∈ D := D.smul_mem a hx
    rw [hadd y hy (a • x) hax _ (D.add_mem hy hax), hsmul a x hx _ (D.add_mem hy hax),
      hadd2 y hy y hy (a • x) hax, hadd2 x hx y hy (a • x) hax, hsmul2 a y hy x hx,
      hsmul2 a x hx x hx]
    ring
  set c := B y x with hc
  have hxy : B x y = starRingEnd ℂ c := hherm y hy x hx
  by_contra hc0
  have hn : 0 < Complex.normSq c := Complex.normSq_pos.2 hc0
  set t : ℝ := ((B y y).re + 1) / (2 * Complex.normSq c) with ht
  have h := hpos _ (D.add_mem hy (D.smul_mem (-(t : ℂ) * c) hx))
  rw [key, hxy, hxx] at h
  have hre : (B y y + -(t : ℂ) * c * starRingEnd ℂ c + starRingEnd ℂ (-(t : ℂ) * c) * c +
      -(t : ℂ) * c * starRingEnd ℂ (-(t : ℂ) * c) * 0).re = (B y y).re - 2 * t * Complex.normSq c := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [hre] at h
  have h2 : 2 * t * Complex.normSq c = (B y y).re + 1 := by
    rw [ht]; field_simp
  linarith

theorem fixed_projection_nonradical : ∀ {V G : Type} [AddCommGroup V] [Module ℂ V] [Group G] (ρ : G →* Module.End ℂ V)
    (B : V → V → ℂ) (D : Submodule ℂ V),
    (∀ g, ∀ x ∈ D, ρ g x ∈ D) →
    (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x + y) z = B x z + B y z) →
    (∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B (c • x) y = c * B x y) →
    (∀ x ∈ D, ∀ y ∈ D, B y x = starRingEnd ℂ (B x y)) →
    (∀ g, ∀ x ∈ D, ∀ y ∈ D, B (ρ g x) (ρ g y) = B x y) →
    (∀ x ∈ D, B x x = 0 → ∀ y ∈ D, B y x = 0) →
    ∀ x₀ ∈ D, ∀ Z : Submodule ℂ V, Z ≤ Submodule.span ℂ (Set.range fun g => ρ g x₀) →
    (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) → ∀ a ∈ Z, (∀ y ∈ Z, B y (x₀ - a) = 0) →
    (∃ z ∈ Z, B z z ≠ 0) → B a a ≠ 0 := by
  intro V G _ _ _ ρ B D hD hadd hsmul hherm hinv hrad0 x₀ hx₀ Z hZU hZ a haZ ha hnz h0
  have hadd2 : ∀ u ∈ D, ∀ v ∈ D, ∀ w ∈ D, B u (v + w) = B u v + B u w := by
    intro u hu v hv w hw
    rw [hherm (v + w) (D.add_mem hv hw) u hu, hadd v hv w hw u hu, map_add, ← hherm v hv u hu,
      ← hherm w hw u hu]
  have hsmul2 : ∀ c : ℂ, ∀ u ∈ D, ∀ v ∈ D, B u (c • v) = starRingEnd ℂ c * B u v := by
    intro c u hu v hv
    rw [hherm (c • v) (D.smul_mem c hv) u hu, hsmul c v hv u hu, map_mul, ← hherm v hv u hu]
  have hUD : Submodule.span ℂ (Set.range fun g => ρ g x₀) ≤ D :=
    Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hD g x₀ hx₀)
  have hZD : ∀ y ∈ Z, y ∈ D := fun y hy => hUD (hZU hy)
  have haD := hZD a haZ
  have h1 : ∀ y ∈ Z, B y x₀ = 0 := by
    intro y hy
    have e : x₀ = (x₀ - a) + a := by abel
    rw [e, hadd2 y (hZD y hy) _ (D.sub_mem hx₀ haD) a haD, ha y hy, hrad0 a haD h0 y (hZD y hy),
      add_zero]
  have hinvapp : ∀ (g : G) (x : V), ρ g (ρ g⁻¹ x) = x := by
    intro g x
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h2 : ∀ g, ∀ y ∈ Z, B y (ρ g x₀) = 0 := by
    intro g y hy
    rw [← hinvapp g y, hinv g _ (hD _ _ (hZD y hy)) x₀ hx₀]
    exact h1 _ (hZ _ _ hy)
  have h3 : ∀ w ∈ Submodule.span ℂ (Set.range fun g => ρ g x₀), ∀ y ∈ Z, B y w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, rfl⟩ := hw
      exact h2 g
    | zero =>
      intro y hy
      have := hadd2 y (hZD y hy) 0 D.zero_mem 0 D.zero_mem
      simpa using this
    | add u v hu hv ihu ihv =>
      intro y hy
      rw [hadd2 y (hZD y hy) u (hUD hu) v (hUD hv), ihu y hy, ihv y hy, add_zero]
    | smul c u hu ih =>
      intro y hy
      rw [hsmul2 c y (hZD y hy) u (hUD hu), ih y hy, mul_zero]
  obtain ⟨z, hz, hzz⟩ := hnz
  exact hzz (h3 z (hZU hz) z hz)

theorem isSimpleOver_sup_of_minimal : ∀ {V G : Type} [AddCommGroup V] [Module ℂ V] [Group G] (ρ : G →* Module.End ℂ V)
    (B : V → V → ℂ) (D N Z : Submodule ℂ V),
    N ≤ D → (∀ g, ∀ x ∈ N, ρ g x ∈ N) → (∀ x ∈ D, B x x = 0 → x ∈ N) →
    Z ≤ D → (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) → (∀ z ∈ Z, z ∈ N → B z z = 0) → (∃ z ∈ Z, B z z ≠ 0) →
    (∀ Z₁ : Submodule ℂ V, Z₁ ≤ Z → (∀ g, ∀ x ∈ Z₁, ρ g x ∈ Z₁) →
        (∀ z ∈ Z₁, B z z = 0) ∨ ∀ z ∈ Z, ∃ z₁ ∈ Z₁, B (z - z₁) (z - z₁) = 0) →
    GlobalTheory.ThKLocSS.IsSimpleOver (Set.range ρ) N (N ⊔ Z) := by
  intro V G _ _ _ ρ B D N Z hND hNst hrad hZD hZst hZN hnz hsimp
  have hstab : ∀ g, ∀ x ∈ N ⊔ Z, ρ g x ∈ N ⊔ Z := by
    intro g x hx
    obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hNst g n hn) (hZst g z hz)
  refine ⟨lt_of_le_of_ne le_sup_left fun hEq => ?_, ?_, ?_⟩
  · obtain ⟨z, hz, hzz⟩ := hnz
    have : z ∈ N := hEq ▸ (Submodule.mem_sup_right hz : z ∈ N ⊔ Z)
    exact hzz (hZN z hz this)
  · rintro _ ⟨g, rfl⟩ x hx
    exact hstab g x hx
  · intro S' hNS' hS'S hS'st
    have hS'g : ∀ g, ∀ x ∈ S', ρ g x ∈ S' := fun g x hx => hS'st _ ⟨g, rfl⟩ x hx
    have hZ₁ : ∀ g, ∀ x ∈ S' ⊓ Z, ρ g x ∈ S' ⊓ Z := fun g x hx => ⟨hS'g g x hx.1, hZst g x hx.2⟩
    rcases hsimp (S' ⊓ Z) inf_le_right hZ₁ with h | h
    · left
      refine le_antisymm (fun x hx => ?_) hNS'
      obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.1 (hS'S hx)
      have hzS : z ∈ S' := by
        have := S'.sub_mem hx (hNS' hn)
        simpa using this
      exact N.add_mem hn (hrad z (hZD hz) (h z ⟨hzS, hz⟩))
    · right
      refine le_antisymm hS'S (sup_le hNS' fun z hz => ?_)
      obtain ⟨z₁, hz₁, hzz⟩ := h z hz
      have hd : z - z₁ ∈ N := hrad _ (D.sub_mem (hZD hz) (hZD hz₁.2)) hzz
      have : z = (z - z₁) + z₁ := by abel
      rw [this]
      exact S'.add_mem (hNS' hd) hz₁.1

theorem exists_isSimpleOver_of_unitary : ∀ {V G : Type} [AddCommGroup V] [Module ℂ V] [Group G] (ρ : G →* Module.End ℂ V)
    (𝒦 : Set (Subgroup G)) (B : V → V → ℂ) (D N : Submodule ℂ V)
    (hD : ∀ g, ∀ x ∈ D, ρ g x ∈ D) (hND : N ≤ D) (hne : N ≠ D) (hN : ∀ g, ∀ x ∈ N, ρ g x ∈ N)
    (hadd : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x + y) z = B x z + B y z)
    (hsmul : ∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B (c • x) y = c * B x y)
    (hherm : ∀ x ∈ D, ∀ y ∈ D, B y x = starRingEnd ℂ (B x y))
    (hpos : ∀ x ∈ D, 0 ≤ (B x x).re)
    (hinv : ∀ g, ∀ x ∈ D, ∀ y ∈ D, B (ρ g x) (ρ g y) = B x y)
    (hrad : ∀ x ∈ D, B x x = 0 → x ∈ N)
    (hsm : ∀ x ∈ D, ∃ K ∈ 𝒦, ∀ k ∈ K, ρ k x = x)
    (hfin : ∀ K ∈ 𝒦, ∀ x ∈ D, {y | ∃ k ∈ K, ρ k x = y}.Finite)
    (hadm : ∀ K ∈ 𝒦, ∀ x ∈ D, ∃ s : Finset V, (↑s ⊆ (D : Set V)) ∧
      ∀ y ∈ Submodule.span ℂ (Set.range fun g => ρ g x), (∀ k ∈ K, ρ k y = y) →
        ∃ z ∈ Submodule.span ℂ (s : Set V), B (y - z) (y - z) = 0),
    ∃ S : Submodule ℂ V, S ≤ D ∧ GlobalTheory.ThKLocSS.IsSimpleOver (Set.range ρ) N S := by
  intro V G _ _ _ ρ 𝒦 B D N hD hND hne hN hadd hsmul hherm hpos hinv hrad hsm hfin hadm
  have hrad0 := radical_orthogonal B D hadd hsmul hherm hpos
  have hadd2 : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B x (y + z) = B x y + B x z := by
    intro x hx y hy z hz
    rw [hherm (y + z) (D.add_mem hy hz) x hx, hadd y hy z hz x hx, map_add, ← hherm y hy x hx,
      ← hherm z hz x hx]
  have hsmul2 : ∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B x (c • y) = starRingEnd ℂ c * B x y := by
    intro c x hx y hy
    rw [hherm (c • y) (D.smul_mem c hy) x hx, hsmul c y hy x hx, map_mul, ← hherm y hy x hx]
  have hzero2 : ∀ x ∈ D, B x 0 = 0 := by
    intro x hx
    have := hadd2 x hx 0 D.zero_mem 0 D.zero_mem
    simpa using this
  have hinvapp : ∀ (g : G) (x : V), ρ g (ρ g⁻¹ x) = x := by
    intro g x
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨x₀, hx₀D, hx₀N⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hND hne)
  obtain ⟨K₀, hK₀, hK₀x⟩ := hsm x₀ hx₀D
  set U : Submodule ℂ V := Submodule.span ℂ (Set.range fun g => ρ g x₀) with hUdef
  have hUD : U ≤ D := Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hD g x₀ hx₀D)
  have hUst : ∀ g, ∀ x ∈ U, ρ g x ∈ U := by
    intro g x hx
    have : U ≤ U.comap (ρ g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩)
    exact this hx
  have hx0U : x₀ ∈ U := Submodule.subset_span ⟨1, by simp⟩
  have hproj : ∀ K ∈ 𝒦, ∀ Z : Submodule ℂ V, Z ≤ U → (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) →
      ∀ u ∈ D, (∀ k ∈ K, ρ k u = u) →
        ∃ a ∈ Z, (∀ k ∈ K, ρ k a = a) ∧ ∀ y ∈ Z, B y (u - a) = 0 := by
    intro K hK Z hZU hZ u hu hKu
    let Wf : Submodule ℂ V :=
      { carrier := {z | z ∈ Z ∧ ∀ k ∈ K, ρ k z = z}
        add_mem' := fun {a b} ha hb => ⟨Z.add_mem ha.1 hb.1, fun k hk => by
          rw [map_add, ha.2 k hk, hb.2 k hk]⟩
        zero_mem' := ⟨Z.zero_mem, fun k _ => map_zero _⟩
        smul_mem' := fun c z hz => ⟨Z.smul_mem c hz.1, fun k hk => by
          rw [map_smul, hz.2 k hk]⟩ }
    obtain ⟨s, hsD, hs⟩ := hadm K hK x₀ hx₀D
    have hWD : Wf ≤ D := fun z hz => hUD (hZU hz.1)
    obtain ⟨a, haW, ha⟩ := GlobalTheory.T.hermitian_form_orthogonal_decomposition B D hadd hsmul hherm hrad0 Wf hWD s hsD
      (fun w hw => hs w (hZU hw.1) hw.2) u hu
    refine ⟨a, haW.1, haW.2, fun y hy => ?_⟩
    obtain ⟨e, he, hefix, heB⟩ := GlobalTheory.T.finite_orbit_orthogonal_complement ρ B D hD hadd hsmul hinv K y (hUD (hZU hy))
      (hfin K hK y (hUD (hZU hy)))
    have heZ : e ∈ Z := (Submodule.span_le (p := Z)).2
      (by rintro _ ⟨k, _, rfl⟩; exact hZ k y hy) he
    have hua : u - a ∈ D := D.sub_mem hu (hUD (hZU haW.1))
    rw [← heB (u - a) hua (fun k hk => by rw [map_sub, hKu k hk, haW.2 k hk])]
    exact ha e ⟨heZ, hefix⟩
  have hcomp : ∀ Z : Submodule ℂ V, Z ≤ U → (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) →
      ∀ u ∈ U, ∃ z ∈ Z, ∀ y ∈ Z, B y (u - z) = 0 := by
    intro Z hZU hZ u hu
    obtain ⟨K, hK, hKu⟩ := hsm u (hUD hu)
    obtain ⟨a, haZ, -, ha⟩ := hproj K hK Z hZU hZ u (hUD hu) hKu
    exact ⟨a, haZ, ha⟩
  have hfix : ∀ Z : Submodule ℂ V, Z ≤ U → (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) → (∃ z ∈ Z, B z z ≠ 0) →
      ∃ a ∈ Z, (∀ k ∈ K₀, ρ k a = a) ∧ B a a ≠ 0 := by
    intro Z hZU hZ hnz
    obtain ⟨a, haZ, hafix, ha⟩ := hproj K₀ hK₀ Z hZU hZ x₀ hx₀D hK₀x
    exact ⟨a, haZ, hafix, fixed_projection_nonradical ρ B D hD hadd hsmul hherm hinv hrad0 x₀ hx₀D Z hZU hZ a haZ ha hnz⟩
  let P : Submodule ℂ V :=
    { carrier := {u | u ∈ U ∧ ∀ n ∈ N, n ∈ U → B n u = 0}
      add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, fun n hn hnU => by
        rw [hadd2 n (hUD hnU) a (hUD ha.1) b (hUD hb.1), ha.2 n hn hnU, hb.2 n hn hnU, add_zero]⟩
      zero_mem' := ⟨U.zero_mem, fun n _ hnU => hzero2 n (hUD hnU)⟩
      smul_mem' := fun c z hz => ⟨U.smul_mem c hz.1, fun n hn hnU => by
        rw [hsmul2 c n (hUD hnU) z (hUD hz.1), hz.2 n hn hnU, mul_zero]⟩ }
  have hPU : P ≤ U := fun z hz => hz.1
  have hPst : ∀ g, ∀ x ∈ P, ρ g x ∈ P := by
    intro g x hx
    refine ⟨hUst g x hx.1, fun n hn hnU => ?_⟩
    rw [← hinvapp g n, hinv g _ (hD _ _ (hUD hnU)) x (hUD hx.1)]
    exact hx.2 _ (hN g⁻¹ n hn) (hUst _ _ hnU)
  have hNUst : ∀ g, ∀ x ∈ N ⊓ U, ρ g x ∈ N ⊓ U := fun g x hx => ⟨hN g x hx.1, hUst g x hx.2⟩
  have hP : ∃ z ∈ P, B z z ≠ 0 := by
    obtain ⟨n, hn, hnB⟩ := hcomp (N ⊓ U) inf_le_right hNUst x₀ hx0U
    refine ⟨x₀ - n, ⟨U.sub_mem hx0U hn.2, fun n' hn' hn'U => hnB n' ⟨hn', hn'U⟩⟩, fun h0 => hx₀N ?_⟩
    have := hrad _ (D.sub_mem hx₀D (hUD hn.2)) h0
    simpa using N.add_mem this hn.1
  obtain ⟨Z, hZP, hZst, hZnz, hZsimp⟩ := GlobalTheory.T.hermitian_invariant_form_orthogonal_split ρ B D hadd hsmul hherm hinv hrad0 U hUD K₀ P hPU hPst
    hcomp hfix (hadm K₀ hK₀ x₀ hx₀D) hP
  have hZD : Z ≤ D := fun z hz => hUD (hPU (hZP hz))
  refine ⟨N ⊔ Z, sup_le hND hZD, isSimpleOver_sup_of_minimal ρ B D N Z hND hN hrad hZD hZst ?_ hZnz hZsimp⟩
  intro z hz hzN
  exact (hZP hz).2 z hzN (hPU (hZP hz))

end GlobalTheory.UnitaryRep
