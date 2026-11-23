import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.CongUnit

variable {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
  [Module L V]

theorem norm_one_add_of_lt {t : L} (ht : ‖t‖ < 1) : ‖1 + t‖ = 1 := by
  have hne : ‖(1 : L)‖ ≠ ‖t‖ := by rw [norm_one]; exact ht.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]
  exact max_eq_left ht.le

theorem exists_coord {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (hx : x ≠ 0) :
    ∃ i, (∀ j, ‖b.repr x j‖ ≤ ‖b.repr x i‖) ∧ b.repr x i ≠ 0 ∧
      ‖b.repr ((1 + g) x) i‖ = ‖b.repr x i‖ := by
  have hne : ∃ j, b.repr x j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have : b.repr x = 0 := by
      ext j
      simpa using hcon j
    simpa using this
  obtain ⟨j₀, hj₀⟩ := hne
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖b.repr x j‖)
    ⟨j₀, Finset.mem_univ _⟩
  have hmax : ∀ j, ‖b.repr x j‖ ≤ ‖b.repr x i‖ := fun j => hi j (Finset.mem_univ _)
  have hc : b.repr x i ≠ 0 := by
    intro h0
    have := hmax j₀
    rw [h0, norm_zero] at this
    exact hj₀ (norm_le_zero_iff.mp this)
  refine ⟨i, hmax, hc, ?_⟩
  set c := b.repr x i with hcdef
  have hy : c⁻¹ • x ∈ Λ := by
    rw [hb]
    intro j
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hmax j) (norm_nonneg _)
  obtain ⟨z, hz, hgz⟩ := hg _ hy
  have hzi : ‖b.repr z i‖ ≤ 1 := (hb z).1 hz i
  have hval : g x = c • π • z := by
    have h1 : g (c⁻¹ • x) = c⁻¹ • g x := map_smul g _ _
    rw [h1] at hgz
    rw [← hgz, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hGx : b.repr ((1 + g) x) i = c * (1 + π * b.repr z i) := by
    have : (1 + g) x = x + c • π • z := by
      rw [LinearMap.add_apply, Module.End.one_apply, hval]
    rw [this, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, ← hcdef]
    ring
  have ht : ‖π * b.repr z i‖ < 1 := by
    rw [norm_mul]
    calc ‖π‖ * ‖b.repr z i‖ ≤ ‖π‖ * 1 := by gcongr
      _ < 1 := by simpa using hπ
  rw [hGx, norm_mul, norm_one_add_of_lt ht, mul_one]

theorem eq_zero_of_apply {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (h0 : (1 + g) x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨i, -, hc, hn⟩ := exists_coord b hb hπ hg hx
  rw [h0, map_zero, Finsupp.zero_apply, norm_zero] at hn
  exact hc (norm_eq_zero.mp hn.symm)

theorem mem_of_apply_mem {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (hG : (1 + g) x ∈ Λ) : x ∈ Λ := by
  by_cases hx : x = 0
  · rw [hx]; exact Λ.zero_mem
  obtain ⟨i, hmax, -, hn⟩ := exists_coord b hb hπ hg hx
  rw [hb]
  intro j
  exact (hmax j).trans (hn ▸ (hb _).1 hG i)

theorem main : ∀ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V] (Λ : AddSubgroup V), IsLat L Λ → ∀ π : L, ‖π‖ < 1 →
    ∀ g ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π, ∃ g' ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π,
      (1 + g) * (1 + g') = 1 ∧ (1 + g') * (1 + g) = 1 := by
  intro L V _ _ _ _ _ Λ hΛ π hπ g hg
  obtain ⟨m, b, hb⟩ := hΛ
  have hker : LinearMap.ker (1 + g) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact eq_zero_of_apply b hb hπ hg hx
  obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_ker_eq_bot (1 + g)).2 hker
  have hGH : (1 + g) * (↑u⁻¹ : Module.End L V) = 1 := by rw [← hu]; exact u.mul_inv
  have hHG : (↑u⁻¹ : Module.End L V) * (1 + g) = 1 := by rw [← hu]; exact u.inv_mul
  set H : Module.End L V := ↑u⁻¹ with hH
  have hGHx : ∀ x, (1 + g) (H x) = x := fun x => by
    have := congrArg (fun f : Module.End L V => f x) hGH
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hHGx : ∀ x, H ((1 + g) x) = x := fun x => by
    have := congrArg (fun f : Module.End L V => f x) hHG
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hHmem : ∀ x ∈ Λ, H x ∈ Λ := fun x hx =>
    mem_of_apply_mem b hb hπ hg (by rw [hGHx]; exact hx)
  refine ⟨H - 1, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hgy⟩ := hg x hx
    refine ⟨-H y, Λ.neg_mem (hHmem y hy), ?_⟩
    have h1 : H x + H (g x) = x := by
      have := hHGx x
      rwa [LinearMap.add_apply, Module.End.one_apply, map_add] at this
    have h2 : (H - 1) x = H x - x := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
    rw [h2, smul_neg, ← map_smul, ← hgy]
    rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, h1, sub_self]
  · rw [add_sub_cancel]; exact hGH
  · rw [add_sub_cancel]; exact hHG

end GlobalTheory.CompanionTheory.Iwahori.CongUnit
