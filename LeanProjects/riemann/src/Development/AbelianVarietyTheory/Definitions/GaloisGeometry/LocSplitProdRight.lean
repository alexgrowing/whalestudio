import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.LocalToGlobal.Columns.HeckeSp

namespace GlobalTheory.HkB

open Formalism.IndefR.Bridge

def LocSplit {G : Type} [Group G] (J L : Subgroup G) : Prop :=
  ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l

theorem locSplit_prod_left {G H : Type} [Group G] [Group H] (A : Subgroup G) (B : Subgroup H) :
    LocSplit (A.prod B) ((⊤ : Subgroup G).prod ⊥) := by
  intro k hk
  refine ⟨(k.1, 1), Subgroup.mem_prod.2 ⟨(Subgroup.mem_prod.1 hk).1, B.one_mem⟩, (1, k.2),
    Subgroup.mem_prod.2 ⟨A.one_mem, (Subgroup.mem_prod.1 hk).2⟩,
    Subgroup.mem_prod.2 ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩, ?_, ?_⟩
  · ext <;> simp
  · intro l hl
    have hl2 : l.2 = 1 := Subgroup.mem_bot.1 (Subgroup.mem_prod.1 hl).2
    show (1, k.2) * l = l * (1, k.2)
    ext <;> simp [hl2]

theorem LocSplit.map {G H : Type} [Group G] [Group H] {J L : Subgroup G} (h : LocSplit J L) (e : G ≃* H) :
    LocSplit (J.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  intro k hk
  obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.1 hk
  obtain ⟨k₁, hk₁, k₂, hk₂, hk₁L, hsplit, hc⟩ := h k' hk'
  refine ⟨e.toMonoidHom k₁, Subgroup.mem_map_of_mem _ hk₁, e.toMonoidHom k₂, Subgroup.mem_map_of_mem _ hk₂,
    Subgroup.mem_map_of_mem _ hk₁L, by rw [hsplit, map_mul], ?_⟩
  intro l hl
  obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.1 hl
  exact (hc l' hl').map e.toMonoidHom

theorem LocSplit.conj_mem {G : Type} [Group G] {J L : Subgroup G} (h : LocSplit J L) {k l : G} (hk : k ∈ J) (hl : l ∈ L) :
    k * l * k⁻¹ ∈ L := by
  obtain ⟨k₁, _, k₂, _, hk₁L, rfl, hc⟩ := h k hk
  have hcl : k₂ * l * k₂⁻¹ = l := by rw [(hc l hl).eq, mul_inv_cancel_right]
  rw [show k₁ * k₂ * l * (k₁ * k₂)⁻¹ = k₁ * (k₂ * l * k₂⁻¹) * k₁⁻¹ by group, hcl]
  exact L.mul_mem (L.mul_mem hk₁L hl) (L.inv_mem hk₁L)

section Operators

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem sum_mul_reps (ρ : Γ →* Module.End ℂ W) {J L : Subgroup G} {χ : J →* ℂˣ}
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) {x : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J x B)
    (hAL : ∀ a ∈ A, a ∈ L) (hBL : ∀ b ∈ B, b ∈ L) {F : G → W} (hF : F ∈ AdForms ι ρ J χ)
    {k : G} (hkJ : k ∈ J) (hkL : k ∈ L) (h : G) :
    ∑ a ∈ A, F (h * k * a) = ∑ b ∈ B, F (h * b) := by
  have hF' : ∀ (γ : Γ) (g : G) (j : J), F (ι γ * g * j) = (χ j : ℂ) • ρ γ (F g) := hF
  have hterm : ∀ a ∈ A, ∀ b ∈ B, b⁻¹ * (k * a) ∈ J → F (h * k * a) = F (h * b) := by
    intro a ha b hb hJ
    have e : h * k * a = ι 1 * (h * b) * ((⟨b⁻¹ * (k * a), hJ⟩ : J) : G) := by simp [mul_assoc]
    rw [e, hF', hχ ⟨b⁻¹ * (k * a), hJ⟩ (L.mul_mem (L.inv_mem (hBL b hb)) (L.mul_mem hkL (hAL a ha)))]
    simp
  have exB : ∀ a ∈ A, ∃ b, b ∈ B ∧ b⁻¹ * (k * a) ∈ J := by
    intro a ha
    obtain ⟨k₁, k₂, hk⟩ := hA.1 a ha
    exact (hB.2 _ ⟨⟨k, hkJ⟩ * k₁, k₂, by rw [hk]; simp [mul_assoc]⟩).exists
  have exA : ∀ b ∈ B, ∃ a, a ∈ A ∧ a⁻¹ * (k⁻¹ * b) ∈ J := by
    intro b hb
    obtain ⟨k₁, k₂, hk⟩ := hB.1 b hb
    exact (hA.2 _ ⟨⟨k, hkJ⟩⁻¹ * k₁, k₂, by rw [hk]; simp [mul_assoc]⟩).exists
  choose! φ hφB hφJ using exB
  choose! ψ hψA hψJ using exA
  refine Finset.sum_nbij' φ ψ hφB hψA ?_ ?_ ?_
  · intro a ha
    obtain ⟨k₁, k₂, hk⟩ := hB.1 (φ a) (hφB a ha)
    have hg : ∃ k₁ k₂ : J, k⁻¹ * φ a = (k₁ : G) * x * k₂ :=
      ⟨⟨k, hkJ⟩⁻¹ * k₁, k₂, by rw [hk]; simp [mul_assoc]⟩
    refine (hA.2 _ hg).unique ⟨hψA _ (hφB a ha), hψJ _ (hφB a ha)⟩ ⟨ha, ?_⟩
    rw [show a⁻¹ * (k⁻¹ * φ a) = ((φ a)⁻¹ * (k * a))⁻¹ by group]
    exact J.inv_mem (hφJ a ha)
  · intro b hb
    obtain ⟨k₁, k₂, hk⟩ := hA.1 (ψ b) (hψA b hb)
    have hg : ∃ k₁ k₂ : J, k * ψ b = (k₁ : G) * x * k₂ :=
      ⟨⟨k, hkJ⟩ * k₁, k₂, by rw [hk]; simp [mul_assoc]⟩
    refine (hB.2 _ hg).unique ⟨hφB _ (hψA b hb), hφJ _ (hψA b hb)⟩ ⟨hb, ?_⟩
    rw [show b⁻¹ * (k * ψ b) = ((ψ b)⁻¹ * (k⁻¹ * b))⁻¹ by group]
    exact J.inv_mem (hψJ b hb)
  · intro a ha
    exact hterm a ha (φ a) (hφB a ha) (hφJ a ha)

theorem dcOp_eq_of_isDC (ρ : Γ →* Module.End ℂ W) {J L : Subgroup G} {χ : J →* ℂˣ}
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) {x : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J x B)
    (hAL : ∀ a ∈ A, a ∈ L) (hBL : ∀ b ∈ B, b ∈ L) {F : G → W} (hF : F ∈ AdForms ι ρ J χ) :
    dcOp A F = dcOp B F := by
  funext h
  have hs := sum_mul_reps ι ρ hχ hA hB hAL hBL hF J.one_mem L.one_mem h
  simp only [mul_one] at hs
  exact hs

theorem LocSplit.dcOp_mem (ρ : Γ →* Module.End ℂ W) {J L : Subgroup G} {χ : J →* ℂˣ} (hs : LocSplit J L)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) {x : G} {A : Finset G} (hA : IsDC J x A) (hAL : ∀ a ∈ A, a ∈ L)
    {F : G → W} (hF : F ∈ AdForms ι ρ J χ) : dcOp A F ∈ AdForms ι ρ J χ := by
  have hF' : ∀ (γ : Γ) (g : G) (j : J), F (ι γ * g * j) = (χ j : ℂ) • ρ γ (F g) := hF
  show ∀ (γ : Γ) (g : G) (j : J), dcOp A F (ι γ * g * j) = (χ j : ℂ) • ρ γ (dcOp A F g)
  intro γ g j
  obtain ⟨j₁, hj₁J, j₂, hj₂J, hj₁L, hj, hc⟩ := hs (j : G) j.2
  have hχj : χ j = χ ⟨j₂, hj₂J⟩ := by
    have hjj : j = ⟨j₁, hj₁J⟩ * ⟨j₂, hj₂J⟩ := Subtype.ext hj
    rw [hjj, map_mul, hχ ⟨j₁, hj₁J⟩ hj₁L, one_mul]
  have hsum := sum_mul_reps ι ρ hχ hA hA hAL hAL hF hj₁J hj₁L g
  simp only [dcOp]
  rw [← hsum, map_sum, Finset.smul_sum, hχj]
  refine Finset.sum_congr rfl fun a ha => ?_
  have e : ι γ * g * (j : G) * a = ι γ * (g * j₁ * a) * ((⟨j₂, hj₂J⟩ : J) : G) := by
    rw [hj]; simp only [mul_assoc]; rw [(hc a (hAL a ha)).eq]
  rw [e]
  exact hF' γ (g * j₁ * a) ⟨j₂, hj₂J⟩

end Operators

example : LocSplit ((Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)).prod (⊤ : Subgroup (Equiv.Perm (Fin 3))))
    ((⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥) := locSplit_prod_left _ _

example {G : Type} [Group G] {J L : Subgroup G} (h : J ≤ L) : LocSplit J L :=
  fun k hk => ⟨k, hk, 1, J.one_mem, h hk, (mul_one k).symm, fun l _ => Commute.one_left l⟩

example : Formalism.L2.Col.gaussBin 2 4 2 = 35 := by decide

end GlobalTheory.HkB
