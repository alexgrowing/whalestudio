import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.OrbStabZ

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdE

section Gen

variable {G : Type} [Group G] {ι : Type} {H : ι → Type} [∀ i, Group (H i)] (π : ∀ i, G →* H i)

def glob (A : ∀ i, Subgroup (H i)) : Subgroup G := ⨅ i, (A i).comap (π i)

theorem mem_glob {A : ∀ i, Subgroup (H i)} {g : G} : g ∈ glob π A ↔ ∀ i, π i g ∈ A i := by
  simp [glob, Subgroup.mem_iInf]

theorem relIndex_glob (A C : ∀ i, Subgroup (H i)) (S : Finset ι) (hS : ∀ i ∉ S, A i = C i)
    (hfin : ∀ i, (C i).relIndex (A i) ≠ 0)
    (happrox : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ A i ⊓ C i) ∧ ∀ i ∉ S, π i g ∈ A i) :
    (glob π C).relIndex (glob π A) = ∏ i ∈ S, (C i).relIndex (A i) := by
  classical
  set K := (glob π C).subgroupOf (glob π A) with hK
  let Φ : ↥(glob π A) → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι)) := fun g i =>
    QuotientGroup.mk ⟨π i g, (mem_glob π).1 g.2 i⟩
  have hrel : ∀ a b : ↥(glob π A), Φ a = Φ b ↔ a⁻¹ * b ∈ K := by
    intro a b
    rw [hK, Subgroup.mem_subgroupOf, mem_glob]
    simp only [Φ, funext_iff]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · have h1 := h ⟨i, hi⟩
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
        simpa using h1
      · rw [← hS i hi]
        simpa using (A i).mul_mem ((A i).inv_mem ((mem_glob π).1 a.2 i)) ((mem_glob π).1 b.2 i)
    · intro h i
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using h i
  have hsurj : Function.Surjective Φ := by
    intro q
    choose r hr using fun i : S => QuotientGroup.mk_surjective (q i)
    obtain ⟨g, hg1, hg2⟩ := happrox (fun i => if hi : i ∈ S then ((r ⟨i, hi⟩ : A i) : H i) else 1)
    have hgA : g ∈ glob π A := by
      rw [mem_glob]
      intro i
      by_cases hi : i ∈ S
      · have h1 := hg1 i hi
        simp only [dif_pos hi] at h1
        have h2 := (A i).mul_mem (r ⟨i, hi⟩).2 (Subgroup.mem_inf.1 h1).1
        simpa using h2
      · exact hg2 i hi
    refine ⟨⟨g, hgA⟩, ?_⟩
    funext i
    rw [← hr i]
    simp only [Φ]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := hg1 i.1 i.2
    simp only [dif_pos i.2] at h1
    simpa using (C i).inv_mem (Subgroup.mem_inf.1 h1).2
  let Ψ : ↥(glob π A) ⧸ K → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι)) :=
    Quotient.lift Φ (fun a b hab => (hrel a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hbij : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      exact QuotientGroup.eq.2 ((hrel a b).1 hxy)
    · intro q
      obtain ⟨a, ha⟩ := hsurj q
      exact ⟨QuotientGroup.mk a, ha⟩
  have hcard := Nat.card_congr (Equiv.ofBijective Ψ hbij)
  rw [Nat.card_pi] at hcard
  rw [← Finset.prod_coe_sort S]
  exact hcard

theorem idxRatio_glob (A C : ∀ i, Subgroup (H i)) (S : Finset ι) (hS : ∀ i ∉ S, A i = C i)
    (hfinA : ∀ i, (C i).relIndex (A i) ≠ 0) (hfinC : ∀ i, (A i).relIndex (C i) ≠ 0)
    (happrox : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ A i ⊓ C i) ∧ ∀ i ∉ S, π i g ∈ A i) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (glob π A) (glob π C) = ∏ i ∈ S, Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A i) (C i) := by
  have happrox' : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ C i ⊓ A i) ∧ ∀ i ∉ S, π i g ∈ C i := by
    intro h
    obtain ⟨g, hg1, hg2⟩ := happrox h
    refine ⟨g, fun i hi => ?_, fun i hi => ?_⟩
    · rw [inf_comm]
      exact hg1 i hi
    · rw [← hS i hi]
      exact hg2 i hi
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [relIndex_glob π A C S hS hfinA happrox,
    relIndex_glob π C A S (fun i hi => (hS i hi).symm) hfinC happrox']
  push_cast
  rw [Finset.prod_div_distrib]

end Gen

end Formalism.L2.SG.Pf.ProdE
