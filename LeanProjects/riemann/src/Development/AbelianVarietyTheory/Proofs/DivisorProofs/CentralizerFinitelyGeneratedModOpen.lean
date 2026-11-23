import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtensionProductDecompositionStatement
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerBoundedValuationKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedSubgroupFiniteCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerFiniteGenerationTransfer

noncomputable section

open Matrix GlobalTheory.LKRes ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct Classical

namespace GlobalTheory.CentFG

theorem field_case (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hL : FiniteDimensional ℚ_[p] L) (n : ℕ) (N : GL (Fin n) L) (hN : N.val.charpoly.Separable) :
    ∃ G : Finset (GL (Fin n) L), (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) L)) ∪
        ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKLoc.KintK p L n : Subgroup _) : Set (GL (Fin n) L))) := by
  obtain ⟨v, c, hv⟩ := GlobalTheory.T.centralizer_bounded_valuation_kernel p L hL n N hN
  have hfg : v.range.FG := by
    rw [Subgroup.fg_iff_add_fg]
    exact (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule v.range.toAddSubgroup)).1
      (IsNoetherian.noetherian (R := ℤ) (M := Additive (Multiplicative (Fin n → ℤ))) _)
  obtain ⟨S, hS⟩ := hfg
  have hpre : ∀ s : S, ∃ z : Subgroup.centralizer {N}, v z = s := fun s =>
    (show (s : Multiplicative (Fin n → ℤ)) ∈ v.range from hS ▸ Subgroup.subset_closure s.2)
  choose pre hpre using hpre
  let B : Subgroup (GL (Fin n) L) := v.ker.map (Subgroup.centralizer {N}).subtype
  obtain ⟨T, hT, hTB⟩ := GlobalTheory.T.bounded_subgroup_finite_cosets p L hL n B c (by
    rintro _ ⟨z, hz, rfl⟩ i j
    exact hv z hz i j)
  refine ⟨Finset.univ.image (fun s => ((pre s : Subgroup.centralizer {N}) : GL (Fin n) L)) ∪ T, ?_, ?_⟩
  · intro g hg
    rcases Finset.mem_union.1 hg with h | h
    · obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 h
      exact (pre s).2
    · obtain ⟨z, -, rfl⟩ := hT g h
      exact z.2
  · intro z hz
    set C := Subgroup.closure (((Finset.univ.image (fun s => ((pre s : Subgroup.centralizer {N}) : GL (Fin n) L)) ∪ T :
      Finset _) : Set (GL (Fin n) L)) ∪ ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKLoc.KintK p L n : Subgroup _) : Set (GL (Fin n) L)))
    let W : Subgroup (Subgroup.centralizer {N}) := Subgroup.closure (Set.range pre)
    have hW : W.map v = v.range := by
      rw [MonoidHom.map_closure, ← hS]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        rw [hpre]; exact s.2
      · intro hx
        exact ⟨pre ⟨x, hx⟩, ⟨_, rfl⟩, hpre _⟩
    obtain ⟨w, hw, hwv⟩ : v ⟨z, hz⟩ ∈ W.map v := by rw [hW]; exact ⟨_, rfl⟩
    have hWle : W ≤ C.comap (Subgroup.centralizer {N}).subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨s, rfl⟩
      refine Subgroup.subset_closure (Or.inl ?_)
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
        Set.mem_range]
      exact Or.inl ⟨s, rfl⟩
    have hWC : ∀ y ∈ W, (y : GL (Fin n) L) ∈ C := fun y hy => hWle hy
    have hk : w⁻¹ * ⟨z, hz⟩ ∈ v.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwv, inv_mul_cancel]
    obtain ⟨t, htT, ht⟩ := hTB _ ⟨_, hk, rfl⟩
    have htZ : t ∈ Subgroup.centralizer {N} := by
      obtain ⟨y, -, rfl⟩ := hT t htT; exact y.2
    have hrest : t⁻¹ * ((w : GL (Fin n) L)⁻¹ * z) ∈ C := by
      refine Subgroup.subset_closure (Or.inr ⟨?_, ?_⟩)
      · exact (Subgroup.centralizer {N}).mul_mem ((Subgroup.centralizer {N}).inv_mem htZ)
          ((Subgroup.centralizer {N}).mul_mem ((Subgroup.centralizer {N}).inv_mem w.2) hz)
      · simpa using ht
    have htC : t ∈ C := Subgroup.subset_closure (Or.inl (by simp [htT]))
    have : z = (w : GL (Fin n) L) * t * (t⁻¹ * ((w : GL (Fin n) L)⁻¹ * z)) := by group
    rw [this]
    exact C.mul_mem (C.mul_mem (hWC w hw) htC) hrest

theorem centralizer_le_closure : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K →
    ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∃ G : Finset (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)), (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r))) ∪
        ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKRes.Kres p K n r : Subgroup _) : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)))) := by
  intro p _ K hK n r hr N hN
  obtain ⟨f, -, hf⟩ := qK_eq_pow p K hK
  obtain ⟨e, -, -, -, -, -, -, hint⟩ := GlobalTheory.T.unramified_extension_product_decomposition p K hK f r hf hr
  have hd : 0 < Nat.gcd f r := Nat.gcd_pos_of_pos_right _ hr
  have hfin : FiniteDimensional ℚ_[p] (Kn p K (r / Nat.gcd f r)) :=
    finiteDimensional_Kn p K hK (Nat.div_pos (Nat.gcd_le_right _ hr) hd)
  generalize Nat.gcd f r = g at *
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  exact GlobalTheory.T.centralizer_finite_generation_transfer _ _ k n e (intKQ p K r) (GlobalTheory.LKLoc.intR p K (r / (k + 1))) hint
    (fun N' hN' => field_case p _ hfin n N' hN') N hN

end GlobalTheory.CentFG
