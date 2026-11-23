import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory

theorem exists_reps_sup_of_finite_quot (E : Type) [Field E] (H : Type) [AddCommGroup H]
    [Module (𝓞 E) H] (Z₁ Z₀ : Submodule (𝓞 E) H) (C : AddSubgroup H)
    (hfin : Finite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)) :
    ∃ R : Finset H, (∀ x ∈ R, x ∈ Z₁) ∧
      (∀ x ∈ R, ∀ y ∈ R, x - y ∈ Z₀.toAddSubgroup ⊔ C → x = y) ∧
      ∀ y ∈ Z₁, ∃ x ∈ R, y - x ∈ Z₀.toAddSubgroup ⊔ C := by
  classical
  letI := Fintype.ofFinite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)
  set Z : AddSubgroup H := Z₀.toAddSubgroup ⊔ C with hZ
  let s : (↥Z₁ ⧸ Z₀.comap Z₁.subtype) → ↥Z₁ :=
    Function.surjInv (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype))
  have hs : ∀ z, Submodule.Quotient.mk (s z) = z := fun z =>
    Function.surjInv_eq (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype)) z
  let T : Finset (H ⧸ Z) := Finset.univ.image fun z => QuotientAddGroup.mk (s z : H)
  have hsurj : (Z₁ : Set H).SurjOn (QuotientAddGroup.mk : H → H ⧸ Z) T := by
    intro t ht
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    exact ⟨s z, (s z).2, rfl⟩
  obtain ⟨R, hR, hinj, him⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ hsurj
  refine ⟨R, fun x hx => hR hx, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hinj hx hy (QuotientAddGroup.eq_iff_sub_mem.2 hxy)
  · intro y hy
    have h1 : (⟨y, hy⟩ : ↥Z₁) - s (Submodule.Quotient.mk ⟨y, hy⟩) ∈ Z₀.comap Z₁.subtype :=
      (Submodule.Quotient.eq _).1 (hs _).symm
    have h2 : y - (s (Submodule.Quotient.mk ⟨y, hy⟩) : H) ∈ Z :=
      AddSubgroup.mem_sup_left (by simpa using h1)
    have h3 : (QuotientAddGroup.mk y : H ⧸ Z) ∈ T :=
      Finset.mem_image.2 ⟨_, Finset.mem_univ _, (QuotientAddGroup.eq_iff_sub_mem.2 h2).symm⟩
    rw [← him] at h3
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 h3
    exact ⟨x, hx, QuotientAddGroup.eq_iff_sub_mem.1 hxy.symm⟩

theorem latSum_eq_sum_sum_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (H : Type) [AddCommGroup H] [Module (𝓞 E) H] (Z₁ Z₀ : Submodule (𝓞 E) H) (C : AddSubgroup H) (J : Finset H), Z₀ ≤ Z₁ → C ≤ Z₁.toAddSubgroup → Finite (↥Z₁ ⧸ Z₀.comap Z₁.subtype) → IsReps Z₀.toAddSubgroup C J → ∃ R : Finset H, (∀ x ∈ R, x ∈ Z₁) ∧ ∀ (M : Type) [AddCommMonoid M] (f : H → M), (∀ x ∈ Z₁, ∀ y ∈ Z₀, f (x + y) = f x) → latSum Z₁ Z₀ f = ∑ x ∈ R, ∑ j ∈ J, f (x + j) := by
  intro E _ _ _ H _ _ Z₁ Z₀ C J h01 hC hfin hJ
  classical
  obtain ⟨R, hR, hRinj, hRsurj⟩ := exists_reps_sup_of_finite_quot E H Z₁ Z₀ C hfin
  obtain ⟨hJC, hJinj, hJsurj⟩ := hJ
  refine ⟨R, hR, ?_⟩
  intro M _ f hf
  letI := Fintype.ofFinite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)
  have hmem : ∀ p ∈ R ×ˢ J, p.1 + p.2 ∈ Z₁ := fun p hp =>
    Z₁.add_mem (hR _ (Finset.mem_product.1 hp).1) (hC (hJC _ (Finset.mem_product.1 hp).2))
  unfold latSum
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_product']
  symm
  refine Finset.sum_bij
    (fun p hp => (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩ : ↥Z₁ ⧸ Z₀.comap Z₁.subtype))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨x, j⟩ hp ⟨x', j'⟩ hp' h
    obtain ⟨hx, hj⟩ := Finset.mem_product.1 hp
    obtain ⟨hx', hj'⟩ := Finset.mem_product.1 hp'
    have h1 : x + j - (x' + j') ∈ Z₀ := by
      simpa using (Submodule.Quotient.eq _).1 h
    have h2 : x = x' := by
      refine hRinj x hx x' hx' ?_
      have : x - x' = (x + j - (x' + j')) + (j' - j) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup h1 (C.sub_mem (hJC _ hj') (hJC _ hj))
    subst h2
    have h3 : j = j' := by
      refine hJinj j hj j' hj' ?_
      have : j - j' = x + j - (x + j') := by abel
      rw [this]
      exact h1
    rw [h3]
  · intro z _
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨x, hx, hyx⟩ := hRsurj y hy
    obtain ⟨a, ha, c, hc, hac⟩ := AddSubgroup.mem_sup.1 hyx
    obtain ⟨j, hj, hcj⟩ := hJsurj c hc
    refine ⟨(x, j), Finset.mem_product.2 ⟨hx, hj⟩, (Submodule.Quotient.eq _).2 ?_⟩
    have h1 : x + j - y = -(a + (c - j)) := by
      have : y = x + (a + c) := by rw [hac]; abel
      rw [this]; abel
    have h2 : x + j - y ∈ Z₀ := by
      rw [h1]
      exact Z₀.neg_mem (Z₀.add_mem ha hcj)
    simpa using h2
  · intro p hp
    set w := Function.surjInv (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype))
      (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩) with hw
    have h0 : Submodule.Quotient.mk w =
        (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩ : ↥Z₁ ⧸ Z₀.comap Z₁.subtype) :=
      Function.surjInv_eq _ _
    have h1 : (w : H) - (p.1 + p.2) ∈ Z₀ := by
      simpa using (Submodule.Quotient.eq _).1 h0
    have h2 := hf _ (hmem p hp) _ h1
    rw [← h2]
    congr 1
    abel

end GlobalTheory
