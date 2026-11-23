import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobenius

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem conjBy_left {G C : Type} [Group G] [CommRing C] (h : GL (Fin 3) C) (r : G →* GG 3 C) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  show (GG.ofGL h * r g * (GG.ofGL h)⁻¹).left = _
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  simp only [SemidirectProduct.right_inl, SemidirectProduct.left_inl, SemidirectProduct.mul_right, hg, mul_one, inv_one, map_one, MulAut.one_apply]

theorem conjBy_mat {G C : Type} [Group G] [CommRing C] (h : GL (Fin 3) C) (r : G →* GG 3 C) (g : G)
    (hg : (r g).right = 1) :
    (conjBy h r g).mat = (h : Matrix (Fin 3) (Fin 3) C) * (r g).mat * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  unfold GG.mat
  rw [conjBy_left h r g hg, Units.val_mul, Units.val_mul]

section Conj

variable {C : Type} [CommRing C]

theorem ent_mem_mul {J : Ideal C} {N : Matrix (Fin 3) (Fin 3) C} (hN : ∀ i j, N i j ∈ J)
    (A B : Matrix (Fin 3) (Fin 3) C) (i j : Fin 3) : (A * N * B) i j ∈ J := by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _
    (Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hN m k))

theorem conj_sub_scalar (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) (c : C) :
    (h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ c =
      (h : Matrix (Fin 3) (Fin 3) C) * (M - Matrix.scalar _ c) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  have e : (h : Matrix (Fin 3) (Fin 3) C) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← (Matrix.scalar_commute c (fun _ => Commute.all _ _) (h : Matrix (Fin 3) (Fin 3) C)),
    Matrix.mul_assoc (Matrix.scalar _ c), e, Matrix.mul_one]

theorem conj_mul_three_alt (h : GL (Fin 3) C) (A B E : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * A * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) *
      ((h : Matrix (Fin 3) (Fin 3) C) * B * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) *
      ((h : Matrix (Fin 3) (Fin 3) C) * E * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) =
      (h : Matrix (Fin 3) (Fin 3) C) * (A * B * E) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  have e : ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (h : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) (h : Matrix (Fin 3) (Fin 3) C), e, Matrix.one_mul,
    ← Matrix.mul_assoc ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) (h : Matrix (Fin 3) (Fin 3) C), e, Matrix.one_mul]

theorem unconj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    M = ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) *
      ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) * (h : Matrix (Fin 3) (Fin 3) C) := by
  have e : ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (h : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [e, Matrix.mul_one, ← Matrix.mul_assoc, e, Matrix.one_mul]

theorem trace_conj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem charpoly_conj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)).charpoly = M.charpoly := by
  rw [Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj h M

end Conj

end GlobalTheory.OrdLoc

namespace GlobalTheory.OrdLoc

theorem ordEqs_conjBy : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG 3 C) (h : GL (Fin 3) C), HasMult D.η r → GlobalTheory.OrdLoc.ordIdeal D (conjBy h r) = GlobalTheory.OrdLoc.ordIdeal D r ∧ (∀ a, GlobalTheory.OrdLoc.dd D (conjBy h r) a = GlobalTheory.OrdLoc.dd D r a) ∧ GlobalTheory.OrdLoc.del D (conjBy h r) = GlobalTheory.OrdLoc.del D r := by
  intro l _ O _ _ _ D C _ _ r h hr
  have hR : ∀ s ∈ D.HL, (r s).right = 1 := fun s hs =>
    (hr s).trans (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).1)
  have hM : ∀ s ∈ D.HL, (conjBy h r s).mat = (h : Matrix (Fin 3) (Fin 3) C) * (r s).mat *
      ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := fun s hs => conjBy_mat h r s (hR s hs)
  have hsh : ∀ s ∈ D.HL, ∀ a, sh D (conjBy h r) a s = (h : Matrix (Fin 3) (Fin 3) C) * sh D r a s *
      ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro s hs a
    unfold sh
    rw [hM s hs, conj_sub_scalar]
  have hs0 : s0 D ∈ D.HL := (GlobalTheory.OrdLoc.hl_basic D).2.2.2.2.1
  obtain ⟨⟨hfr, -⟩, -⟩ := GlobalTheory.OrdLoc.fr_isFr D
  have htr : ∀ a, tr D (conjBy h r) a = tr D r a := by
    intro a
    unfold tr
    rw [hsh _ hs0, hsh _ hs0, hM _ hfr, conj_mul_three_alt, trace_conj]
  have hdd : ∀ a, dd D (conjBy h r) a = dd D r a := by
    intro a
    unfold dd
    rw [htr, htr]
  refine ⟨?_, hdd, ?_⟩
  · unfold ordIdeal
    apply le_antisymm
    · refine Ideal.span_le.2 (Set.union_subset ?_ ?_)
      · rintro x ⟨s, hs, i, rfl⟩
        apply Ideal.subset_span
        refine Or.inl ⟨s, hs, i, ?_⟩
        rw [hM s (Subgroup.mem_inf.1 hs).1, charpoly_conj]
      · rintro x ⟨s, hs, i, j, rfl⟩
        rw [hsh _ (Subgroup.mem_inf.1 (hs 0)).1, hsh _ (Subgroup.mem_inf.1 (hs 1)).1,
          hsh _ (Subgroup.mem_inf.1 (hs 2)).1, conj_mul_three_alt]
        apply ent_mem_mul
        intro i' j'
        exact Ideal.subset_span (Or.inr ⟨s, hs, i', j', rfl⟩)
    · refine Ideal.span_le.2 (Set.union_subset ?_ ?_)
      · rintro x ⟨s, hs, i, rfl⟩
        apply Ideal.subset_span
        refine Or.inl ⟨s, hs, i, ?_⟩
        rw [hM s (Subgroup.mem_inf.1 hs).1, charpoly_conj]
      · rintro x ⟨s, hs, i, j, rfl⟩
        rw [unconj h (sh D r 0 (s 0) * sh D r 1 (s 1) * sh D r 2 (s 2))]
        apply ent_mem_mul
        intro i' j'
        apply Ideal.subset_span
        refine Or.inr ⟨s, hs, i', j', ?_⟩
        rw [hsh _ (Subgroup.mem_inf.1 (hs 0)).1, hsh _ (Subgroup.mem_inf.1 (hs 1)).1,
          hsh _ (Subgroup.mem_inf.1 (hs 2)).1, conj_mul_three_alt]
  · unfold del
    rw [hdd 0, hdd 1]

end GlobalTheory.OrdLoc
