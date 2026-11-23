import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
  PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel Topology MatrixGroups

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSSmooth

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem mem_congruenceSubgroup_of_div {c : ℕ} {g : GL (Fin n) F}
    (hg : Div (c + 1) ((g : Matrix (Fin n) (Fin n) F) - 1)) :
    g ∈ congruenceSubgroup F n (c + 1) := by
  choose y hy hgy using hg
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hent : ∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (c + 1) * y i j := fun i j => by
    rw [← hgy i j, Matrix.sub_apply]
  have hint : ∀ i j, g i j ∈ 𝒪[F] := fun i j => by
    have h1 : g i j = (uniformizer F : F) ^ (c + 1) * y i j +
        (1 : Matrix (Fin n) (Fin n) F) i j := by rw [← hent i j, sub_add_cancel]
    rw [h1]
    exact add_mem (mul_mem (pow_mem (uniformizer F).2 _) (hy i j)) (hone i j)
  let A : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨g i j, hint i j⟩
  have hres : (IsLocalRing.residue 𝒪[F]).mapMatrix A = 1 := by
    ext i j
    have hmem : A i j - (1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
      have h1 : A i j - (1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j =
          uniformizer F * (uniformizer F ^ c * ⟨y i j, hy i j⟩) := by
        apply Subtype.ext
        have h2 : (((1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j : 𝒪[F]) : F) =
            (1 : Matrix (Fin n) (Fin n) F) i j := by
          rw [Matrix.one_apply, Matrix.one_apply]
          split_ifs <;> simp
        simp only [AddSubgroupClass.coe_sub, h2, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
        change g i j - _ = _
        rw [hent i j]
        ring
      rw [h1]
      exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (irreducible_uniformizer F).not_isUnit)
    have h3 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
    rw [map_sub, sub_eq_zero] at h3
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit A.det := by
    have h1 : IsLocalRing.residue 𝒪[F] A.det = 1 := by
      rw [RingHom.map_det, hres, Matrix.det_one]
    by_contra h
    have h2 := (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [h2] at h1
    exact zero_ne_one h1
  rw [mem_congruenceSubgroup_iff]
  refine ⟨⟨Matrix.GeneralLinearGroup.mk'' A hdet, Units.ext rfl⟩, fun i j => ?_⟩
  rw [hent i j, map_mul, map_pow]
  exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hy i j))

theorem smooth_of_isSmooth {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (h : GlobalTheory.PRep.IsSmooth ρ) : Smooth ρ := fun u => by
  have h1 : {g : GL (Fin n) F | ρ g u = u} ∈ 𝓝 (1 : GL (Fin n) F) :=
    (h u).mem_nhds (by simp)
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one F n).mem_iff.1 h1
  exact ⟨m, fun g hg => hm (congruenceSubgroup_antitone F n (Nat.le_succ m)
    (mem_congruenceSubgroup_of_div hg))⟩

theorem g3 : G3 := fun _ _ _ _ _ π w => smooth_of_isSmooth _ (π.isSmooth_locRep w)

end GlobalTheory.CompanionTheory.JSSmooth

end
