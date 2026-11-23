import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrExt

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem res_dual (O : Type) [CommRing O] [IsLocalRing O] [IsCO O (DualNumber (ResidueField O))]
    (x : DualNumber (ResidueField O)) : res O _ x = x.fst := by
  obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective x.fst
  have ha : (algebraMap O (DualNumber (ResidueField O)) o).fst = x.fst := by
    rw [← ho]
    first
      | rfl
      | rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, IsLocalRing.ResidueField.algebraMap_eq]
  have hfst : (x - algebraMap O _ o).fst = 0 := by
    rw [TrivSqZeroExt.fst_sub, ha, sub_self]
  have hsq : (x - algebraMap O _ o) * (x - algebraMap O _ o) = 0 := by
    ext
    · rw [TrivSqZeroExt.fst_mul, hfst, mul_zero, TrivSqZeroExt.fst_zero]
    · rw [TrivSqZeroExt.snd_mul, hfst, zero_smul, MulOpposite.op_zero, zero_smul, add_zero, TrivSqZeroExt.snd_zero]
  have hmem : x - algebraMap O _ o ∈ maximalIdeal (DualNumber (ResidueField O)) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h2 := hu.mul hu
    rw [hsq] at h2
    exact not_isUnit_zero h2
  have h0 := (res_eq_zero_iff O _ _).2 hmem
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h0
  rw [h0, ← ha]
  first
    | rfl
    | rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]

theorem UpperTheory.V.Fr.pr_dof :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ [IsCO O (DualNumber (ResidueField O))] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → ∀ (ρ' : NRep F n (DualNumber (ResidueField O))) (r' : F.Γ →* GG n (DualNumber (ResidueField O))), ρ'.Cont (maximalIdeal _) → ρ'.bar O = ρ.bar O → (∀ s, (r' s).right = F.del s) → (r' F.c).mat = 1 → (∀ s : F.G0, (r' s).mat = ρ'.r s) → ∃ D ∈ Tan O R, ∀ s, (r' s).mat.map TrivSqZeroExt.snd = B.tanCo O D s * ((B.bar O).r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ _ R _ _ _ ρ B hU hOf ρ' r' hc' hbar hnu hatc hres
  obtain ⟨g, hg, -⟩ := hU.univ _ ρ' hc' hbar
  have hfst : ∀ x, (g x).fst = res O R x := fun x => by
    rw [← res_dual O (g x), res_map]
  let Dd : R →ₗ[O] ResidueField O :=
    { toFun := fun x => (g x).snd
      map_add' := fun x y => by
        simp only [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun a x => by
        simp only [map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
  have hDd : ∀ x, Dd x = (g x).snd := fun _ => rfl
  have hof := hOf.map (g : R →+* DualNumber (ResidueField O))
  have hr : (Box.map (g : R →+* DualNumber (ResidueField O)) B).r = r' := by
    refine pr_ext hF _ _ _ (Box.nu _) hnu ?_ ?_
    · rw [hof.atc, hatc]
    · intro s
      rw [hof.res, hg, hres]
  refine ⟨Dd, ?_, fun s => ?_⟩
  · intro f h
    rw [hDd, hDd, hDd, map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]
  · rw [← hr]
    show ((B.r s).mat.map g).map TrivSqZeroExt.snd = ((B.r s).mat.map Dd * ((((Box.bar O B).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))) * ((((Box.bar O B).r s).left : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))
    rw [mul_assoc, Units.inv_mul, mul_one, Matrix.map_map]
    rfl
