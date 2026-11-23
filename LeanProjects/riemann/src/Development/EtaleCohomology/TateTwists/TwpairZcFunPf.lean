import Development.EtaleCohomology.TateTwists.EtaleTateTwistCupPairingOfTensorAndResolutionPro

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

section
variable {R : Type} [CommRing R]

lemma zc_pull_mk {K L I : Cx R} (f : K ⟶ L) (n : ℤ) (b : Cocycle L I n) :
    cpull f I n (CohomologyClass.mk b) =
      CohomologyClass.mk (Cocycle.mk ((Cochain.ofHom f).comp b.1 (zero_add n)) (n + 1) rfl
        (by rw [δ_ofHom_comp, Cocycle.δ_eq_zero, Cochain.comp_zero])) := by
  rw [cpre_mk]; congr 1

lemma zc_push_mk {K I J : Cx R} (g : I ⟶ J) (n : ℤ) (a : Cocycle K I n) :
    cpush K g n (CohomologyClass.mk a) =
      CohomologyClass.mk (Cocycle.mk (a.1.comp (Cochain.ofHom g) (add_zero n)) (n + 1) rfl
        (by rw [δ_comp_ofHom, Cocycle.δ_eq_zero, Cochain.zero_comp])) := by
  rw [cpost_mk]; congr 1

end

theorem twpair_zc_fun_of : twpair_zc_fun := by
  intro R _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K I n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    constructor
    · rw [zc_pull_mk]; congr 1; apply Cocycle.ext; simp [Cochain.id_comp]
    · rw [zc_push_mk]; congr 1; apply Cocycle.ext; simp [Cochain.comp_id]
  · intro K L M f g I n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_pull_mk, zc_pull_mk, zc_pull_mk]; congr 1; apply Cocycle.ext
    simp [Cochain.ofHom_comp]
  · intro K I J M f g n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_push_mk, zc_push_mk, zc_push_mk]
    congr 1
  · intro K L I J f g n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_push_mk, zc_pull_mk, zc_pull_mk, zc_push_mk]; congr 1; apply Cocycle.ext
    simp
  · intro K L f g ⟨ho⟩ I n
    obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g ho
    constructor
    · ext x
      obtain ⟨b, rfl⟩ := x.mk_surjective
      rw [zc_pull_mk, zc_pull_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨n.negOnePow • z.comp b.1 (by omega), ?_⟩
      have hb : δ n (n + 1) (b : Cochain L I n) = 0 := Cocycle.δ_eq_zero _ _
      have hz' : δ (-1) 0 z = Cochain.ofHom f - Cochain.ofHom g := by rw [hz]; abel
      rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) rfl]
      simp only [hb, Cochain.comp_zero, zero_add, smul_smul, Int.units_mul_self, one_smul, hz',
        Cochain.sub_comp]
      rfl
    · ext x
      obtain ⟨a, rfl⟩ := x.mk_surjective
      rw [zc_push_mk, zc_push_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨a.1.comp z (by omega), ?_⟩
      have ha : δ n (n + 1) (a : Cochain I K n) = 0 := Cocycle.δ_eq_zero _ _
      have hz' : δ (-1) 0 z = Cochain.ofHom f - Cochain.ofHom g := by rw [hz]; abel
      rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega)]
      simp only [ha, Cochain.zero_comp, smul_zero, add_zero, hz', Cochain.comp_sub]
      rfl

end LateralTheory.EtaleFoundations
