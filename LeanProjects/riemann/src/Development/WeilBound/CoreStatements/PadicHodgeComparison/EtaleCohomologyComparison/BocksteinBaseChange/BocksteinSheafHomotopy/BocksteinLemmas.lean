import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison.PostcompositionHomotopy

open GlobalTheory.EtC

variable {R : Type} [CommRing R]

theorem cpost_homotopy (K : Cx R) {I J : Cx R} {f g : I ⟶ J} (h : Homotopy f g) (n : ℤ) (x : CohomologyClass K I n) :
    cpost K (Cocycle.ofHom f) n n (add_zero n) x = cpost K (Cocycle.ofHom g) n n (add_zero n) x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [cpost_mk, cpost_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨n - 1, by omega, α.1.comp (Cochain.ofHomotopy h) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero,
    Cochain.zero_comp, smul_zero, add_zero]
  ext p q hpq
  simp [zcomp, Cochain.comp_sub]

theorem cpost_add (K : Cx R) {I J : Cx R} (f g : I ⟶ J) (n : ℤ) (x : CohomologyClass K I n) :
    cpost K (Cocycle.ofHom (f + g)) n n (add_zero n) x =
      cpost K (Cocycle.ofHom f) n n (add_zero n) x + cpost K (Cocycle.ofHom g) n n (add_zero n) x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [cpost_mk, cpost_mk, cpost_mk, ← CohomologyClass.mk_add]
  congr 1
  all_goals (ext p q hpq; simp [zcomp, Cochain.ofHom_add, Cochain.comp_add])

theorem cpost_id (K : Cx R) (I : Cx R) (n : ℤ) (x : CohomologyClass K I n) :
    cpost K (Cocycle.ofHom (𝟙 I)) n n (add_zero n) x = x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [cpost_mk]
  congr 1
  all_goals (ext p q hpq; simp [zcomp])

theorem cpost_comp (K : Cx R) {I J L : Cx R} (f : I ⟶ J) (g : J ⟶ L) (n : ℤ) (x : CohomologyClass K I n) :
    cpost K (Cocycle.ofHom (f ≫ g)) n n (add_zero n) x =
      cpost K (Cocycle.ofHom g) n n (add_zero n) (cpost K (Cocycle.ofHom f) n n (add_zero n) x) := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [cpost_mk, cpost_mk, cpost_mk]
  congr 1

theorem post_eq (K : Cx R) {F G : Shv R} (φ : F ⟶ G)
    (g : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex)
    (hg : (injectiveResolution F).ι ≫ g = (CochainComplex.single₀ _).map φ ≫ (injectiveResolution G).ι)
    (n : ℤ) (x : HK R K F n) :
    HK.post R K φ n x = cpost K (Cocycle.ofHom (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)) n n (add_zero n) x :=
  cpost_homotopy K ((InjectiveResolution.descHomotopy φ _ g (InjectiveResolution.desc_commutes _ _ _) hg).extend
    ComplexShape.embeddingUpNat) n x

theorem post_id (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.post R K (𝟙 F) n x = x := by
  rw [post_eq K (𝟙 F) (𝟙 _) (by simp), HomologicalComplex.extendMap_id]
  exact cpost_id K _ n x

theorem post_add (K : Cx R) {F G : Shv R} (φ ψ : F ⟶ G) (n : ℤ) (x : HK R K F n) :
    HK.post R K (φ + ψ) n x = HK.post R K φ n x + HK.post R K ψ n x := by
  rw [post_eq K (φ + ψ) (InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F) +
    InjectiveResolution.desc ψ (injectiveResolution G) (injectiveResolution F))
    (by rw [Preadditive.comp_add, InjectiveResolution.desc_commutes, InjectiveResolution.desc_commutes,
      Functor.map_add, Preadditive.add_comp]),
    HomologicalComplex.extendMap_add, cpost_add]
  rfl

theorem post_comp (K : Cx R) {F G L : Shv R} (φ : F ⟶ G) (ψ : G ⟶ L) (n : ℤ) (x : HK R K F n) :
    HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x) := by
  rw [post_eq K (φ ≫ ψ) (InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F) ≫
    InjectiveResolution.desc ψ (injectiveResolution L) (injectiveResolution G))
    (by rw [← Category.assoc, InjectiveResolution.desc_commutes, Category.assoc, InjectiveResolution.desc_commutes,
      Functor.map_comp, Category.assoc]),
    HomologicalComplex.extendMap_comp, cpost_comp]
  rfl

theorem post_zero (K : Cx R) {F G : Shv R} (n : ℤ) (x : HK R K F n) : HK.post R K (0 : F ⟶ G) n x = 0 := by
  have h := post_add K (0 : F ⟶ G) 0 n x
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

theorem post_nsmul (K : Cx R) {F G : Shv R} (f : F ⟶ G) (n : ℤ) (k : ℕ) (x : HK R K F n) :
    HK.post R K (k • f) n x = k • HK.post R K f n x := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, post_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, post_add, ih]

theorem post_nsmul_id (K : Cx R) (F : Shv R) (n : ℤ) (k : ℕ) (x : HK R K F n) : HK.post R K (k • 𝟙 F) n x = k • x := by
  induction k with
  | zero =>
    rw [zero_nsmul, zero_nsmul]
    have h := post_add K (0 : F ⟶ F) 0 n x
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  | succ k ih => rw [succ_nsmul, succ_nsmul, post_add, ih, post_id]

end CrystallineSemistableComparison.PostcompositionHomotopy
