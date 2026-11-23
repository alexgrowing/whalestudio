import Development.EtaleCohomology.EtaleTrace.LRingPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

theorem ringL_holds : RingL := by
  unfold RingL
  intro hI l _
  have h11 := hI.a11
  have h6n := hI.a6nat
  have h6r := hI.a6ring
  have hone : ∀ X : Scheme.{0}, IsUnit (l : Γ(X, ⊤)) → ∀ (n : ℤ) (u : V l X n),
      cupV l X (zero_add n) (oneV l X) u = u := by
    intro X hl n u
    rw [cupV_eq l h11, oneV_eq l h11 X hl]
    have key : cupQ l h11 X (zero_add n) ((1 : ℚ_[l]) ⊗ₜ z0 l h11 X hl) = LinearMap.id := by
      apply ext1; intro x
      rw [cupQ_tmul, LinearMap.id_apply]
      congr 1
      exact Subtype.ext (funext fun j => one_cc h6r (inv_of l X hl j) (x.1 j))
    rw [key, LinearMap.id_apply]
  have hcomm : ∀ (X : Scheme.{0}) (n m r : ℤ) (h : n + m = r) (h' : m + n = r) (u : V l X n) (v : V l X m),
      cupV l X h u v = (n * m).negOnePow • cupV l X h' v u := by
    intro X n m r h h' u v
    simp only [cupV_eq l h11]
    have key : cupQ l h11 X h = (((n * m).negOnePow : ℤˣ) : ℤ) • (cupQ l h11 X h').flip := by
      apply LateralTheory.EtaleTrace.LRingPf.ext2; intro x y
      rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.flip_apply, cupQ_tmul, cupQ_tmul]
      have e := map_zsmul (TensorProduct.mk ℤ_[l] ℚ_[l] (Hl l (sch.obj X) r 0) (1 : ℚ_[l]))
        (((n * m).negOnePow : ℤˣ) : ℤ) (cupL l (sch.obj X) h' h11 y x)
      simp only [TensorProduct.mk_apply] at e
      rw [← e]
      congr 1
      exact Subtype.ext (funext fun j => (comm_cc h h6r h' (x.1 j) (y.1 j)).trans rfl)
    rw [key, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.flip_apply, Units.smul_def]
  refine ⟨fun X n m r h => ?_, fun {Y X} f n m r h u v => ?_, fun X hl => ?_, hone, fun X hl n u => ?_,
    fun {Y X} f hl => ?_, fun X n m r s t w h1 h2 h3 h4 u v z => ?_, hcomm⟩
  · rw [cupV_eq l h11]; exact isCup_cupQ l h11 X h
  · rw [cupV_eq l h11 X, cupV_eq l h11 Y]
    have key : (cupQ l h11 X h).compr₂ (pb l f r) = (cupQ l h11 Y h).compl₁₂ (pb l f n) (pb l f m) := by
      apply LateralTheory.EtaleTrace.LRingPf.ext2; intro x y
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
      rw [cupQ_tmul, pb_tmul, pb_tmul, pb_tmul, cupQ_tmul]
      congr 1
      exact Subtype.ext (funext fun j => pull_cc h h6n (sch.map f) (x.1 j) (y.1 j))
    exact LinearMap.congr_fun₂ key u v
  · exact ⟨z0 l h11 X hl, fun j => rfl, oneV_eq l h11 X hl⟩
  · rw [hcomm X n 0 n (add_zero n) (zero_add n) u (oneV l X), hone X hl n u, mul_zero,
      Int.negOnePow_zero, one_smul]
  · rw [oneV_eq l h11 X hl, oneV_eq l h11 Y (unit_pull l f hl), pb_tmul]
    congr 1
    exact Subtype.ext (funext fun j => (h6n (l ^ j)).2.1 (sch.map f) (inv_of l X hl j))
  · simp only [cupV_eq l h11]
    have key : ∀ z, (cupQ l h11 X h1).compr₂ ((cupQ l h11 X h2).flip z) =
        (cupQ l h11 X h4).compl₂ ((cupQ l h11 X h3).flip z) := by
      intro z; apply LateralTheory.EtaleTrace.LRingPf.ext2; intro x y
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.flip_apply]
      rw [cupQ_tmul]
      have k2 : cupQ l h11 X h2 ((1 : ℚ_[l]) ⊗ₜ cupL l (sch.obj X) h1 h11 x y) =
          (cupQ l h11 X h4 ((1 : ℚ_[l]) ⊗ₜ x)).comp (cupQ l h11 X h3 ((1 : ℚ_[l]) ⊗ₜ y)) := by
        apply ext1; intro w
        rw [LinearMap.comp_apply, cupQ_tmul, cupQ_tmul, cupQ_tmul]
        congr 1
        exact Subtype.ext (funext fun j => assoc_cc h6r h1 h2 h3 h4 (x.1 j) (y.1 j) (w.1 j))
      exact LinearMap.congr_fun k2 z
    exact LinearMap.congr_fun₂ (key z) u v

end UpperTheory.Gal.KunnethLefschetz
