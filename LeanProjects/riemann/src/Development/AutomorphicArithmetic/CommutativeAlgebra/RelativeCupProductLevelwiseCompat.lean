import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AutomorphicArithmetic.CommutativeAlgebra.ColumnExactZeroOfTotalExactOfVerticalZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.MemPullbackImageIffFactorsThroughOpen
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem units_map_smul {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (η : ℤˣ) (x : A) :
    f (η • x) = η • f x := by
  simp [Units.smul_def]

private theorem colEx_transfer {C C' D D' : DC} (Φ : C.Hom C') (Ψ : D.Hom D') (p : ℕ) (η : ℤˣ)
    (e : ∀ s, C.A p s ≃+ D.A 0 s) (e' : ∀ s, C'.A p s ≃+ D'.A 0 s)
    (hd : ∀ s t x, e t (C.d p s t x) = D.d 0 s t (e s x))
    (hd' : ∀ s t x, e' t (C'.d p s t x) = D'.d 0 s t (e' s x))
    (hΦ : ∀ s x, e' s (Φ p s x) = η • Ψ 0 s (e s x)) (h : Ψ.ColEx 0) : Φ.ColEx p := by
  have hηη : ∀ {A : Type 1} [AddCommGroup A] (x : A), η • η • x = x := fun x => by
    rw [smul_smul, Int.units_mul_self, one_smul]
  intro s a y ha hy
  have hΨ : ∀ s x, Ψ 0 s (e s x) = η • e' s (Φ p s x) := fun s x => by rw [hΦ, hηη]
  obtain ⟨a', y', h1, h2⟩ := h s (e _ a) (η • e' s y)
    (by rw [← hd, ha, map_zero])
    (by rw [hΨ, hy, hd', units_map_smul])
  refine ⟨(e s).symm a', η • (e' _).symm y', ?_, ?_⟩
  · apply (e _).injective
    rw [hd, AddEquiv.apply_symm_apply, h1]
  · apply (e' _).injective
    have h3 : e' s y = η • (Ψ 0 s a' + D'.d 0 (s - 1) s y') := by rw [← h2, hηη]
    have h4 : e' (s - 1) (η • (e' (s - 1)).symm y') = η • y' := by
      have := units_map_smul (e' (s - 1)).toAddMonoidHom η ((e' (s - 1)).symm y')
      simpa using this
    rw [h3, map_add, hΦ, hd', AddEquiv.apply_symm_apply, h4, units_map_smul, smul_add]

private def lvl {R : Type} [CommRing R] {E : Spc} {p : ℕ} (Z : Sub E)
    (Z' : Sub (disc.obj (E.obj (op (SimplexCategory.mk p)))))
    (h : ∀ (W : Scheme.{0}) (z : Sx E p W), Z'.mem 0 W z ↔ Z.mem p W z) (M : Shv R) :
    Fam Z p M ≃+ Fam Z' 0 M where
  toFun a := ⟨a.1, a.2.1, fun U x hx => a.2.2 U x ((h U x).1 hx)⟩
  invFun a := ⟨a.1, a.2.1, fun U x hx => a.2.2 U x ((h U x).2 hx)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem disc_δ {R : Type} [CommRing R] {F : PSh} (Z : Sub (disc.obj F)) (L : Cx R) (m s : ℤ)
    (x : (famDC Z L m).A 0 s) : (famDC Z L m).δ 0 s x = 0 := by
  apply Subtype.ext
  funext U z
  have hf : ∀ i, Sx.face (E := disc.obj F) z i = z := fun _ => rfl
  change m.negOnePow • ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (show Fam Z 0 (L.X (s + m)) from x).1 U (Sx.face (E := disc.obj F) z i) = 0
  simp [Fin.sum_univ_two, hf]

private theorem fam_smul {R : Type} [CommRing R] {E : Spc} (Z : Sub E) (p : ℕ) (M : Shv R) (η : ℤˣ) (a : Fam Z p M)
    (W : Scheme.{0}) (z : Sx E p W) : (η • a).1 W z = η • a.1 W z := by
  rcases Int.units_eq_one_or η with rfl | rfl <;> simp

theorem UpperTheory.relativeCupProduct_levelwise_compat :
    ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X) (p : ℕ)
    (Φ : (famDC (Sub.bot E) I 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) K m))
    (Ψ : (famDC (Sub.bot (disc.obj (E.obj (op (SimplexCategory.mk p))))) I 0).Hom (famDC (Sub.img (E := disc.obj (E.obj (op (SimplexCategory.mk p)))) (pullback.fst (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) (sch.map U.ι))) K m)),
    IsProd μ π β Φ → IsProd μ (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) β Ψ → Ψ.TotEx → Φ.ColEx p := by
  intro R _ I J K μ X U E π m β p Φ Ψ hΦ hΨ hT
  have h0 : Ψ.ColEx 0 := UpperTheory.columnExact_zero_of_totalExact_of_vertical_zero _ _ Ψ (disc_δ _ _ _) (disc_δ _ _ _) hT
  have hbot : ∀ (W : Scheme.{0}) (z : Sx E p W),
      (Sub.bot (disc.obj (E.obj (op (SimplexCategory.mk p))))).mem 0 W z ↔ (Sub.bot E).mem p W z :=
    fun _ _ => Iff.rfl
  have himg : ∀ (W : Scheme.{0}) (z : Sx E p W),
      (Sub.img (E := disc.obj (E.obj (op (SimplexCategory.mk p)))) (pullback.fst (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) (sch.map U.ι))).mem 0 W z ↔
        (Sub.img (E := E) (pullback.fst π (sch.map U.ι))).mem p W z := fun W z =>
    ((UpperTheory.mem_pullbackImage_iff_factors_through_open U (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) 0 W z).1).trans
      ((UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).1).symm
  refine colEx_transfer Φ Ψ p (m * (p : ℤ)).negOnePow (fun s => lvl _ _ hbot _) (fun s => lvl _ _ himg _)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) ?_ h0
  intro s x
  apply Subtype.ext
  funext W z
  have h1 := hΦ p s x W z
  have h2 := hΨ 0 s (lvl _ _ hbot _ x) W z
  refine Eq.trans h1 (Eq.trans ?_ (fam_smul _ _ _ (m * (p : ℤ)).negOnePow (Ψ 0 s (lvl _ _ hbot _ x)) W z).symm)
  refine congrArg _ (Eq.trans ?_ h2.symm)
  have h0' : (m * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
  rw [h0', one_smul]
  rfl
