import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AutomorphicArithmetic.CommutativeAlgebra.MemPullbackImageIffFactorsThroughOpen
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem leib {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (W : Scheme.{0})
    (s s' t w w' : ℤ) (h : s + t = w) (h' : s' + t = w') (hs : s' = s + 1)
    (a : Sec (I.X s) W) (b : Sec (J.X t) W) (hb : Sec.map (J.d t (t + 1)) b = 0) :
    Sec.map (K.d w w') (μ.mul W s t w h a b) = μ.mul W s' t w' h' (Sec.map (I.d s s') a) b := by
  subst hs
  obtain rfl : w' = w + 1 := by omega
  rw [μ.leibniz W s t w h a b, hb, map_zero, smul_zero, add_zero]

private theorem res_usmul {R : Type} [CommRing R] {F : Shv R} {V W : Scheme.{0}} (g : V ⟶ W)
    (u : ℤˣ) (x : Sec F W) : Sec.res g (u • x) = u • Sec.res g x := by
  simp only [Sec.res, Units.smul_def, map_zsmul]

private theorem map_usmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {W : Scheme.{0}}
    (u : ℤˣ) (x : Sec F W) : Sec.map φ (u • x) = u • Sec.map φ x := by
  simp only [Sec.map, Units.smul_def, map_zsmul]

private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {V W X : Scheme.{0}} (g : V ⟶ W)
    (f : W ⟶ X) (x : Sec F X) : Sec.res (g ≫ f) x = Sec.res g (Sec.res f x) := by
  simp only [Sec.res, op_comp, Functor.map_comp]
  rfl

private theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V W : Scheme.{0}}
    (g : V ⟶ W) (x : Sec F W) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  ConcreteCategory.congr_hom (φ.hom.naturality g.op) x

private noncomputable def prodFam {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K)
    {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X)
    (hU : Sec.res U.ι β = 0) (p : ℕ) (s : ℤ) :
    Fam (Sub.bot E) p (I.X (s + 0)) →+
      Fam (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) p (K.X (s + m)) where
  toFun a := ⟨fun W z => (m * (p : ℕ)).negOnePow •
      μ.mul W (s + 0) m (s + m) (by omega) (a.1 W z) (Sec.res (under π z) β), fun V W g z => by
      beta_reduce
      rw [res_usmul, μ.nat, a.2.1 V W g z, (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).2.1 V g, res_comp],
    fun W z h => by
      obtain ⟨w, hw⟩ := (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).1.1 h
      beta_reduce
      rw [← hw, res_comp, hU]
      simp⟩
  map_zero' := by ext W z; simp
  map_add' a b := by ext W z; simp

theorem UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open :
    ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X), Sec.map (J.d m (m + 1)) β = 0 → Sec.res U.ι β = 0 →
    ∃ Φ : (famDC (Sub.bot E) I 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) K m), IsProd μ π β Φ ∧ Φ.Ok := by
  intro R _ I J K μ X U E π m β hd hU
  refine ⟨fun p s => prodFam μ U π m β hU p s, fun p s a W z => rfl, ?_, ?_⟩
  · intro p s a
    refine Subtype.ext (funext fun W => funext fun z => ?_)
    change (m * (p : ℕ)).negOnePow • μ.mul W (s + 1 + 0) m (s + 1 + m) (by omega)
        (Sec.map (I.d (s + 0) (s + 1 + 0)) (a.1 W z)) (Sec.res (under π z) β) =
      Sec.map (K.d (s + m) (s + 1 + m)) ((m * (p : ℕ)).negOnePow •
        μ.mul W (s + 0) m (s + m) (by omega) (a.1 W z) (Sec.res (under π z) β))
    rw [map_usmul, leib μ W (s + 0) (s + 1 + 0) m (s + m) (s + 1 + m) (by omega) (by omega) (by omega)
      _ _ (by rw [map_res, hd]; simp)]
  · intro p s a
    refine Subtype.ext (funext fun W => funext fun z => ?_)
    have hf : ∀ i : Fin (p + 2), under π (z.face i) = under π z := fun i =>
      (UpperTheory.mem_pullbackImage_iff_factors_through_open U π (p + 1) W z).2.2 p (SimplexCategory.δ i)
    change ((m * ((p + 1 : ℕ) : ℤ))).negOnePow • μ.mul W (s + 0) m (s + m) (by omega)
        ((0 : ℤ).negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • a.1 W (z.face i)) (Sec.res (under π z) β) =
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ((m * (p : ℕ)).negOnePow •
        μ.mul W (s + 0) m (s + m) (by omega) (a.1 W (z.face i)) (Sec.res (under π (z.face i)) β))
    simp only [hf]
    have hsign : (m * ((p + 1 : ℕ) : ℤ)).negOnePow = m.negOnePow * (m * (p : ℕ)).negOnePow := by
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_comm, Int.negOnePow_add]
    generalize Sec.res (under π z) β = b
    let f := ((μ.mul W (s + 0) m (s + m) (by omega)).flip b).toAddMonoidHom
    change _ • f _ = _ • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (_ • f _)
    have e : ∀ (u : ℤˣ) (i : Fin (p + 2)) (y : Sec (K.X (s + m)) W),
        (-1 : ℤ) ^ (i : ℕ) • (u • y) = u • ((-1 : ℤ) ^ (i : ℕ) • y) := by
      intro u i y
      simp only [Units.smul_def]
      exact smul_comm _ _ _
    simp only [e]
    rw [← Finset.smul_sum, hsign, mul_smul, Int.negOnePow_zero, one_smul, map_sum]
    simp only [map_zsmul]
