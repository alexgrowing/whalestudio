import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.ArtinElem

variable {K K' : Type*} [CommRing K] [CommRing K'] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [DecidableEq M] {F : M → Type*} [∀ m, CommRing (F m)]

noncomputable def coord (e : K ≃+* ∀ m, F m) (m : M) : K →+* F m :=
  (Pi.evalRingHom F m).comp e.toRingHom

noncomputable def liftT (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    TransvectionStruct ι K :=
  ⟨t.i, t.j, t.hij, e.symm (Pi.single m t.c)⟩

lemma coord_symm_single (e : K ≃+* ∀ m, F m) (m m' : M) (c : F m) :
    coord e m' (e.symm (Pi.single m c)) = (Pi.single m c : ∀ m, F m) m' := by
  simp [coord]

lemma mapMatrix_single (f : K →+* K') (a b : ι) (c : K) :
    f.mapMatrix (single a b c) = single a b (f c) := by
  ext x y
  simp only [RingHom.mapMatrix_apply, map_apply, single_apply]
  split_ifs <;> simp

lemma liftT_toMatrix (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    (liftT e m t).toMatrix = 1 + single t.i t.j (e.symm (Pi.single m t.c)) := rfl

lemma mapMatrix_liftT_same (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    (coord e m).mapMatrix (liftT e m t).toMatrix = t.toMatrix := by
  rw [liftT_toMatrix, map_add, map_one, mapMatrix_single, coord_symm_single, Pi.single_eq_same]
  rfl

lemma mapMatrix_liftT_ne (e : K ≃+* ∀ m, F m) {m m' : M} (h : m' ≠ m)
    (t : TransvectionStruct ι (F m)) :
    (coord e m').mapMatrix (liftT e m t).toMatrix = 1 := by
  rw [liftT_toMatrix, map_add, map_one, mapMatrix_single, coord_symm_single,
    Pi.single_eq_of_ne h, single_zero, add_zero]

lemma mapMatrix_prod_same (e : K ≃+* ∀ m, F m) (m : M) (T : List (TransvectionStruct ι (F m))) :
    (coord e m).mapMatrix (((T.map (liftT e m)).map TransvectionStruct.toMatrix).prod) =
      (T.map TransvectionStruct.toMatrix).prod := by
  induction T with
  | nil => simp
  | cons t T ih => simp only [List.map_cons, List.prod_cons, map_mul, ih, mapMatrix_liftT_same]

lemma mapMatrix_prod_ne (e : K ≃+* ∀ m, F m) {m m' : M} (h : m' ≠ m)
    (T : List (TransvectionStruct ι (F m))) :
    (coord e m').mapMatrix (((T.map (liftT e m)).map TransvectionStruct.toMatrix).prod) = 1 := by
  induction T with
  | nil => simp
  | cons t T ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih, mapMatrix_liftT_ne e h, mul_one]

noncomputable def big (e : K ≃+* ∀ m, F m) (T : ∀ m, List (TransvectionStruct ι (F m))) (l : List M) :
    List (TransvectionStruct ι K) :=
  l.flatMap fun m => (T m).map (liftT e m)

lemma mapMatrix_big (e : K ≃+* ∀ m, F m) (T : ∀ m, List (TransvectionStruct ι (F m)))
    (m' : M) (l : List M) (hl : l.Nodup) :
    (coord e m').mapMatrix (((big e T l).map TransvectionStruct.toMatrix).prod) =
      if m' ∈ l then ((T m').map TransvectionStruct.toMatrix).prod else 1 := by
  induction l with
  | nil => simp [big]
  | cons m l ih =>
    have ih' := ih (List.nodup_cons.mp hl).2
    have hm : m ∉ l := (List.nodup_cons.mp hl).1
    have hb : big e T (m :: l) = (T m).map (liftT e m) ++ big e T l := by simp [big]
    rw [hb, List.map_append, List.prod_append, map_mul, ih']
    by_cases h : m' = m
    · subst h
      rw [mapMatrix_prod_same]
      simp [hm]
    · rw [mapMatrix_prod_ne e h, one_mul]
      simp [h]

lemma matrix_ext_coord (e : K ≃+* ∀ m, F m) {A B : Matrix ι ι K}
    (h : ∀ m, (coord e m).mapMatrix A = (coord e m).mapMatrix B) : A = B := by
  ext a b
  apply e.injective
  funext m
  have := congrFun (congrFun (h m) a) b
  simpa [coord] using this

theorem factor_of_pi [Fintype M] (e : K ≃+* ∀ m, F m)
    (hF : ∀ (m : M) (A : Matrix ι ι (F m)),
      ∃ (L L' : List (TransvectionStruct ι (F m))) (D : ι → F m),
        A = (L.map TransvectionStruct.toMatrix).prod * diagonal D *
          (L'.map TransvectionStruct.toMatrix).prod)
    (A : Matrix ι ι K) :
    ∃ (L L' : List (TransvectionStruct ι K)) (D : ι → K),
      A = (L.map TransvectionStruct.toMatrix).prod * diagonal D *
        (L'.map TransvectionStruct.toMatrix).prod := by
  choose L L' D hD using fun m => hF m ((coord e m).mapMatrix A)
  refine ⟨big e L Finset.univ.toList, big e L' Finset.univ.toList,
    fun i => e.symm (fun m => D m i), matrix_ext_coord e fun m => ?_⟩
  have hnd := Finset.nodup_toList (Finset.univ : Finset M)
  have hdiag : (coord e m).mapMatrix (diagonal fun i => e.symm (fun m => D m i)) =
      diagonal (D m) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [coord]
    · simp [hab]
  rw [map_mul, map_mul, mapMatrix_big e L m _ hnd, mapMatrix_big e L' m _ hnd, hdiag]
  simpa using hD m

end GlobalTheory.CompanionTheory.SW.ArtinElem

namespace GlobalTheory.CompanionTheory.SW

theorem artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec
    (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) :
    ∃ (L L' : List (Matrix.TransvectionStruct ι K)) (D : ι → K),
      A = (L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D *
        (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
  classical
  letI : Fintype (MaximalSpectrum K) := Fintype.ofFinite _
  refine ArtinElem.factor_of_pi (F := fun m : MaximalSpectrum K => K ⧸ m.asIdeal)
    (IsArtinianRing.equivPi K).toRingEquiv (fun m B => ?_) A
  letI : Field (K ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec B

end GlobalTheory.CompanionTheory.SW
