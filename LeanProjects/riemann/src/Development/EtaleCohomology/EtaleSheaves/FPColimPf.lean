import Development.EtaleCohomology.EtaleSheaves.CompPf

noncomputable section
open CategoryTheory Limits MvPolynomial

namespace LateralTheory.E.FPColimPf

attribute [local instance] Classical.propDecidable

def FP (X : CommRingCat.{0}) : ObjectProperty (Under X) := fun S => S.hom.hom.FinitePresentation

def FPColim : Prop := ∀ (X : CommRingCat.{0}) (S : Under X),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J), (FP X).colimitsOfShape J S

section Alg
variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]

structure Idx where
  s : Finset A
  T : Finset (MvPolynomial A R)
  hT : ∀ t ∈ T, aeval (R := R) (fun a : A => a) t = 0
  hv : ∀ t ∈ T, t.vars ⊆ s

variable {R A}

instance : Preorder (Idx R A) := Preorder.lift (fun i => (i.s, i.T))

theorem Idx.le_iff {i j : Idx R A} : i ≤ j ↔ i.s ⊆ j.s ∧ i.T ⊆ j.T := Iff.rfl

def Idx.join (i j : Idx R A) : Idx R A where
  s := i.s ∪ j.s
  T := i.T ∪ j.T
  hT t ht := by
    rcases Finset.mem_union.1 ht with h | h
    · exact i.hT t h
    · exact j.hT t h
  hv t ht := by
    rcases Finset.mem_union.1 ht with h | h
    · exact (i.hv t h).trans Finset.subset_union_left
    · exact (j.hv t h).trans Finset.subset_union_right

instance : IsDirected (Idx R A) (· ≤ ·) :=
  ⟨fun i j => ⟨i.join j, ⟨Finset.subset_union_left, Finset.subset_union_left⟩,
    ⟨Finset.subset_union_right, Finset.subset_union_right⟩⟩⟩

instance : Nonempty (Idx R A) := ⟨⟨∅, ∅, by simp, by simp⟩⟩

example : IsFiltered (Idx R A) := inferInstance

def rel (i : Idx R A) : Ideal (MvPolynomial i.s R) :=
  Ideal.comap (rename (R := R) (Subtype.val : i.s → A)) (Ideal.span (i.T : Set (MvPolynomial A R)))

abbrev D (i : Idx R A) := MvPolynomial i.s R ⧸ rel i

def retr (i : Idx R A) : MvPolynomial A R →ₐ[R] MvPolynomial i.s R :=
  aeval (fun a => if h : a ∈ i.s then X ⟨a, h⟩ else 0)

theorem retr_rename (i : Idx R A) (p : MvPolynomial i.s R) : retr i (rename Subtype.val p) = p := by
  rw [retr, aeval_rename]
  conv_rhs => rw [← aeval_X_left_apply (R := R) p]
  congr 1
  ext x
  simp

theorem rename_retr (i : Idx R A) (t : MvPolynomial A R) (ht : t.vars ⊆ i.s) :
    rename Subtype.val (retr i t) = t := by
  obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range t (Subtype.val : i.s → A)
    Subtype.val_injective (fun x hx => ⟨⟨x, ht hx⟩, rfl⟩)
  rw [retr_rename]

theorem rel_fg (i : Idx R A) : (rel i).FG := by
  have : rel i = Ideal.map (retr i) (Ideal.span (i.T : Set (MvPolynomial A R))) := by
    apply le_antisymm
    · intro p hp
      rw [← retr_rename i p]
      exact Ideal.mem_map_of_mem _ hp
    · rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
      intro t ht
      rw [SetLike.mem_coe, Ideal.mem_comap, rel, Ideal.mem_comap, rename_retr i t (i.hv t ht)]
      exact Ideal.subset_span ht
  rw [this]
  exact Ideal.FG.map ⟨i.T, rfl⟩ _

instance (i : Idx R A) : Algebra.FinitePresentation R (D i) :=
  Algebra.FinitePresentation.quotient (rel_fg i)

def trans (i j : Idx R A) (h : i ≤ j) : D i →ₐ[R] D j :=
  Ideal.quotientMapₐ (rel j) (rename (fun x : i.s => (⟨x.1, h.1 x.2⟩ : j.s))) (by
    intro p hp
    rw [rel, Ideal.mem_comap, Ideal.mem_comap, rename_rename]
    exact Ideal.span_mono (Finset.coe_subset.2 h.2) hp)

def toA (i : Idx R A) : D i →ₐ[R] A :=
  Ideal.Quotient.liftₐ (rel i) (aeval (fun x : i.s => (x : A))) (by
    intro p hp
    have h0 : aeval (R := R) (fun a : A => a) (rename Subtype.val p) = 0 := by
      refine (Submodule.span_le (p := RingHom.ker (aeval (R := R) (fun a : A => a)))).2 ?_ hp
      intro t ht
      exact i.hT t ht
    rwa [aeval_rename] at h0)

@[simp] theorem trans_mk (i j : Idx R A) (h : i ≤ j) (p) :
    trans i j h (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename (fun x : i.s => (⟨x.1, h.1 x.2⟩ : j.s)) p) := rfl

@[simp] theorem toA_mk (i : Idx R A) (p) :
    toA i (Ideal.Quotient.mk _ p) = aeval (fun x : i.s => (x : A)) p := rfl

theorem trans_id (i : Idx R A) : trans i i le_rfl = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro x; simp [Ideal.Quotient.mkₐ_eq_mk]

theorem trans_comp (i j k : Idx R A) (h₁ : i ≤ j) (h₂ : j ≤ k) :
    trans i k (h₁.trans h₂) = (trans j k h₂).comp (trans i j h₁) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro x; simp [Ideal.Quotient.mkₐ_eq_mk]

theorem toA_trans (i j : Idx R A) (h : i ≤ j) : (toA j).comp (trans i j h) = toA i := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro x; simp [Ideal.Quotient.mkₐ_eq_mk]

end Alg

section Cat
variable (X : CommRingCat.{0}) (A : Type) [CommRing A] [Algebra X A]

abbrev mkU (B : Type) [CommRing B] [Algebra X B] : Under X := Under.mk (CommRingCat.ofHom (algebraMap X B))

variable {X}

def uHom {B C : Type} [CommRing B] [Algebra X B] [CommRing C] [Algebra X C] (φ : B →ₐ[X] C) :
    mkU X B ⟶ mkU X C :=
  Under.homMk (CommRingCat.ofHom φ.toRingHom) (by ext x; simp)

theorem uHom_id {B : Type} [CommRing B] [Algebra X B] : uHom (AlgHom.id X B) = 𝟙 _ := by
  ext; rfl

theorem uHom_comp {B C E : Type} [CommRing B] [Algebra X B] [CommRing C] [Algebra X C] [CommRing E] [Algebra X E]
    (φ : B →ₐ[X] C) (ψ : C →ₐ[X] E) : uHom (ψ.comp φ) = uHom φ ≫ uHom ψ := by
  ext; rfl

def diag : Idx X A ⥤ Under X where
  obj i := mkU X (D i)
  map {i j} f := uHom (trans i j f.le)
  map_id i := by rw [trans_id]; exact uHom_id
  map_comp {i j k} f g := by rw [trans_comp i j k f.le g.le]; exact uHom_comp _ _

def cocone : Cocone (diag (X := X) A) where
  pt := mkU X A
  ι := { app := fun i => uHom (toA i)
         naturality := fun i j f => by
           simp only [Functor.const_obj_obj, Functor.const_obj_map]
           show uHom (trans i j f.le) ≫ uHom (toA j) = uHom (toA i)
           rw [← uHom_comp, toA_trans] }

theorem cocone_app (i : Idx X A) (x : D i) :
    ((Under.forget X ⋙ forget CommRingCat).mapCocone (cocone A)).ι.app i x = toA i x := rfl

def isColimitCocone : IsColimit (cocone (X := X) A) := by
  have : ReflectsColimitsOfShape (Idx X A) (Under.forget X ⋙ forget CommRingCat) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (Under.forget X ⋙ forget CommRingCat) ?_
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (a : A)
    refine ⟨⟨{a}, ∅, by simp, by simp⟩, Ideal.Quotient.mk _ (MvPolynomial.X ⟨a, Finset.mem_singleton_self a⟩), ?_⟩
    show a = aeval _ (MvPolynomial.X _)
    rw [aeval_X]
  · intro i j (xi : D i) (xj : D j) hx
    change toA i xi = toA j xj at hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective xi
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective xj
    rw [toA_mk, toA_mk] at hx
    set r : MvPolynomial A X := rename Subtype.val p - rename Subtype.val q with hr
    have hr0 : aeval (R := X) (fun a : A => a) r = 0 := by
      rw [hr, map_sub, aeval_rename, aeval_rename]
      exact sub_eq_zero.2 hx
    let k : Idx X A := ⟨i.s ∪ j.s ∪ r.vars, i.T ∪ j.T ∪ {r}, by
        intro t ht
        simp only [Finset.mem_union, Finset.mem_singleton] at ht
        rcases ht with (h | h) | rfl
        · exact i.hT t h
        · exact j.hT t h
        · exact hr0, by
        intro t ht
        simp only [Finset.mem_union, Finset.mem_singleton] at ht
        rcases ht with (h | h) | rfl
        · exact (i.hv t h).trans (Finset.subset_union_left.trans Finset.subset_union_left)
        · exact (j.hv t h).trans (Finset.subset_union_right.trans Finset.subset_union_left)
        · exact Finset.subset_union_right⟩
    have hi : i ≤ k := ⟨Finset.subset_union_left.trans Finset.subset_union_left,
      Finset.subset_union_left.trans Finset.subset_union_left⟩
    have hj : j ≤ k := ⟨Finset.subset_union_right.trans Finset.subset_union_left,
      Finset.subset_union_right.trans Finset.subset_union_left⟩
    refine ⟨k, homOfLE hi, homOfLE hj, ?_⟩
    show trans i k hi (Ideal.Quotient.mk _ p) = trans j k hj (Ideal.Quotient.mk _ q)
    rw [trans_mk, trans_mk, Ideal.Quotient.eq, rel, Ideal.mem_comap, map_sub, rename_rename, rename_rename]
    apply Ideal.subset_span
    show r ∈ ((i.T ∪ j.T ∪ {r} : Finset _) : Set (MvPolynomial A X))
    exact Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_singleton_self _))

theorem fp_diag (i : Idx X A) : FP X ((diag (X := X) A).obj i) :=
  show (algebraMap X (D i)).FinitePresentation from RingHom.finitePresentation_algebraMap.2 inferInstance

theorem colim_mkU : (FP X).colimitsOfShape (Idx X A) (mkU X A) :=
  ⟨{ diag := diag A, ι := (cocone A).ι, isColimit := isColimitCocone A, prop_diag_obj := fp_diag A }⟩

end Cat

theorem FPColim_of : FPColim := by
  intro X S
  let _ : Algebra X S.right := S.hom.hom.toAlgebra
  exact ⟨Idx X S.right, inferInstance, inferInstance, colim_mkU S.right⟩

end LateralTheory.E.FPColimPf
