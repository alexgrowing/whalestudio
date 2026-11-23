import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebra
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChart
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebraSpecSmooth
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebraStandardSmooth
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceGlobalSections
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def polynomialOfSection (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (j : Fin q) : MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k :=
  (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm (F j)

theorem mvPolynomialEquivGlobalSections_polynomialOfSection (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (j : Fin q) :
    mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n)) (polynomialOfSection k M n q F j) = F j :=
  (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).apply_symm_apply (F j)

def sumVariableMap (M n q : ℕ) (s : Fin q → Fin n) :
    ULift.{u, 0} (Fin M ⊕ Fin q) → ULift.{u, 0} (Fin M ⊕ Fin n) :=
  fun i =>
    ULift.up (Sum.elim (fun a : Fin M => Sum.inl a) (fun j : Fin q => Sum.inr (s j)) i.down)

theorem sumVariableMap_injective (M n q : ℕ) (s : Fin q → Fin n) (hs : Function.Injective s) :
    Function.Injective (sumVariableMap.{u} M n q s) := by
  rintro ⟨x⟩ ⟨y⟩ h
  have h' : Sum.elim (fun a : Fin M => Sum.inl a) (fun j : Fin q => Sum.inr (s j)) x
      = Sum.elim (fun a : Fin M => Sum.inl a) (fun j : Fin q => Sum.inr (s j)) y :=
    congrArg ULift.down h
  have hxy : x = y := by
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        have hab : a = b := by simpa using h'
        exact congrArg Sum.inl hab
      | inr j => simp at h'
    | inr i =>
      cases y with
      | inl b => simp at h'
      | inr j =>
        simp only [Sum.elim_inr, Sum.inr.injEq] at h'
        exact congrArg Sum.inr (hs h')
  exact congrArg ULift.up hxy

def jacobianMatrixOfSections (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Matrix (Fin q) (Fin q) (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k) :=
  Matrix.of fun i j =>
    (MvPolynomial.pderiv (ULift.up (Sum.inr (s i)) : ULift.{u, 0} (Fin M ⊕ Fin n)))
      (polynomialOfSection k M n q F j)

theorem jacobianMatrixOfSections_apply (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) (i j : Fin q) :
    jacobianMatrixOfSections k M n q F s i j =
      (MvPolynomial.pderiv (ULift.up (Sum.inr (s i)) : ULift.{u, 0} (Fin M ⊕ Fin n)))
        (polynomialOfSection k M n q F j) := rfl

def graphCoordinates (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤))) :
    ULift.{u, 0} (Fin M ⊕ Fin q) → MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k :=
  fun i =>
    Sum.elim
      (fun a : Fin M => MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n)))
      (fun j : Fin q => polynomialOfSection k M n q F j) i.down

theorem graphCoordinates_inl (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (a : Fin M) :
    graphCoordinates k M n q F (ULift.up (Sum.inl a)) =
      MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n)) := rfl

theorem graphCoordinates_inr (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (j : Fin q) :
    graphCoordinates k M n q F (ULift.up (Sum.inr j)) = polynomialOfSection k M n q F j := rfl

private theorem det_graphJacobianMinorMatrix_eq_det_jacobianMatrix (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)).det =
      (jacobianMatrixOfSections k M n q F s).det := by
  have hup : ∀ x y : Fin M ⊕ Fin n,
      (ULift.up x : ULift.{u, 0} (Fin M ⊕ Fin n)) = ULift.up y → x = y :=
    fun _ _ h => congrArg ULift.down h
  have hXne : ∀ i j : ULift.{u, 0} (Fin M ⊕ Fin n), i ≠ j →
      (MvPolynomial.pderiv i)
          (MvPolynomial.X j : MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k) = 0 := by
    intro i j h
    simp [MvPolynomial.pderiv_X, Ne.symm h]
  have key :
      (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)).submatrix
          ⇑(Equiv.ulift.symm : (Fin M ⊕ Fin q) ≃ ULift.{u, 0} (Fin M ⊕ Fin q))
          ⇑(Equiv.ulift.symm : (Fin M ⊕ Fin q) ≃ ULift.{u, 0} (Fin M ⊕ Fin q)) =
        Matrix.fromBlocks
          (1 : Matrix (Fin M) (Fin M) (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k))
          (Matrix.of fun (a : Fin M) (j : Fin q) =>
            (MvPolynomial.pderiv (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n)))
              (polynomialOfSection k M n q F j))
          0 (jacobianMatrixOfSections k M n q F s) := by
    apply Matrix.ext
    intro x y
    simp only [Matrix.submatrix_apply, graphJacobianMinorMatrix_apply]
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        show (MvPolynomial.pderiv (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n)))
              (MvPolynomial.X (ULift.up (Sum.inl b) : ULift.{u, 0} (Fin M ⊕ Fin n))) =
            (1 : Matrix (Fin M) (Fin M) (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k)) a b
        by_cases h : a = b
        · subst h
          rw [MvPolynomial.pderiv_X_self, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne h]
          exact hXne _ _ fun hc => h (Sum.inl_injective (hup _ _ hc))
      | inr j => rfl
    | inr i =>
      cases y with
      | inl b =>
        show (MvPolynomial.pderiv (ULift.up (Sum.inr (s i)) : ULift.{u, 0} (Fin M ⊕ Fin n)))
              (MvPolynomial.X (ULift.up (Sum.inl b) : ULift.{u, 0} (Fin M ⊕ Fin n))) = 0
        refine hXne _ _ ?_
        intro hc
        have hc' := hup _ _ hc
        simp at hc'
      | inr j => rfl
  have hdet := Matrix.det_submatrix_equiv_self
      (Equiv.ulift.symm : (Fin M ⊕ Fin q) ≃ ULift.{u, 0} (Fin M ⊕ Fin q))
      (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))
  rw [key, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul] at hdet
  exact hdet.symm

theorem graphJacobianMinorDet_graphCoordinates (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s) =
      graphAlgebraEquiv (graphCoordinates k M n q F) (jacobianMatrixOfSections k M n q F s).det := by
  have h := det_graphJacobianMinorMatrix_eq_det_jacobianMatrix k M n q F s
  show graphAlgebraEquiv (graphCoordinates k M n q F)
      (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)).det =
    graphAlgebraEquiv (graphCoordinates k M n q F) (jacobianMatrixOfSections k M n q F s).det
  rw [h]

def jacobianDetSection (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)) :=
  mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n)) (jacobianMatrixOfSections k M n q F s).det

def specGraphAwayToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))) ⟶
      Spec (CommRingCat.of (GraphAlgebra (graphCoordinates k M n q F))) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (GraphAlgebra (graphCoordinates k M n q F))
      (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))))

theorem isOpenImmersion_specGraphAwayToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (specGraphAwayToSpecGraphAlgebra k M n q F s) := by
  unfold specGraphAwayToSpecGraphAlgebra
  infer_instance

instance instIsOpenImmersionGraphAwaySpecHom (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (specGraphAwayToSpecGraphAlgebra k M n q F s) :=
  isOpenImmersion_specGraphAwayToSpecGraphAlgebra k M n q F s

def basicOpenToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).toScheme ⟶
      Spec (CommRingCat.of (GraphAlgebra (graphCoordinates k M n q F))) :=
  ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
      (jacobianDetSection k M n q F s)).ι ≫
    (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
      Spec.map (CommRingCat.ofHom
        ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))

private def specIsoOfRingEquiv {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of A) :=
  Scheme.Spec.mapIso e.toCommRingCatIso.op

private theorem isIso_spec_map_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
  refine ⟨(specIsoOfRingEquiv e).inv, ?_, ?_⟩
  · exact (specIsoOfRingEquiv e).hom_inv_id
  · exact (specIsoOfRingEquiv e).inv_hom_id

theorem isOpenImmersion_basicOpenToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (basicOpenToSpecGraphAlgebra k M n q F s) := by
  have : IsIso (Spec.map (CommRingCat.ofHom
      ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))) :=
    isIso_spec_map_ringEquiv ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv)
  unfold basicOpenToSpecGraphAlgebra
  infer_instance

instance instIsOpenImmersionGraphChartHom (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (basicOpenToSpecGraphAlgebra k M n q F s) :=
  isOpenImmersion_basicOpenToSpecGraphAlgebra k M n q F s

private theorem base_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X) :
    ⇑(f ≫ g).base x = ⇑g.base (⇑f.base x) := rfl

private theorem range_base_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Set.range ⇑(f ≫ g).base = ⇑g.base '' Set.range ⇑f.base := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⇑f.base x, ⟨x, rfl⟩, (base_comp_apply f g x).symm⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, base_comp_apply f g x⟩

private theorem image_base_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (S : Set ↥X) :
    ⇑(f ≫ g).base '' S = ⇑g.base '' (⇑f.base '' S) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⇑f.base x, ⟨x, hx, rfl⟩, (base_comp_apply f g x).symm⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, base_comp_apply f g x⟩

private theorem image_hom_preimage_eq {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    ⇑e.hom.base '' ((e.hom ⁻¹ᵁ U : X.Opens) : Set ↥X) = (U : Set ↥Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨⇑e.inv.base y, ?_, Scheme.inv_hom_apply e y⟩
    show ⇑e.hom.base (⇑e.inv.base y) ∈ (U : Set ↥Y)
    rw [Scheme.inv_hom_apply e y]
    exact hy

private theorem image_hom_eq_preimage_inv {X Y : Scheme.{u}} (e : X ≅ Y) (U : X.Opens) :
    ⇑e.hom.base '' ((U : X.Opens) : Set ↥X) = ((e.inv ⁻¹ᵁ U : Y.Opens) : Set ↥Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show ⇑e.inv.base (⇑e.hom.base x) ∈ ((U : X.Opens) : Set ↥X)
    rw [Scheme.hom_inv_apply e x]
    exact hx
  · intro hy
    exact ⟨⇑e.inv.base y, hy, Scheme.inv_hom_apply e y⟩

private theorem image_basicOpen_spec_map_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (a : A) :
    ⇑(Spec.map (CommRingCat.ofHom e.toRingHom)).base ''
        (PrimeSpectrum.basicOpen (e a) : Set (PrimeSpectrum B))
      = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
  have h2 : (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B))
      = (Spec (CommRingCat.of B)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a)) := by
    have h2' : (Spec (CommRingCat.of B)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a))
        = (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B)) :=
      basicOpen_eq_of_affine _
    exact h2'.symm
  have h3 : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ⁻¹ᵁ
        ((Spec (CommRingCat.of B)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a)))
      = (Spec (CommRingCat.of A)).basicOpen
          ((Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom e.symm.toRingHom)))
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a))) :=
    Scheme.preimage_basicOpen (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) _
  have h4 : (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom e.symm.toRingHom)))
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a))
      = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ((e.symm.toRingHom) (e a)) :=
    (RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e.symm.toRingHom))) (e a)).symm
  have h5 : (e.symm.toRingHom) (e a) = a := by simp
  have h6 : (Spec (CommRingCat.of A)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)
      = (PrimeSpectrum.basicOpen a : Opens (PrimeSpectrum A)) :=
    basicOpen_eq_of_affine _
  have hop : (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B)))
      = (PrimeSpectrum.basicOpen a : Opens (PrimeSpectrum A)) := by
    rw [h2, h3, h4, h5]
    exact h6
  have h1 : ⇑(Spec.map (CommRingCat.ofHom e.toRingHom)).base ''
        (PrimeSpectrum.basicOpen (e a) : Set (PrimeSpectrum B))
      = ((Spec.map (CommRingCat.ofHom e.symm.toRingHom) ⁻¹ᵁ
          (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B))) :
          Set ↥(Spec (CommRingCat.of A))) :=
    image_hom_eq_preimage_inv (specIsoOfRingEquiv e) (PrimeSpectrum.basicOpen (e a))
  exact h1.trans (congrArg (fun U : (Spec (CommRingCat.of A)).Opens =>
    (U : Set ↥(Spec (CommRingCat.of A)))) hop)

theorem range_specGraphAwayToSpecGraphAlgebra_eq (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Set.range ⇑(specGraphAwayToSpecGraphAlgebra k M n q F s).base =
      Set.range ⇑(basicOpenToSpecGraphAlgebra k M n q F s).base := by
  have hL : Set.range ⇑(specGraphAwayToSpecGraphAlgebra k M n q F s).base =
      (PrimeSpectrum.basicOpen
          (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) :
        Set (PrimeSpectrum (GraphAlgebra (graphCoordinates k M n q F)))) :=
    range_specMap_algebraMap_graphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)
  have hR1 : Set.range ⇑(basicOpenToSpecGraphAlgebra k M n q F s).base
      = ⇑((affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
            Spec.map (CommRingCat.ofHom
              ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))).base ''
          Set.range ⇑(((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s)).ι).base :=
    range_base_comp
      (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).ι)
      ((affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
        Spec.map (CommRingCat.ofHom
          ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom)))
  have hD : Set.range ⇑(((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).ι).base
      = (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s) :
          (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
          Set ↥(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n)))) :=
    Scheme.Opens.range_ι _
  have hDopen : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)
      = (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ⁻¹ᵁ
          (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det) :=
    mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum k (ULift.{u, 0} (Fin M ⊕ Fin n))
      (jacobianMatrixOfSections k M n q F s).det
  have himg1 : ⇑(affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom.base ''
        (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s) :
          (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
          Set ↥(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))))
      = (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det :
          Set (PrimeSpectrum (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k))) := by
    rw [hDopen]
    exact image_hom_preimage_eq (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n)))
      (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det)
  have hdet : (jacobianMatrixOfSections k M n q F s).det
      = ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv)
          (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) := by
    rw [graphJacobianMinorDet_graphCoordinates]
    simp
  have himg2 : ⇑(Spec.map (CommRingCat.ofHom
        ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))).base ''
        (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det :
          Set (PrimeSpectrum (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k)))
      = (PrimeSpectrum.basicOpen
            (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) :
          Set (PrimeSpectrum (GraphAlgebra (graphCoordinates k M n q F)))) := by
    rw [hdet]
    exact image_basicOpen_spec_map_ringEquiv ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv)
      (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))
  have hrange : Set.range ⇑(basicOpenToSpecGraphAlgebra k M n q F s).base
      = (PrimeSpectrum.basicOpen
            (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) :
          Set (PrimeSpectrum (GraphAlgebra (graphCoordinates k M n q F)))) := by
    rw [hR1, hD, image_base_comp, himg1]
    exact himg2
  exact hL.trans hrange.symm

def specGraphAwayIsoBasicOpen (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))) ≅
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).toScheme :=
  IsOpenImmersion.isoOfRangeEq (specGraphAwayToSpecGraphAlgebra k M n q F s) (basicOpenToSpecGraphAlgebra k M n q F s)
    (range_specGraphAwayToSpecGraphAlgebra_eq k M n q F s)

theorem specGraphAwayIsoBasicOpen_inv_comp (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToSpecGraphAlgebra k M n q F s =
      basicOpenToSpecGraphAlgebra k M n q F s := by
  exact IsOpenImmersion.isoOfRangeEq_inv_fac (specGraphAwayToSpecGraphAlgebra k M n q F s)
    (basicOpenToSpecGraphAlgebra k M n q F s) (range_specGraphAwayToSpecGraphAlgebra_eq k M n q F s)

def specGraphAwayToAffineSpace (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))) ⟶
      Spec (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
      (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))))

private theorem graphAlgebraEquiv_symm_comp_algebraMap_X (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (i : ULift.{u, 0} (Fin M ⊕ Fin q)) :
    (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
        (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
          (GraphAlgebra (graphCoordinates k M n q F)))) (MvPolynomial.X i)
      = graphCoordinates k M n q F i := by
  simp [algebraMap_graphAlgebra]

private theorem graphAlgebraEquiv_symm_comp_algebraMap_comp_C (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤))) :
    ((((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
        (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
          (GraphAlgebra (graphCoordinates k M n q F)))).comp
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k))
      = (MvPolynomial.C : k →+* MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k) := by
  ext c
  simp [algebraMap_graphAlgebra, MvPolynomial.algebraMap_eq]

private theorem appTop_comp_apply {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : ↑(Z.presheaf.obj (Opposite.op ⊤))) :
    (Scheme.Hom.appTop (a ≫ b)) x
      = (Scheme.Hom.appTop a) ((Scheme.Hom.appTop b) x) := rfl

theorem graphMorphismToAffineSpace_basicOpen_jacobianDetSection_eq (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    graphMorphismToAffineSpace k M n q F
        ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
          (jacobianDetSection k M n q F s)) =
      (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToAffineSpace k M n q F s ≫
        (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv := by
  have hgc : basicOpenToSpecGraphAlgebra k M n q F s =
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
          (jacobianDetSection k M n q F s)).ι ≫
        (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
          Spec.map (CommRingCat.ofHom
            ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom)) := rfl
  have h1 : specGraphAwayToAffineSpace k M n q F s =
      specGraphAwayToSpecGraphAlgebra k M n q F s ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
            (GraphAlgebra (graphCoordinates k M n q F)))) :=
    specMap_algebraMap_graphAlgebraAway_eq_comp (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)
  have hre : ∀ {Z : Scheme.{u}}
      (g : Spec (CommRingCat.of (GraphAlgebra (graphCoordinates k M n q F))) ⟶ Z),
      (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToSpecGraphAlgebra k M n q F s ≫ g
        = basicOpenToSpecGraphAlgebra k M n q F s ≫ g := by
    intro Z g
    rw [← Category.assoc, specGraphAwayIsoBasicOpen_inv_comp]
  have key : (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToAffineSpace k M n q F s ≫
        (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv
      = ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s)).ι ≫
          (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
            Spec.map (CommRingCat.ofHom
              (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
                (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
                  (GraphAlgebra (graphCoordinates k M n q F))))) ≫
              (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv := by
    rw [h1, Category.assoc, hre, hgc, CommRingCat.ofHom_comp, Spec.map_comp]
    simp only [Category.assoc]
  have hτ : (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv ≫
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin q))
      = Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)) := by
    simp
  have hσ : (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).inv ≫
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n))
      = Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k)) := by
    simp
  have hA : (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s)).ι ≫
          (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
            Spec.map (CommRingCat.ofHom
              (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
                (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
                  (GraphAlgebra (graphCoordinates k M n q F))))) ≫
              (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv) ≫
        affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin q))
      = ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s)).ι ≫
          affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n)) := by
    simp only [Category.assoc]
    rw [hτ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, graphAlgebraEquiv_symm_comp_algebraMap_comp_C k M n q F, ← hσ,
      Iso.hom_inv_id_assoc]
  have hB : ∀ i : ULift.{u, 0} (Fin M ⊕ Fin q),
      (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F
          ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s))))
        (AffineSpace.coord (Spec (CommRingCat.of k)) i)
      = (Scheme.Hom.appTop (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s)).ι ≫
          (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
            Spec.map (CommRingCat.ofHom
              (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
                (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
                  (GraphAlgebra (graphCoordinates k M n q F))))) ≫
              (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv))
          (AffineSpace.coord (Spec (CommRingCat.of k)) i) := by
    intro i
    have e1 : (Scheme.Hom.appTop (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv)
          (AffineSpace.coord (Spec (CommRingCat.of k)) i)
        = (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k))).inv
            (MvPolynomial.X i) := by
      have h : (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k))).hom
          ((Scheme.Hom.appTop (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv)
            (AffineSpace.coord (Spec (CommRingCat.of k)) i))
          = MvPolynomial.X i :=
        (mvPolynomialEquivGlobalSections_symm_apply k (ULift.{u, 0} (Fin M ⊕ Fin q))
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)).symm.trans
          (mvPolynomialEquivGlobalSections_symm_coord k (ULift.{u, 0} (Fin M ⊕ Fin q)) i)
      rw [← h, Iso.hom_inv_id_apply]
    have e2 : (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom
          (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
            (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
              (GraphAlgebra (graphCoordinates k M n q F)))))))
          ((Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k))).inv
            (MvPolynomial.X i))
        = (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k))).inv
            (graphCoordinates k M n q F i) := by
      rw [← graphAlgebraEquiv_symm_comp_algebraMap_X k M n q F i]
      exact (RingHom.congr_fun (congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
          (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
            (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
              (GraphAlgebra (graphCoordinates k M n q F)))))))
        (MvPolynomial.X i)).symm
    have e3 : (Scheme.Hom.appTop (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom)
          ((Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k))).inv
            (graphCoordinates k M n q F i))
        = mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n)) (graphCoordinates k M n q F i) :=
      (mvPolynomialEquivGlobalSections_apply k (ULift.{u, 0} (Fin M ⊕ Fin n)) (graphCoordinates k M n q F i)).symm
    rw [appTop_comp_apply, appTop_comp_apply, appTop_comp_apply, e1, e2, e3]
    obtain ⟨i⟩ := i
    cases i with
    | inl a =>
      rw [graphCoordinates_inl, mvPolynomialEquivGlobalSections_X]
      exact graphMorphismToAffineSpace_appTop_coord_inl k M n q F _ a
    | inr j =>
      rw [graphCoordinates_inr, mvPolynomialEquivGlobalSections_polynomialOfSection]
      exact graphMorphismToAffineSpace_appTop_coord_inr k M n q F _ j
  rw [key]
  apply AffineSpace.hom_ext
  · exact (graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec k M n q F _).trans hA.symm
  · exact hB

theorem smooth_graphMorphismToAffineSpace_basicOpen (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) (hs : Function.Injective s) :
    Smooth (graphMorphismToAffineSpace k M n q F
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s))) := by
  have hsm : Smooth (specGraphAwayToAffineSpace k M n q F s) :=
    smooth_specMap_algebraMap_graphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)
      (sumVariableMap_injective M n q s hs)
  rw [graphMorphismToAffineSpace_basicOpen_jacobianDetSection_eq k M n q F s]
  infer_instance

end FunctorialResolution.EmbeddedResolution

end
