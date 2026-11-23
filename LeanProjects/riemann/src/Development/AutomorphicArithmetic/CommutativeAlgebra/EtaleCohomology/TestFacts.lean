import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ZeroPull
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitRules
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

def IsDec {A : Test l} (S : Fam A) : Prop := Function.Bijective fun (a : A.obj.A) (i : S.ι) => PAlg.Hom.f (S.f i).hom a

def TZero {Q P : PAlg l ⥤ Type} {I : Type} [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)) : Prop :=
  ∀ (A : Test l) (y : Q.obj A.obj), ∃ S : Fam A, IsDec S ∧ ∀ s,
    ∑ i, Finsupp.single ((u i).app _ (Q.map (S.f s).hom y)) (a i) = 0 ∨ Subsingleton (S.B s).obj.A

def TTrans {Q P : PAlg l ⥤ Type} (p : Q ⟶ P) {I : Type} [Fintype I] (g : I → (Q ⟶ Q)) : Prop :=
  (∀ i, g i ≫ p = p) ∧ (∀ A : Test l, Function.Surjective (p.app A.obj)) ∧
  ∀ (A : Test l) (y y' : Q.obj A.obj), p.app _ y = p.app _ y' → ∃ S : Fam A, IsDec S ∧ ∀ s,
    (Finset.univ.val.map fun i => (g i).app _ (Q.map (S.f s).hom y)) = Finset.univ.val.map fun i => (g i).app _ (Q.map (S.f s).hom y')

abbrev Qb (A : PAlg l) : Type := A.Q (pFlat l)

abbrev Qo (l : ℕ) [Fact l.Prime] : Type := Ob l ⧸ Ideal.span {pFlat l}

def qs (A : PAlg l) : Qo l →+* Qb A :=
  Ideal.quotientMap _ A.s (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact Ideal.subset_span rfl)

def PQ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (g : O →+* Qo l) : PAlg l ⥤ Type where
  obj A := {y : Spec (CommRingCat.of (Qb A)) ⟶ X // y ≫ q = Spec.map (CommRingCat.ofHom ((qs A).comp g))}
  map {A B} f := TypeCat.ofHom fun y => ⟨Spec.map (CommRingCat.ofHom (PAlg.mapQ f (pFlat l))) ≫ y.1, by
    rw [Category.assoc, y.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g x)
    simp only [RingHom.comp_apply, ← hz]
    exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun (PAlg.Hom.comm f) z)⟩
  map_id A := by
    ext y
    have : PAlg.mapQ (𝟙 A) (pFlat l) = RingHom.id _ := Ideal.Quotient.ringHom_ext rfl
    change Spec.map (CommRingCat.ofHom (PAlg.mapQ (𝟙 A) (pFlat l))) ≫ y.1 = y.1
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  map_comp {A B C} f f' := by
    ext y
    have : PAlg.mapQ (f ≫ f') (pFlat l) = (PAlg.mapQ f' (pFlat l)).comp (PAlg.mapQ f (pFlat l)) := Ideal.Quotient.ringHom_ext rfl
    change Spec.map (CommRingCat.ofHom (PAlg.mapQ (f ≫ f') (pFlat l))) ≫ y.1 =
      Spec.map (CommRingCat.ofHom (PAlg.mapQ f' (pFlat l))) ≫ Spec.map (CommRingCat.ofHom (PAlg.mapQ f (pFlat l))) ≫ y.1
    rw [this, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

def IsFr (m : ℕ) {g : O →+* Qo l} (F : PQ q g ⟶ PQ q g) : Prop :=
  ∀ (A : PAlg l) (φ : Qb A →+* Qb A), (∀ x, φ x = x ^ l ^ m) → ∀ y, (F.app A y).1 = Spec.map (CommRingCat.ofHom φ) ≫ y.1

def IsRd (m : ℕ) {κ : O →+* OC l} {g : O →+* Qo l} (ρ : PX q κ ⟶ PQ q g) : Prop :=
  ∀ (A : PAlg l) (ψ : A.U →+* Qb A), (∀ x : A.W, ψ (A.th x) = Ideal.Quotient.mk _ (x.coeff 0) ^ l ^ m) →
    ∀ y, (ρ.app A y).1 = Spec.map (CommRingCat.ofHom ψ) ≫ y.1

abbrev phiH (P : PAlg l ⥤ Type) (n j : ℕ) : MH P n j → MH P n j := (phiMor P n).pull j

abbrev pullH {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (n j : ℕ) : MH P' n j →ₗ[Acris l] MH P n j := (pullMor u n).pull j

def DecEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (A : Test l) (ι : Type) [Fintype ι] (e : ι → A.obj.A), CompleteOrthogonalIdempotents e →
  ∃ (B : ι → Test l) (f : ∀ i, A ⟶ B i), IsDec (⟨ι, B, f⟩ : Fam A) ∧ ∀ i, PAlg.Hom.f (f i).hom (e i) = 1

def PartsEx : Prop := ∀ (l : ℕ) [Fact l.Prime], ∃ Pa : Parts (Test l), ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S

def AcrAdd : Prop := ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (A : Test l) (S : Fam A), IsDec S →
  Function.Bijective fun (x : A.obj.Acr n) (i : S.ι) => PAlg.mapAcr (S.f i).hom n x

def TheoryEx : Prop := ∀ (C : Type 1) [Category.{0} C], ∃ T : Theory C, ∀ (R : Type) [CommRing R] (F : C ⥤ ModuleCat.{0} R),
  ∃ (F' : Coef C) (c : ∀ A, F.obj A ≃+ F'.obj A) (e : ∀ (P : C ⥤ Type) (j : ℕ), CH.H (CategoryOfElements.π P ⋙ F) j ≃+ T.H P F' j),
    (∀ {A B : C} (φ : A ⟶ B) (x : F.obj A), c B ((F.map φ).hom x) = (F'.map φ).hom (c A x)) ∧
    ∀ {Q P : C ⥤ Type} (u : Q ⟶ P) (m : CH.Mor (CategoryOfElements.π P ⋙ F) (CategoryOfElements.π Q ⋙ F) (RingHom.id R)),
      ∀ h : m.G = CategoryOfElements.map u, (∀ T x, HEq (m.τ T x) x) → ∀ j x, e Q j (m.pull j x) = T.pull u F' j (e P j x)

def SumMH : Prop := ∀ (l : ℕ) [Fact l.Prime] (Q P : PAlg l ⥤ Type) (I : Type) [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)), TZero a u →
  ∀ (n j : ℕ) (x : MH P n j), ∑ i, a i • pullH (u i) n j x = 0

def AvgMH : Prop := ∀ (l : ℕ) [Fact l.Prime] (Q P : PAlg l ⥤ Type) (p : Q ⟶ P) (I : Type) [Fintype I] (g : I → (Q ⟶ Q)), TTrans p g →
  ∀ (n j : ℕ) (x : MH P n j), pullH p n j x = 0 → Fintype.card I • x = 0

def TestFacts : Prop := ∀ (l : ℕ) [Fact l.Prime] (A : PAlg l), A.IsTest → (l : A.U) ∈ nonZeroDivisors A.U ∧
  (∀ x : A.Ug, IsIntegral A.U x → ∃ u : A.U, algebraMap A.U _ u = x) ∧
  (∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A.Ug)), Etale f → Surjective f → ∃ s, s ≫ f = 𝟙 _) ∧
  (∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A.U)), Etale f → Surjective f → ∃ s, s ≫ f = 𝟙 _) ∧
  ∀ e : A.U, IsIdempotentElem e → ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e

def FrEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l)
  (g : O →+* Qo l) (m f : ℕ), (∀ x, g x ^ l ^ f = g x) →
  (∃ F : PQ q g ⟶ PQ q g, IsFr f F) ∧
  ((∀ (x : O) (w : Ainf l), theta0 l w = κ x → g x = Ideal.Quotient.mk _ (w.coeff 0) ^ l ^ m) → ∃ ρ : PX q κ ⟶ PQ q g, IsRd m ρ) ∧
  ∀ (P P' : PAlg l ⥤ Type) (u : P ⟶ P') (n j : ℕ) (x : MH P' n j), phiH P n j (pullH u n j x) = pullH u n j (phiH P' n j x)

def WTrans : Prop := ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (Y : Scheme.{0}) (q : Y ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l)
  (J : Type) [Fintype J] [DecidableEq J] (T : J → Corr l Y) (D : WDat l T),
  ∃ g : (∀ j, Equiv.Perm (Fin (T j).d)) → (PX (D.π ≫ q) κ ⟶ PX (D.π ≫ q) κ), TTrans (pxMap κ D.π rfl) g

def itE {P : PAlg l ⥤ Type} (F : P ⟶ P) (k : ℕ) : P ⟶ P := (show End P from F) ^ k

def WZero : Prop := ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
  Irreducible ϖ → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (Y : Scheme.{0}) (q : Y ⟶ Spec (CommRingCat.of O)), Smooth q → QuasiCompact q →
  AffFin Y → 0 < f → ∀ (T : Fin (n + 1) → Corr l Y) (hr : ∀ j, (T j).r ≫ q = (T j).p ≫ q), PtId l (l ^ f) n (fn q ϖ) T →
  ∀ (κ : O →+* OC l) (g : O →+* Qo l), g ϖ = 0 → ∀ (m : ℕ) (F : PQ q g ⟶ PQ q g) (ρ : PX q κ ⟶ PQ q g), IsFr f F → IsRd m ρ →
  (∀ x, g x ^ l ^ f = g x) → ∀ D : WDat l T, ∃ N : ℕ,
    TZero (I := Σ j : Fin (n + 1), Fin (T j).d) (fun x => (-1) ^ (x.1 : ℕ) * ((l ^ f) ^ ((x.1 : ℕ).choose 2) : ℕ))
      fun x => pxMap (p := D.π ≫ q) κ (D.s x.1 x.2 ≫ (T x.1).r)
        (by rw [Category.assoc, hr, ← Category.assoc, D.hs]) ≫ ρ ≫ itE F (n - x.1 + N)

end UpperTheory.Ru.crystallineComparison
