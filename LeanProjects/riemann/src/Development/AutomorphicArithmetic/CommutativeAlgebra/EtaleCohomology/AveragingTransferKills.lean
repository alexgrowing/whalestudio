import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PullbackDecomposition
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrystallineAlgebraAlgebraMap
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TheoryEx
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SumTransport

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

private abbrev coefT (l : ℕ) [Fact l.Prime] (n : ℕ) : Test l ⥤ ModuleCat.{0} (Acris l) :=
  CH.modF (testι l ⋙ AcrA l n)

private lemma add_gen {C : Type 1} [Category.{0} C] (Pa : Parts C) {R : Type} [CommRing R]
    (F : C ⥤ ModuleCat.{0} R)
    (hF : ∀ (A : C) (S : Fam A), Pa.Cov S →
      Function.Bijective fun (x : F.obj A) (i : S.ι) => (F.map (S.f i)).hom x)
    (F' : Coef C) (c : ∀ A, F.obj A ≃+ F'.obj A)
    (hc : ∀ {A B : C} (φ : A ⟶ B) (x : F.obj A), c B ((F.map φ).hom x) = (F'.map φ).hom (c A x)) :
    Pa.Add F' := by
  intro A S hS
  have e : (fun (x : F'.obj A) (i : S.ι) => (F'.map (S.f i)).hom x) =
      (fun (v : ∀ i, F.obj (S.B i)) (i : S.ι) => c (S.B i) (v i)) ∘
        (fun (x : F.obj A) (i : S.ι) => (F.map (S.f i)).hom x) ∘ (c A).symm := by
    funext x i
    have := hc (S.f i) ((c A).symm x)
    rw [AddEquiv.apply_symm_apply] at this
    exact this.symm
  rw [e]
  exact (Equiv.piCongrRight fun i => (c (S.B i)).toEquiv).bijective.comp
    ((hF A S hS).comp (c A).symm.bijective)

private lemma coefT_add (hA : AcrAdd) (Pa : Parts (Test l))
    (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S) (n : ℕ) (A : Test l) (S : Fam A)
    (hS : Pa.Cov S) :
    Function.Bijective fun (x : (coefT l n).obj A) (i : S.ι) => ((coefT l n).map (S.f i)).hom x :=
  hA l n A S ((hPa A S).1 hS)

private lemma avg_gen (hLA : LocAvg) {C : Type 1} [Category.{0} C] (Pa : Parts C) (T : Theory C)
    {R : Type} [CommRing R] (F : C ⥤ ModuleCat.{0} R) (F' : Coef C) (hF : Pa.Add F')
    (e : ∀ (P : C ⥤ Type) (j : ℕ), CH.H (CategoryOfElements.π P ⋙ F) j ≃+ T.H P F' j)
    {Q P : C ⥤ Type} (p : Q ⟶ P) {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (hL : Pa.LocTrans p g)
    (m : CH.Mor (CategoryOfElements.π P ⋙ F) (CategoryOfElements.π Q ⋙ F) (RingHom.id R)) (j : ℕ)
    (hm : ∀ x, e Q j (m.pull j x) = T.pull p F' j (e P j x))
    (x : CH.H (CategoryOfElements.π P ⋙ F) j) (hx : m.pull j x = 0) : Fintype.card I • x = 0 := by
  have h0 : T.pull p F' j (e P j x) = 0 := by rw [← hm, hx, map_zero]
  apply (e P j).injective
  rw [map_nsmul, hLA C Pa T F' hF Q P p I g hL j _ h0, map_zero]

private def pullT {Q P : PAlg l ⥤ Type} (p : Q ⟶ P) (n : ℕ) :
    CH.Mor (CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n)
      (CategoryOfElements.π (testι l ⋙ Q) ⋙ coefT l n) (RingHom.id _) := pullMor p n

private lemma locTrans_of {Q P : PAlg l ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I]
    {g : I → (Q ⟶ Q)} (h : TTrans p g) (Pa : Parts (Test l))
    (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S) :
    Pa.LocTrans (Functor.whiskerLeft (testι l) p)
      (fun i => Functor.whiskerLeft (testι l) (g i)) := by
  refine ⟨fun i => ?_, fun A => h.2.1 A, fun A y y' hy => ?_⟩
  · rw [← Functor.whiskerLeft_comp, h.1 i]
  · obtain ⟨S, hS, hm⟩ := h.2.2 A y y' hy
    exact ⟨S, (hPa A S).2 hS, hm⟩

private lemma averaging_transfer_kills (hLA : LocAvg) (hP : PartsEx) (hA : AcrAdd) (hT : TheoryEx)
    {Q P : PAlg l ⥤ Type} (p : Q ⟶ P) {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : TTrans p g)
    (n j : ℕ) (x : CH.H (CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n) j)
    (hx : (pullT p n).pull j x = 0) : Fintype.card I • x = 0 := by
  refine Exists.elim (hP l) fun Pa hPa => Exists.elim (hT (Test l)) fun T hT => ?_
  refine Exists.elim (hT (Acris l) (coefT l n)) fun F' h1 => Exists.elim h1 fun c h2 =>
    Exists.elim h2 fun e h3 => ?_
  have hF : Pa.Add F' := add_gen Pa (coefT l n) (coefT_add hA Pa hPa n) F' c h3.1
  have hG : (pullT p n).G = CategoryOfElements.map (Functor.whiskerLeft (testι l) p) := rfl
  have hτ : ∀ (T : (testι l ⋙ Q).Elements) (y : ((CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n).obj ((pullT p n).G.obj T))),
      HEq ((pullT p n).τ T y) y := fun _ _ => HEq.rfl
  have hm := h3.2 (Functor.whiskerLeft (testι l) p) (pullT p n) hG hτ j
  have hL := locTrans_of h Pa hPa
  exact avg_gen hLA Pa T (coefT l n) F' hF e (Functor.whiskerLeft (testι l) p) hL (pullT p n) j hm x hx

end UpperTheory.Ru.crystallineComparison

open CategoryTheory CategoryTheory.Limits GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.avgMH :
    UpperTheory.Ru.crystallineComparison.AvgMH := by
  intro l _ Q P p I _ g h n j x hx
  exact averaging_transfer_kills locAvg partsEx acrAdd theoryEx p h n j x hx
