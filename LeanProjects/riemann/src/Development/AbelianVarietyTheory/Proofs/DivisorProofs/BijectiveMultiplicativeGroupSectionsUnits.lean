import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GmSec

def gammaIso : yoneda.obj (Spec (CommRingCat.of (MvPolynomial Unit (ULift ℤ)))) ≅ Scheme.Γ ⋙ forget CommRingCat :=
  NatIso.ofComponents (fun U => Equiv.toIso
    ((AffineSpace.toSpecMvPolyIntEquiv Unit (X := U.unop)).trans (Equiv.funUnique Unit _))) (by
      intro U V f
      ext g
      rfl)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in

theorem _root_.GlobalTheory.EtC.GmSec.isSheaf_gamma :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (Scheme.Γ ⋙ forget CommRingCat) :=
  Presieve.isSheaf_iso _ _root_.GlobalTheory.EtC.GmSec.gammaIso
    (Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))

abbrev uval {V : Scheme.{0}} (t : ((Scheme.Γ ⋙ unitsF) ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op V)) : Γ(V, ⊤)ˣ :=
  Additive.toMul (ULift.down (α := Additive Γ(V, ⊤)ˣ) t)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private lemma gmSec_uval_map_eq_units_map {U V : Scheme.{0}} (g : V ⟶ U)
    (t : ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op U)) :
    _root_.GlobalTheory.EtC.GmSec.uval (((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
        forget (ModuleCat.{1} (ULift.{1} ℤ))).map g.op t) =
      Units.map (Scheme.Γ.map g.op).hom.toMonoidHom (_root_.GlobalTheory.EtC.GmSec.uval t) :=
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private lemma gmSec_eq_of_uval_eq {U : Scheme.{0}}
    (s s' : ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op U))
    (h : _root_.GlobalTheory.EtC.GmSec.uval s = _root_.GlobalTheory.EtC.GmSec.uval s') : s = s' := by
  cases s; cases s'; congr 1

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private theorem isSheaf_etaleTopology_units :
    Presieve.IsSheaf Scheme.etaleTopology.{0}
      ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) := by
  intro U S hS x hx
  have hG := _root_.GlobalTheory.EtC.GmSec.isSheaf_gamma S hS
  let a : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => ((_root_.GlobalTheory.EtC.GmSec.uval (x f hf) : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  let b : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => (((_root_.GlobalTheory.EtC.GmSec.uval (x f hf))⁻¹ : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  have ha : a.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    exact congrArg (fun t => ((_root_.GlobalTheory.EtC.GmSec.uval t : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤)))
      (hx g₁ g₂ h₁ h₂ w)
  have hb : b.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    have := congrArg (fun t => (((_root_.GlobalTheory.EtC.GmSec.uval t)⁻¹ : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤)))
      (hx g₁ g₂ h₁ h₂ w)
    simp only [gmSec_uval_map_eq_units_map, ← map_inv] at this
    exact this
  have hA := hG.isAmalgamation ha
  have hB := hG.isAmalgamation hb
  set A := hG.amalgamate a ha
  set B := hG.amalgamate b hb
  have hAB : A * B = 1 := by
    refine hG.isSeparatedFor.ext fun V f hf => ?_
    change (Scheme.Γ.map f.op).hom (A * B) = (Scheme.Γ.map f.op).hom 1
    rw [map_mul, map_one]
    change (Scheme.Γ ⋙ forget CommRingCat).map f.op A *
      (Scheme.Γ ⋙ forget CommRingCat).map f.op B = 1
    rw [hA f hf, hB f hf]
    exact (_root_.GlobalTheory.EtC.GmSec.uval (x f hf)).mul_inv
  have hBA : B * A = 1 := by rw [mul_comm, hAB]
  let u : Γ(U, ⊤)ˣ := ⟨A, B, hAB, hBA⟩
  refine ⟨⟨Additive.ofMul u⟩, fun V f hf => gmSec_eq_of_uval_eq _ _ (Units.ext (hA f hf)),
    fun t ht => gmSec_eq_of_uval_eq _ _ (Units.ext ?_)⟩
  refine hG.isSeparatedFor.ext fun V f hf => ?_
  change ((_root_.GlobalTheory.EtC.GmSec.uval (((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).map f.op t) : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) =
    (Scheme.Γ ⋙ forget CommRingCat).map f.op A
  rw [ht f hf, hA f hf]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in

theorem _root_.GlobalTheory.EtC.GmSec.gm_sec_bijective :
    ∀ U : Scheme.{0},
      Function.Bijective
        (_root_.GlobalTheory.EtC.ofRings.sec _root_.GlobalTheory.EtC.unitsF U) := by
  intro U
  have hP : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mpr isSheaf_etaleTopology_units)
  haveI := isIso_toSheafify Scheme.etaleTopology hP
  delta _root_.GlobalTheory.EtC.ofRings.sec
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF)).app (op U))

end GlobalTheory.EtC.GmSec
