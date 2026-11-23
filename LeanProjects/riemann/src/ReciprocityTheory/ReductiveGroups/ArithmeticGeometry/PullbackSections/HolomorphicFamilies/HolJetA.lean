import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {Y : Scheme.{0}}

theorem germ_stalkClosedPointTo_eq {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ Y) (U : Y.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) :
    Y.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem f hU).ge ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo, Scheme.Hom.appLE]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc]
  first
  | rfl
  | congr 3

set_option backward.isDefEq.respectTransparency false in

theorem hom_ext_of_local {R : CommRingCat.{0}} [IsLocalRing R] {f₁ f₂ : Spec R ⟶ Y}
    (hpt : f₁ (IsLocalRing.closedPoint R) = f₂ (IsLocalRing.closedPoint R))
    (happ : ∀ (U : Y.Opens) (h₁ : ⊤ ≤ f₁ ⁻¹ᵁ U) (h₂ : ⊤ ≤ f₂ ⁻¹ᵁ U), f₁.appLE U ⊤ h₁ = f₂.appLE U ⊤ h₂) :
    f₁ = f₂ := by
  apply (SpecToEquivOfLocalRing Y R).injective
  refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨hpt, ?_⟩
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  change Y.presheaf.germ U (f₁ (IsLocalRing.closedPoint R)) hU ≫ Scheme.stalkClosedPointTo f₁ =
    Y.presheaf.germ U (f₁ (IsLocalRing.closedPoint R)) hU ≫ (Y.presheaf.stalkCongr _).hom ≫
      Scheme.stalkClosedPointTo f₂
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_assoc, germ_stalkClosedPointTo_eq,
    germ_stalkClosedPointTo_eq, happ]

section Lift

variable (y₀ : Y) (A : CommRingCat.{0})

def nbhdLift (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU) :
    Y.presheaf.stalk y₀ ⟶ A :=
  Limits.colimit.desc ((OpenNhds.inclusion y₀).op ⋙ Y.presheaf)
    { pt := A
      ι := { app := fun U => ψ U.unop.1 U.unop.2
             naturality := fun U V i =>
               (hψ U.unop.1 V.unop.1 U.unop.2 V.unop.2 (leOfHom i.unop)).trans (Category.comp_id _).symm } }

variable {y₀ A}

theorem germ_nbhdLift (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU) (U : Y.Opens) (hU : y₀ ∈ U) :
    Y.presheaf.germ U y₀ hU ≫ nbhdLift y₀ A ψ hψ = ψ U hU := by
  exact Limits.colimit.ι_desc _ _

def nbhdPt (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU) : Spec A ⟶ Y :=
  Spec.map (nbhdLift y₀ A ψ hψ) ≫ Y.fromSpecStalk y₀

theorem isLocalHom_nbhdLift [IsLocalRing A] (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hloc : ∀ (U : Y.Opens) (hU : y₀ ∈ U) (f : Γ(Y, U)), IsUnit (ψ U hU f) → y₀ ∈ Y.basicOpen f) :
    IsLocalHom (nbhdLift y₀ A ψ hψ).hom := by
  constructor
  intro a ha
  obtain ⟨U, hU, f, rfl⟩ := Y.presheaf.germ_exist a
  have e : (nbhdLift y₀ A ψ hψ).hom (Y.presheaf.germ U y₀ hU f) = ψ U hU f := by
    first
    | simpa using congrArg (fun g => g.hom f) (germ_nbhdLift ψ hψ U hU)
    | rw [← CommRingCat.comp_apply, germ_nbhdLift]
  rw [e] at ha
  first
  | exact (Y.mem_basicOpen f ⟨y₀, hU⟩).mp (hloc U hU f ha)
  | exact (Y.mem_basicOpen f y₀ hU).mp (hloc U hU f ha)

set_option backward.isDefEq.respectTransparency false in
theorem nbhdPt_closedPoint [IsLocalRing A] (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hloc : ∀ (U : Y.Opens) (hU : y₀ ∈ U) (f : Γ(Y, U)), IsUnit (ψ U hU f) → y₀ ∈ Y.basicOpen f) :
    nbhdPt ψ hψ (IsLocalRing.closedPoint A) = y₀ := by
  haveI := isLocalHom_nbhdLift ψ hψ hloc
  show (Y.fromSpecStalk y₀) ((Spec.map (nbhdLift y₀ A ψ hψ)) (IsLocalRing.closedPoint A)) = y₀
  have e : (Spec.map (nbhdLift y₀ A ψ hψ)) (IsLocalRing.closedPoint A) =
      IsLocalRing.closedPoint (Y.presheaf.stalk y₀) := by
    first
    | exact IsLocalRing.comap_closedPoint (nbhdLift y₀ A ψ hψ).hom
    | simp
  rw [e, Scheme.fromSpecStalk_closedPoint]

set_option backward.isDefEq.respectTransparency false in

theorem nbhdPt_appLE [IsLocalRing A] (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hloc : ∀ (U : Y.Opens) (hU : y₀ ∈ U) (f : Γ(Y, U)), IsUnit (ψ U hU f) → y₀ ∈ Y.basicOpen f)
    (U : Y.Opens) (hU : y₀ ∈ U) (h : ⊤ ≤ nbhdPt ψ hψ ⁻¹ᵁ U) :
    (nbhdPt ψ hψ).appLE U ⊤ h = ψ U hU ≫ (Scheme.ΓSpecIso A).inv := by
  have := isLocalHom_nbhdLift ψ hψ hloc
  have hpt := nbhdPt_closedPoint ψ hψ hloc
  have hU' : nbhdPt ψ hψ (IsLocalRing.closedPoint A) ∈ U := by rw [hpt]; exact hU
  have k := germ_stalkClosedPointTo_eq (nbhdPt ψ hψ) U hU'
  have k2 := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (nbhdLift y₀ A ψ hψ) U hU'
  rw [germ_nbhdLift] at k2
  have k3 : (nbhdPt ψ hψ).appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem _ hU').ge ≫
      (Scheme.ΓSpecIso A).hom = ψ U hU := k.symm.trans k2
  rw [← k3]
  simp

theorem nbhdLift_comp {B : CommRingCat.{0}} (χ : A ⟶ B) (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU) :
    nbhdLift y₀ B (fun U hU => ψ U hU ≫ χ) (fun U V hU hV h => by rw [← Category.assoc, hψ]) =
      nbhdLift y₀ A ψ hψ ≫ χ := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  rw [germ_nbhdLift, ← Category.assoc, germ_nbhdLift]

theorem spec_comp_nbhdPt {B : CommRingCat.{0}} (χ : A ⟶ B) (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU) :
    Spec.map χ ≫ nbhdPt ψ hψ =
      nbhdPt (fun U hU => ψ U hU ≫ χ) (fun U V hU hV h => by rw [← Category.assoc, hψ]) := by
  simp only [nbhdPt]
  rw [nbhdLift_comp, Spec.map_comp, Category.assoc]

theorem nbhdPt_congr {ψ ψ' : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A)}
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hψ' : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ' V hV = ψ' U hU)
    (e : ∀ U hU, ψ U hU = ψ' U hU) : nbhdPt ψ hψ = nbhdPt ψ' hψ' := by
  obtain rfl : ψ = ψ' := funext fun U => funext fun hU => e U hU
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem nbhdPt_comp_appLE [IsLocalRing A] {Y' : Scheme.{0}} (φ : Y ⟶ Y')
    (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hloc : ∀ (U : Y.Opens) (hU : y₀ ∈ U) (f : Γ(Y, U)), IsUnit (ψ U hU f) → y₀ ∈ Y.basicOpen f)
    (U' : Y'.Opens) (hU' : φ y₀ ∈ U') (h : ⊤ ≤ (nbhdPt ψ hψ ≫ φ) ⁻¹ᵁ U') :
    (nbhdPt ψ hψ ≫ φ).appLE U' ⊤ h = φ.app U' ≫ ψ (φ ⁻¹ᵁ U') hU' ≫ (Scheme.ΓSpecIso A).inv := by
  rw [Scheme.Hom.comp_appLE]
  first
  | rw [nbhdPt_appLE ψ hψ hloc (φ ⁻¹ᵁ U') hU']
  | erw [nbhdPt_appLE ψ hψ hloc (φ ⁻¹ᵁ U') hU']

end Lift

section Jet

variable (K : Type) [Field K] (ι : Type) (m : ℕ)

open Formalism.L2.Pj MvPolynomial

theorem jet_nilpotent_of_orig {p : MvPolynomial ι K} (hp : p ∈ orig K ι) :
    IsNilpotent (Ideal.Quotient.mk (orig K ι ^ (m + 1)) p) := by
  refine ⟨m + 1, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hp _

instance isLocalRing_jet : IsLocalRing (Jet K ι m) := by
  haveI : Nontrivial (Jet K ι m) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    intro htop
    have h1 : (1 : MvPolynomial ι K) ∈ orig K ι := by
      have := (Ideal.eq_top_iff_one _).mp htop
      exact Ideal.pow_le_self (Nat.succ_ne_zero m) this
    have h1' : (1 : MvPolynomial ι K) ∈ Ideal.span (X '' Set.univ) := by rw [Set.image_univ]; exact h1
    obtain ⟨i, _, hi⟩ := (MvPolynomial.mem_ideal_span_X_image.mp h1') 0 (by simp)
    simp at hi
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hn := jet_nilpotent_of_orig K ι m (sub_const_mem_orig (R := K) p)
  have hsplit : Ideal.Quotient.mk (orig K ι ^ (m + 1)) p =
      algebraMap K (Jet K ι m) (constantCoeff p) +
        Ideal.Quotient.mk (orig K ι ^ (m + 1)) (p - C (constantCoeff p)) := by
    have e : algebraMap K (Jet K ι m) (constantCoeff p) =
        Ideal.Quotient.mk (orig K ι ^ (m + 1)) (C (constantCoeff p)) := by
      rw [← MvPolynomial.algebraMap_eq]; rfl
    rw [map_sub, e, add_sub_cancel]
  by_cases hc : constantCoeff p = 0
  · right
    have e : Ideal.Quotient.mk (orig K ι ^ (m + 1)) p =
        Ideal.Quotient.mk (orig K ι ^ (m + 1)) (p - C (constantCoeff p)) := by
      rw [hc]; simp
    rw [e, sub_eq_add_neg]
    exact IsNilpotent.isUnit_add_left_of_commute hn.neg isUnit_one (Commute.all _ _)
  · left
    rw [hsplit]
    exact IsNilpotent.isUnit_add_left_of_commute hn
      ((isUnit_iff_ne_zero.mpr hc).map (algebraMap K (Jet K ι m))) (Commute.all _ _)

end Jet

end ReciprocityTheory.ChartRestriction.G.PullbackSections
