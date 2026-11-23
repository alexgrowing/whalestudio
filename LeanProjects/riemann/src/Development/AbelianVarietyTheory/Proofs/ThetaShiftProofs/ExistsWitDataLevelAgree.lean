import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HostModel

open ToricData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def LevelAgree {D : Datum H} {l : Level H} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k}
    (a : ArcIn D l (RingHom.id c.F) k bF) (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X}))
    [Module (𝓞 E) P.toPre.X] {φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
    (uF : F),
    (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
    uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
    ∀ (n : ℕ) (p₀ : QkPt a.D₀ (FractionRing k) n),
      ((n = l.A ∧ ∃ v, HEq p₀ (a.etaA v)) ∨
        (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), HEq p₀ (a.eta v))) →
      ∀ (q₀ : QkPt a.D₀ F n) (q₁ q₂ : QkPt P.toPre F n),
        QkExt (algebraMap _ F) p₀ q₀ → q₁.y = e₁ q₀.y → q₂.y = e₂ q₀.y →
        (∀ z, GenRel w₁ (q₁.g.s (e₁ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
        (∀ z, GenRel w₂ (q₂.g.s (e₂ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
        QkPt.Equiv P.toPre F q₁ q₂

theorem dataRigidSt_iff : DataRigidSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
      (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
      (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
      (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
      (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
      (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
      (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
      (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
      WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ → LevelAgree a P w₁ w₂ e₁ e₂ →
      φ₁ = φ₂ ∧ e₁ = e₂ ∧ HEq w₁ w₂ := Iff.rfl

variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)

def witP : DegData (PowerSeries k) (Ideal.span {PowerSeries.X}) :=
  arcData (X := 𝓞 E) k (arcForm l) (arcIn c k bF).be_symm (arcIn c k bF).be_pos (arcIn_be_even c k bF)

instance instModuleWitP : Module (𝓞 E) (witP c k bF).toPre.X := inferInstanceAs (Module (𝓞 E) (𝓞 E))

def witAct : letI := H.starRing; (witP c k bF).toPre.OAct (𝓞 E) :=
  letI := H.starRing
  arcOAct (X := 𝓞 E) k (arcForm l) (arcIn c k bF).be_symm (arcIn c k bF).be_pos (arcIn_be_even c k bF) (𝓞 E)
    (arcIn c k bF).be_adj

def witMap : (witP c k bF).toPre.P.A.left ⟶ (arcIn c k bF).D₀.P.A.left :=
  baseMap (fun _ : 𝓞 E => 1) (PowerSeries.C (R := k)) (arcExp (X := 𝓞 E) k (arcForm l))

theorem witMap_eSec : eSec (witP c k bF).toPre.P.A ≫ witMap c k bF =
    spMap (PowerSeries.C (R := k)) ≫ eSec (arcIn c k bF).D₀.P.A :=
  eSec_baseMap _ _ _

def witIso : LB.Iso (witP c k bF).toPre.P.L ((arcIn c k bF).D₀.P.L.pull (witMap c k bF)) :=
  baseIso (fun _ : 𝓞 E => 1) (PowerSeries.C (R := k)) (arcExp (X := 𝓞 E) k (arcForm l))

theorem witData_of_isometry (e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E)
    (h : ∀ y : 𝓞 E, (arcIn c k bF).be (e y) (e y) = (arcIn c k bF).be y y) :
    WitData (arcIn c k bF) (witP c k bF) (witAct c k bF) (witMap c k bF) (witMap_eSec c k bF) (witIso c k bF) e := by
  refine ⟨baseMap_pb _ _ _, baseIso_isGen _ _ _, baseIso_rig _ _ _ _, fun _ => end_baseMap _ _ _ _ _,
    fun _ => c_baseMap _ _ _ _ _, ?_⟩
  intro F _ _ _ _ u hF hu y
  exact genRel_arcData_psi (X := 𝓞 E) k _ _ _ _ F u hF hu (e y) y (h y)

theorem witData_refl : WitData (arcIn c k bF) (witP c k bF) (witAct c k bF) (witMap c k bF) (witMap_eSec c k bF)
    (witIso c k bF) (LinearEquiv.refl (𝓞 E) (𝓞 E)) :=
  witData_of_isometry c k bF _ fun _ => rfl

theorem witData_neg : WitData (arcIn c k bF) (witP c k bF) (witAct c k bF) (witMap c k bF) (witMap_eSec c k bF)
    (witIso c k bF) (LinearEquiv.neg (𝓞 E) : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) :=
  witData_of_isometry c k bF _ fun y => by
    rw [LinearEquiv.neg_apply, arcIn_be_apply, arcIn_be_apply, map_neg, map_neg, LinearMap.neg_apply, neg_neg]

omit [IsCMField E] in

theorem refl_ne_neg : LinearEquiv.refl (𝓞 E) (𝓞 E) ≠ (LinearEquiv.neg (𝓞 E) : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) := fun h => by
  have h1 : (1 : 𝓞 E) = -1 := congrArg (fun e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E => e 1) h
  exact one_ne_zero (self_eq_neg.1 h1)

theorem exists_witData : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (D : Datum H)
    (l : Level H) (c : Coeff l) (k : Type) (_ : Field k) (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) (_ : Module (𝓞 E) P.toPre.X)
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    e₁ ≠ e₂ ∧ WitData a P oP φ he w e₁ ∧ WitData a P oP φ he w e₂ :=
  ⟨_, _, _, _, host, _, level host 5 (by norm_num), coeff _, (coeff _).F, _, RingHom.id _, arcIn _ _ _, witP _ _ _, _,
    witAct _ _ _, witMap _ _ _, witMap_eSec _ _ _, witIso _ _ _, _, _, refl_ne_neg, witData_refl _ _ _,
    witData_neg _ _ _⟩

section LevelPts

variable (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F]

theorem equiv_refl_witP {n : ℕ} (p : QkPt (witP c k bF).toPre F n) : QkPt.Equiv _ F p p := by
  obtain ⟨t, ht⟩ := (pt_bijective (arcExp (X := 𝓞 E) k (arcForm l)) F).2 p.g
  refine ⟨(0 : 𝓞 E), ((congrArg (p.y + ·) (nsmul_zero n)).trans (add_zero _)).symm, pt _ F 1,
    (isIota_pt _ F _ _).2 fun χ => ?_, ?_⟩
  · rw [polar_arcExp (X := 𝓞 E) k (arcForm l) (arcIn c k bF).be_symm (arcIn_be_even c k bF), map_zero,
      LinearMap.zero_apply, zpow_zero, Units.val_one, map_one]
    rfl
  · rw [← ht]
    exact (isAdd_pt _ F _ _ _).2 (mul_one t).symm

variable [Algebra (FractionRing k) F]
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
    algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
include hF

theorem eq_of_genRel {n : ℕ} (e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) (x : 𝓞 E → F) (q₀ : QkPt (arcIn c k bF).D₀ F n)
    (q₁ q₂ : QkPt (witP c k bF).toPre F n) (hy : q₁.y = q₂.y)
    (h₁ : ∀ z, GenRel (witIso c k bF) (q₁.g.s (e z)) (q₀.g.s z) (x z))
    (h₂ : ∀ z, GenRel (witIso c k bF) (q₂.g.s (e z)) (q₀.g.s z) (x z)) : q₁ = q₂ := by
  obtain ⟨y₀, g₀, e₀⟩ := q₀
  obtain ⟨y₁, g₁, e₁⟩ := q₁
  obtain ⟨y₂, g₂, e₂⟩ := q₂
  obtain ⟨t₀, rfl⟩ := (pt_bijective (fun _ : 𝓞 E => (1 : (FractionRing k)ˣ)) F).2 g₀
  obtain ⟨t₁, rfl⟩ := (pt_bijective (arcExp (X := 𝓞 E) k (arcForm l)) F).2 g₁
  obtain ⟨t₂, rfl⟩ := (pt_bijective (arcExp (X := 𝓞 E) k (arcForm l)) F).2 g₂
  obtain rfl : y₁ = y₂ := hy
  obtain rfl : t₁ = t₂ := hom_eq_iff.1 fun χ => by
    obtain ⟨z, rfl⟩ := e.surjective χ
    exact Units.ext (((genRel_pt_iff _ _ _ F hF _ _ _ _ _).1 (h₁ z)).trans
      ((genRel_pt_iff _ _ _ F hF _ _ _ _ _).1 (h₂ z)).symm)
  rfl

end LevelPts

theorem levelAgree_self (e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) :
    LevelAgree (arcIn c k bF) (witP c k bF) (witIso c k bF) (witIso c k bF) e e := by
  intro F _ _ _ _ u hF _ n _ _ q₀ q₁ q₂ _ hy₁ hy₂ h₁ h₂
  rw [eq_of_genRel c k bF F hF e _ q₀ q₁ q₂ (hy₁.trans hy₂.symm) h₁ h₂]
  exact equiv_refl_witP c k bF F q₂

theorem levelAgree_refl : LevelAgree (arcIn c k bF) (witP c k bF) (witIso c k bF) (witIso c k bF)
    (LinearEquiv.refl (𝓞 E) (𝓞 E)) (LinearEquiv.refl (𝓞 E) (𝓞 E)) :=
  levelAgree_self c k bF _

theorem exists_witData_levelAgree : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E)
    (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) (_ : Field k) (bF : c.F →+* k)
    (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) (_ : Module (𝓞 E) P.toPre.X)
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ ∧ WitData a P oP φ₂ he₂ w₂ e₂ ∧ LevelAgree a P w₁ w₂ e₁ e₂ :=
  ⟨_, _, _, _, host, _, level host 5 (by norm_num), coeff _, (coeff _).F, _, RingHom.id _, arcIn _ _ _, witP _ _ _, _,
    witAct _ _ _, _, _, witMap_eSec _ _ _, witMap_eSec _ _ _, witIso _ _ _, witIso _ _ _, _, _, witData_refl _ _ _,
    witData_refl _ _ _, levelAgree_refl _ _ _⟩

theorem exists_common_field : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F)
    (_ : Algebra (FractionRing (PowerSeries k)) F) (_ : Algebra (FractionRing k) F),
    ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)) := by
  let F := AlgebraicClosure (FractionRing (PowerSeries k))
  let g : k →+* F := ((algebraMap (FractionRing (PowerSeries k)) F).comp
    (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))).comp PowerSeries.C
  refine ⟨F, inferInstance, inferInstance, inferInstance,
    (IsFractionRing.lift (K := FractionRing k) g.injective).toAlgebra, fun x => ?_⟩
  exact IsFractionRing.lift_algebraMap (K := FractionRing k) g.injective x

end GlobalTheory.HostModel
