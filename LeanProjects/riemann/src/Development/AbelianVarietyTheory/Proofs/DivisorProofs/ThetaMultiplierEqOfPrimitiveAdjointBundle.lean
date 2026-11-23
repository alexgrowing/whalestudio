import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEqTauOfBundlePrimitiveForEndomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTripleLinearTorsionIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionDegenerationLinearUniformisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.PrimAdj

section Ring

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem isMonHom_mul' (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) where
  one_hom := by
    rw [MonObj.comp_mul, IsMonHom.one_hom, IsMonHom.one_hom, MonObj.one_eq_one, _root_.mul_one]
  mul_hom := by
    have h : ∀ k : G ⟶ G, [IsMonHom k] → (k ⊗ₘ k) ≫ μ[G] = (fst G G ≫ k) * (snd G G ≫ k) := fun k _ => by
      rw [MonObj.mul_eq_mul, MonObj.comp_mul]
      simp
    rw [MonObj.comp_mul, IsMonHom.mul_hom, IsMonHom.mul_hom, h, h, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp only [← Category.assoc, tensorHom_fst, tensorHom_snd, MonObj.comp_mul]
    exact mul_mul_mul_comm _ _ _ _

def evId (e : AddMonoid.End (Additive (G ⟶ G))) : G ⟶ G := (e (Additive.ofMul (𝟙 _))).toMul

structure IsEnd (e : AddMonoid.End (Additive (G ⟶ G))) : Prop where
  hom : IsMonHom (evId e)
  eq : ∀ x, (e x).toMul = x.toMul ≫ evId e

variable (G) in

def endRing : Subring (AddMonoid.End (Additive (G ⟶ G))) where
  carrier := {e | IsEnd e}
  mul_mem' {a b} ha hb := by
    have := ha.hom; have := hb.hom
    have e : evId (a * b) = evId b ≫ evId a := ha.eq _
    refine ⟨by rw [e]; infer_instance, fun x => ?_⟩
    rw [e, ← Category.assoc, ← hb.eq]
    exact ha.eq _
  one_mem' := ⟨inferInstanceAs (IsMonHom (𝟙 _)), fun x => (Category.comp_id x.toMul).symm⟩
  add_mem' {a b} ha hb := by
    have := ha.hom; have := hb.hom
    have e : evId (a + b) = evId a * evId b := rfl
    refine ⟨by rw [e]; exact isMonHom_mul' _ _, fun x => ?_⟩
    rw [e, MonObj.comp_mul, ← ha.eq, ← hb.eq]
    rfl
  zero_mem' := by
    refine ⟨?_, fun x => (MonObj.comp_one x.toMul).symm⟩
    have e : evId (0 : AddMonoid.End (Additive (G ⟶ G))) = 𝟙 G * (𝟙 G)⁻¹ := (mul_inv_cancel (𝟙 G)).symm
    rw [e]
    exact isMonHom_mul' _ _
  neg_mem' {a} ha := by
    have := ha.hom
    have e : evId (-a) = (evId a)⁻¹ := rfl
    refine ⟨by rw [e]; infer_instance, fun x => ?_⟩
    rw [e, GrpObj.comp_inv, ← ha.eq]
    rfl

def endOf (f : G ⟶ G) [IsMonHom f] : endRing G :=
  ⟨AddMonoidHom.mk' (fun x => Additive.ofMul (x.toMul ≫ f)) fun x y => MonObj.mul_comp _ _ f,
    ⟨by show IsMonHom (𝟙 G ≫ f); rw [Category.id_comp]; infer_instance,
      fun x => by show x.toMul ≫ f = x.toMul ≫ (𝟙 G ≫ f); rw [Category.id_comp]⟩⟩

end Ring

def PolyO : Type := Polynomial ℤ

instance : CommRing PolyO := inferInstanceAs (CommRing (Polynomial ℤ))

theorem comp_one_sub_invol (p : Polynomial ℤ) :
    (p.comp (1 - Polynomial.X)).comp (1 - Polynomial.X) = p := by
  rw [Polynomial.comp_assoc]
  simp

theorem comp_one_sub_add (p q : Polynomial ℤ) :
    (p + q).comp (1 - Polynomial.X) = p.comp (1 - Polynomial.X) + q.comp (1 - Polynomial.X) :=
  Polynomial.add_comp

instance : StarRing PolyO where
  star p := Polynomial.comp (R := ℤ) p (1 - Polynomial.X)
  star_involutive p := comp_one_sub_invol p
  star_mul a b := (Polynomial.mul_comp (R := ℤ) a b _).trans (mul_comm _ _)
  star_add a b := comp_one_sub_add a b

def xO : PolyO := (Polynomial.X : Polynomial ℤ)

theorem star_xO : star xO = 1 - xO := Polynomial.X_comp (R := ℤ)

theorem xO_add_star : xO + star xO = 1 := by rw [star_xO]; ring

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (f : G ⟶ G) [IsMonHom f]

def polyAct : RingAct G PolyO where
  act p := evId (Polynomial.aeval (endOf f) (p : Polynomial ℤ)).1
  hom p := (Polynomial.aeval (endOf f) (p : Polynomial ℤ)).2.hom
  map_one := by
    have e := map_one (Polynomial.aeval (R := ℤ) (endOf f))
    exact (congrArg (fun u : endRing G => evId u.1) e).trans rfl
  map_mul a b := by
    have e := map_mul (Polynomial.aeval (R := ℤ) (endOf f)) (a : Polynomial ℤ) (b : Polynomial ℤ)
    exact (congrArg (fun u : endRing G => evId u.1) e).trans ((Polynomial.aeval (endOf f) (a : Polynomial ℤ)).2.eq _)
  map_add a b := by
    have e := map_add (Polynomial.aeval (R := ℤ) (endOf f)) (a : Polynomial ℤ) (b : Polynomial ℤ)
    exact (congrArg (fun u : endRing G => evId u.1) e).trans rfl

theorem polyAct_X : (polyAct f).act xO = f := by
  have e := Polynomial.aeval_X (R := ℤ) (endOf f)
  exact (congrArg (fun u : endRing G => evId u.1) e).trans (Category.id_comp f)

def addOf (o : RingAct G PolyO) : PolyO →+ Additive (G ⟶ G) :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (o.act a)) fun a b => by rw [o.map_add]; rfl

theorem polyAct_star {f' : G ⟶ G} (h : f * f' = 𝟙 G) : (polyAct f).act (star xO) = f' := by
  have e := map_sub (addOf (polyAct f)) 1 xO
  have e' : (polyAct f).act (1 - xO) = 𝟙 G / f := by
    have := congrArg Additive.toMul e
    simp only [addOf, AddMonoidHom.mk'_apply, (polyAct f).map_one, polyAct_X] at this
    exact this
  rw [star_xO, e']
  exact (eq_div_of_mul_eq' ((mul_comm f' f).trans h)).symm

end Act

end GlobalTheory.PrimAdj

namespace GlobalTheory.PrimAdj

section Adj

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem lam_mul_right' {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) {T : Over S}
    (x y z : T ⟶ G) : lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm, lam_comm _ z]

theorem adjCls_all {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (o : RingAct G PolyO)
    (hX : AdjCls (cls L hL) (cls L hL) (o.act xO) (o.act (star xO))) :
    ∀ a, AdjCls (cls L hL) (cls L hL) (o.act a) (o.act (star a)) := by
  have h0 : o.act 0 = 1 := by
    have e := map_zero (addOf o)
    exact congrArg Additive.toMul e
  have hn : ∀ a, o.act (-a) = (o.act a)⁻¹ := fun a => by
    have e := map_neg (addOf o) a
    exact congrArg Additive.toMul e
  let Sb : Subring PolyO :=
    { carrier := {a | AdjCls (cls L hL) (cls L hL) (o.act a) (o.act (star a))}
      mul_mem' := fun {a b} ha hb T x z => by
        show lam _ x (z ≫ o.act (star (a * b))) = lam _ (x ≫ o.act (a * b)) z
        rw [star_mul, o.map_mul, o.map_mul, ← Category.assoc, hb, ← Category.assoc, ha]
      one_mem' := fun T x z => by
        show lam _ x (z ≫ o.act (star 1)) = lam _ (x ≫ o.act 1) z
        rw [star_one, o.map_one, Category.comp_id, Category.comp_id]
      add_mem' := fun {a b} ha hb T x z => by
        show lam _ x (z ≫ o.act (star (a + b))) = lam _ (x ≫ o.act (a + b)) z
        rw [star_add, o.map_add, o.map_add]
        show lam _ x (z ≫ (o.act (star a) * o.act (star b))) = lam _ (x ≫ (o.act a * o.act b)) z
        rw [MonObj.comp_mul, MonObj.comp_mul, lam_mul_right' hL hΘ, lam_mul_left hL hΘ, ha, hb]
      zero_mem' := fun T x z => by
        show lam _ x (z ≫ o.act (star 0)) = lam _ (x ≫ o.act 0) z
        rw [star_zero, h0, MonObj.comp_one, MonObj.comp_one, lam_one_left, lam_one_right]
      neg_mem' := fun {a} ha T x z => by
        show lam _ x (z ≫ o.act (star (-a))) = lam _ (x ≫ o.act (-a)) z
        rw [star_neg, hn, hn, GrpObj.comp_inv, GrpObj.comp_inv]
        have e₁ := lam_mul_right' hL hΘ x (z ≫ o.act (star a)) (z ≫ o.act (star a))⁻¹
        have e₂ := lam_mul_left hL hΘ (x ≫ o.act a) (x ≫ o.act a)⁻¹ z
        rw [mul_inv_cancel, lam_one_right] at e₁
        rw [mul_inv_cancel, lam_one_left] at e₂
        rw [ha] at e₁
        exact (eq_neg_of_add_eq_zero_right e₁.symm).trans (eq_neg_of_add_eq_zero_right e₂.symm).symm }
  have hXm : xO ∈ Sb := hX
  intro a
  show a ∈ Sb
  induction (a : Polynomial ℤ) using Polynomial.induction_on with
  | C c => exact (eq_intCast Polynomial.C c) ▸ intCast_mem Sb c
  | add p q hp hq => exact Sb.add_mem hp hq
  | monomial n c h =>
    have e : (Polynomial.C c * Polynomial.X ^ (n + 1) : Polynomial ℤ) = Polynomial.C c * Polynomial.X ^ n * Polynomial.X := by
      ring
    rw [e]
    exact Sb.mul_mem h hXm

end Adj

theorem primVal_of_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (f f' : G ⟶ G), IsMonHom f → IsMonHom f' → f * f' = 𝟙 G → AdjCls (cls U.LG.L U.LG.isLB) (cls U.LG.L U.LG.isLB) f f' → cls U.LG.L U.LG.isLB = lam (cls U.LG.L U.LG.isLB) (𝟙 G) f → ∀ (fB : D.toPre.P.A ⟶ D.toPre.P.A) (m : D.toPre.X → D.toPre.X), Over₀ U.toUnifPre U.toUnifPre f fB → OnTorus U.toUnifPre U.toUnifPre f' m → PrimVal D.toPre fB m := by
  intro R _ _ _ hR D A G _ _ hG U f f' hf hf' hff hadj hcls fB m hB hm
  let o := polyAct f
  have aX : o.act xO = f := polyAct_X f
  have aS : o.act (star xO) = f' := polyAct_star f hff
  have hΘ : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have adjA := adjCls_all U.LG.isLB hΘ o (by rw [aX, aS]; exact hadj)
  have hros : ∀ a, LBIso (cubeLB G ![fst G G ≫ o.act a, snd G G] U.LG.L)
      (cubeLB G ![fst G G, snd G G ≫ o.act (star a)] U.LG.L) := fun a => by
    have c₁ := GlobalTheory.CechPic.cls_cube_two U.LG.isLB (fst G G ≫ o.act a) (snd G G) (LB.isLB_linComb U.LG.isLB _ _)
    have c₂ := GlobalTheory.CechPic.cls_cube_two U.LG.isLB (fst G G) (snd G G ≫ o.act (star a)) (LB.isLB_linComb U.LG.isLB _ _)
    exact (cls_eq_iff _ _).1 (c₁.trans ((adjA a _ (fst G G) (snd G G)).symm.trans c₂.symm))
  have hprim : LBIso U.LG.L (cubeLB G ![𝟙 G, o.act xO] U.LG.L) := by
    have c₁ := GlobalTheory.CechPic.cls_cube_two U.LG.isLB (𝟙 G) f (LB.isLB_linComb U.LG.isLB _ _)
    rw [aX]
    exact (cls_eq_iff _ _).1 (hcls.trans c₁.symm)
  have := hR.2
  obtain ⟨oA, hA⟩ := GlobalTheory.PELOfUnif.exists_oAct_unif U.toUnifPre o hros
  obtain ⟨-, h1, h2, h3, h4⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  obtain ⟨md, oD, lin⟩ := GlobalTheory.RingActData.exists_oAct GlobalTheory.firstFiveLaws h1 h2 h3 h4 R (maximalIdeal R) hR.1 D A G hG U
    PolyO oA o hA hros
  have pv := isPrimitiveValue_of_ringElement_psiRelation (GlobalTheory.PsiSign.psi_eq_tau_of_bundle_primitive_for_endomorphism R hR D A G hG U PolyO oD oA o lin hros xO xO_add_star hprim)
  have uq := over₀_onTorus_unique R (maximalIdeal R) hR.1 D D A A G G U.toUnifPre U.toUnifPre f
  have eB : fB = oD.onB.act xO := uq.1 _ _ hB fun e => by
    have := lin.q_lin e xO
    rwa [aX] at this
  have uq' := over₀_onTorus_unique R (maximalIdeal R) hR.1 D D A A G G U.toUnifPre U.toUnifPre f'
  have eM : m = fun y => xO • y := uq'.2 _ _ hm fun e => by
    obtain ⟨t, ht, he⟩ := lin.i_lin e (star xO)
    rw [star_star, aS] at *
    exact ⟨t, ht, he⟩
  subst eB eM
  exact pv

end GlobalTheory.PrimAdj
