import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartTransportSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanAlg

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Tan

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (G : Over X0) [GrpObj G] [IsCommMonObj G]

def tanSub : Subgroup (overAt x0 (DualNumber S) ⟶ G) where
  carrier := {W | smT x0 0 W = 1}
  mul_mem' {u w} hu hw := by
    have hu : smT x0 0 u = 1 := hu
    have hw : smT x0 0 w = 1 := hw
    show smT x0 0 (u * w) = 1
    rw [smT_mul, hu, hw, _root_.mul_one]
  one_mem' := smT_one' x0 0
  inv_mem' {W} hW := by
    have hW : smT x0 0 W = 1 := hW
    show smT x0 0 W⁻¹ = 1
    have h := map_inv (smHom x0 (G := G) 0) W
    change smT x0 0 W⁻¹ = (smT x0 0 W)⁻¹ at h
    rw [h, hW, inv_one]

abbrev TanM := Additive (tanSub x0 G)

variable {x0 G}

def tv (m : TanM x0 G) : overAt x0 (DualNumber S) ⟶ G := (Additive.toMul m : tanSub x0 G)

theorem tv_zero' (m : TanM x0 G) : smT x0 0 (tv m) = 1 := (Additive.toMul m).2

def mkT (W : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 W = 1) : TanM x0 G := Additive.ofMul ⟨W, h⟩

theorem tv_injective : Function.Injective (tv (x0 := x0) (G := G)) := fun _ _ h => Subtype.ext h

theorem tv_add (m m' : TanM x0 G) : tv (m + m') = tv m * tv m' := rfl

theorem tv_sum {κ : Type} (s : Finset κ) (f : κ → TanM x0 G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, tv_add, ih]

instance : Module S (TanM x0 G) where
  smul a m := mkT (smT x0 a (tv m)) (by rw [smT_smT, zero_mul]; exact tv_zero' m)
  one_smul m := tv_injective (smT_unit x0 (tv m))
  mul_smul a b m := tv_injective (smT_smT x0 a b (tv m)).symm
  smul_zero a := tv_injective (smT_one' x0 a)
  smul_add a m m' := tv_injective (smT_mul x0 a (tv m) (tv m'))
  add_smul a b m := tv_injective (smT_add x0 (tv m) (tv_zero' m) a b)
  zero_smul m := tv_injective (tv_zero' m)

def postL (φ : G ⟶ G) [IsMonHom φ] : Module.End S (TanM x0 G) where
  toFun m := mkT (tv m ≫ φ) (by rw [smT_post, tv_zero' m, MonObj.one_comp])
  map_add' m m' := tv_injective (MonObj.mul_comp (tv m) (tv m') φ)
  map_smul' a m := tv_injective (smT_post x0 a (tv m) φ).symm

theorem tv_postL (φ : G ⟶ G) [IsMonHom φ] (m : TanM x0 G) : tv (postL φ m) = tv m ≫ φ := rfl

def actL {O : Type} [CommRing O] (ρ : OAct O G) : O →+* Module.End S (TanM x0 G) where
  toFun a := letI := ρ.hom a; postL (ρ.act a)
  map_one' := LinearMap.ext fun m => tv_injective (by
    rw [tv_postL, ρ.one, Category.comp_id]; rfl)
  map_mul' a b := LinearMap.ext fun m => tv_injective (by
    rw [Module.End.mul_apply, tv_postL, tv_postL, tv_postL, mul_comm a b, ρ.mul, Category.assoc])
  map_zero' := LinearMap.ext fun m => tv_injective (by
    have h0 : ρ.act 0 = 1 := by
      have h := ρ.add 0 0
      rw [add_zero] at h
      have h' : ρ.act 0 * ρ.act 0 = ρ.act 0 * 1 := by rw [_root_.mul_one]; exact h.symm
      exact mul_left_cancel h'
    rw [tv_postL, h0, MonObj.comp_one]; rfl)
  map_add' a b := LinearMap.ext fun m => tv_injective (by
    rw [LinearMap.add_apply, tv_add, tv_postL, tv_postL, tv_postL, ρ.add, MonObj.comp_mul])

theorem tv_comb {κ : Type} [Fintype κ] (v : κ → TanM x0 G) (a : κ → S) :
    tv (∑ k, a k • v k) = ∏ k, smT x0 (a k) (tv (v k)) := by
  rw [tv_sum]; rfl

end Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem frTanBasis_holds (Xo : Moduli Dw l) (c : Coeff l) : FrTanBasisSt Xo c := by
  classical
  intro S _ _ y w hw
  haveI : CharZero S := charZero_of_injective_algebraMap (algebraMap c.F S).injective
  let G := Xo.univ.t.G
  let ρ : 𝓞 E →+* Module.End S (TanM y.x G) := actL Xo.univ.t.act
  let χ : (E →+* ℂ) → (E →+* S) := fun σ => (algebraMap c.F S).comp (embF c σ)
  have hχ : Function.Injective χ := by
    intro σ τ h
    ext x
    have h1 := RingHom.congr_fun h x
    have h2 : embF c σ x = embF c τ x := (algebraMap c.F S).injective h1
    exact congrArg (fun z : c.F => (z : ℂ)) h2
  have hcard : Fintype.card (E →+* ℂ) = Module.finrank ℚ E := by
    convert NumberField.Embeddings.card E ℂ
  let U : Lt1 Dw → TanM y.x G := fun ℓ =>
    mkT (ovT (t := Xo.univ.t) (y.tan ℓ.1 ℓ.2)) (smT_zero_ovT (y.tan ℓ.1 ℓ.2))
  have hU : ∀ σ i (a : 𝓞 E), ρ a (U ⟨σ, i⟩) = χ σ (a : E) • U ⟨σ, i⟩ := fun σ i a =>
    tv_injective ((isEigAt_iff σ (ovT (t := Xo.univ.t) (y.tan σ i))).1 (y.eig σ i) a)
  have hcombσ : ∀ σ (cf : Fin (Dw.mult σ) → S) (W : TanM y.x G),
      IsCombAt y.x (y.u σ) cf (tv W).left ↔ ∑ i, cf i • U ⟨σ, i⟩ = W := by
    intro σ cf W
    have e := isCombAtG_iff Xo.univ.t y.x (fun j => ovT (t := Xo.univ.t) (y.tan σ j)) cf (tv W).left
    refine e.trans ⟨fun h => tv_injective ?_, fun h => ?_⟩
    · rw [tv_comb]
      exact Over.OverMorphism.ext h
    · rw [← h, tv_comb]
      rfl
  have hb : ∀ σ (W : TanM y.x G), (∀ a : 𝓞 E, ρ a W = χ σ (a : E) • W) →
      ∃! cf : Fin (Dw.mult σ) → S, ∑ i, cf i • U ⟨σ, i⟩ = W := by
    intro σ W hW
    have hT : IsTanAt y.x (tv W).left := isTanAtG_of (t := Xo.univ.t) (tv W) (tv_zero' W)
    have hE : IsEigAt c σ (tv W).left :=
      (isEigAt_iff σ (tv W)).2 fun a => congrArg tv (hW a)
    obtain ⟨cf, hcf, hu⟩ := y.basis σ _ hT hE
    exact ⟨cf, (hcombσ σ cf W).1 hcf, fun cf' h => hu cf' ((hcombσ σ cf' W).2 h)⟩
  let W0 : TanM y.x G := mkT (ovT (t := Xo.univ.t) hw) (smT_zero_ovT hw)
  obtain ⟨a, ha, hu⟩ := FrTanAlg.global_basis χ hχ hcard ρ U hU hb W0
  let e := Fintype.equivFin (Lt1 Dw)
  have hiff : ∀ a' : Lt1 Dw → S, IsCombAt y.x (m := Fintype.card (Lt1 Dw))
      (fun i => y.u (e.symm i).1 (e.symm i).2) (fun i => a' (e.symm i)) w ↔ ∑ ℓ, a' ℓ • U ℓ = W0 := by
    intro a'
    have e1 := isCombAtG_iff Xo.univ.t y.x (fun i => ovT (t := Xo.univ.t) (y.tan (e.symm i).1 (e.symm i).2))
      (fun i => a' (e.symm i)) w
    have hprod : combT y.x (fun i => ovT (t := Xo.univ.t) (y.tan (e.symm i).1 (e.symm i).2))
        (fun i => a' (e.symm i)) = tv (∑ ℓ, a' ℓ • U ℓ) := by
      rw [tv_comb]
      exact Equiv.prod_comp e.symm (fun ℓ => smT y.x (a' ℓ) (tv (U ℓ)))
    refine e1.trans ⟨fun h => tv_injective ?_, fun h => ?_⟩
    · rw [← hprod]
      exact Over.OverMorphism.ext h
    · rw [hprod, h]
      rfl
  exact ⟨a, (hiff a).2 ha, fun a' h => hu a' ((hiff a').1 h)⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan
