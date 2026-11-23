import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys.Taylor

def Tw (R : Type) {B B₀ : Type} [CommRing B] [CommRing B₀] (_p : B →+* B₀) (M : Type) : Type := M

section Tw

variable {R B B₀ M : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B₀] (p : B →+* B₀)
  [AddCommGroup M] [Module B₀ M]

instance : AddCommGroup (Tw R p M) := inferInstanceAs (AddCommGroup M)

instance : Module B (Tw R p M) := Module.compHom M p

instance : Module Bᵐᵒᵖ (Tw R p M) := Module.compHom M (p.comp ((RingHom.id B).fromOpposite mul_comm))

instance : IsCentralScalar B (Tw R p M) := ⟨fun _ _ ↦ rfl⟩

instance : Module R (Tw R p M) := Module.compHom M (p.comp (algebraMap R B))

instance : IsScalarTower R B (Tw R p M) := ⟨fun r b m ↦ by
  change p (r • b) • (show M from m) = p (algebraMap R B r) • p b • (show M from m)
  rw [Algebra.smul_def, map_mul, mul_smul]⟩

instance : IsScalarTower R Bᵐᵒᵖ (Tw R p M) := ⟨fun r b m ↦ by
  change p (r • b.unop) • (show M from m) = p (algebraMap R B r) • p b.unop • (show M from m)
  rw [Algebra.smul_def, map_mul, mul_smul]⟩

theorem smul_def (b : B) (m : Tw R p M) : b • m = (p b • (show M from m) : M) := rfl

end Tw

section Ext

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {X₀ : Scheme.{0}} {π : R →+* R₀}
  {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) (hI : I ^ 2 = 0) (U : AffOp X₀)

abbrev M : Type := Tw R (S.p U) Ω[Sec s₀ U.unop.1⁄R₀]

abbrev E : Type := TrivSqZeroExt (S.F.obj U) (M S U)

def red : E S U →+* Sec s₀ U.unop.1 := (S.p U).comp (TrivSqZeroExt.fstHom R (S.F.obj U) (M S U) : E S U →+* S.F.obj U)

theorem red_sq (hI : I ^ 2 = 0) : RingHom.ker (red S U) ^ 2 = 0 := by
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  have ha' : S.p U a.fst = 0 := ha
  have hb' : S.p U b.fst = 0 := hb
  have h1 : a.fst * b.fst = 0 := by
    have := Ideal.mul_mem_mul ((S.ker U _).1 ha') ((S.ker U _).1 hb')
    rwa [← pow_two, map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  rw [Ideal.mem_bot]
  ext
  · exact h1
  · change (S.p U a.fst • (show Ω[Sec s₀ U.unop.1⁄R₀] from b.snd) + S.p U b.fst • (show Ω[Sec s₀ U.unop.1⁄R₀] from a.snd) : Ω[Sec s₀ U.unop.1⁄R₀]) = 0
    rw [ha', hb', zero_smul, zero_smul, add_zero]

@[reducible] def thickE : Thick (divided₂ hI) (s₀ ≫ spMap π) where
  B := E S U
  J := RingHom.ker (red S U)
  δ := divided₂ (red_sq S U hI)
  nil := isDPNilpotent_squareZero _
  dp := isDPMorphism_sqDP hI _ _ fun a ha ↦ by
    change S.p U (algebraMap R (S.F.obj U) a) = 0
    exact (S.ker U _).2 (Ideal.mem_map_of_mem _ ha)
  B₀ := Sec s₀ U.unop.1
  π := red S U
  surj b := by
    obtain ⟨c, rfl⟩ := S.surj U b
    exact ⟨TrivSqZeroExt.inl c, rfl⟩
  ker _ := Iff.rfl
  x := affPt s₀ U.unop
  w := (S.thickObj hI U).w.trans (congrArg spMap (RingHom.ext fun _ ↦ rfl))

end Ext

section Homs

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {X₀ : Scheme.{0}} {π : R →+* R₀}
  {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) (hI : I ^ 2 = 0) (U : AffOp X₀)

def derP : Derivation R (S.F.obj U) (M S U) :=
  Derivation.mk'
    { toFun := fun b ↦ (D R₀ (Sec s₀ U.unop.1) (S.p U b) : Ω[Sec s₀ U.unop.1⁄R₀])
      map_add' := fun a b ↦ by simp only [map_add]; rfl
      map_smul' := fun r b ↦ by
        change D R₀ (Sec s₀ U.unop.1) (S.p U (r • b)) =
          S.p U (algebraMap R (S.F.obj U) r) • D R₀ (Sec s₀ U.unop.1) (S.p U b)
        rw [Algebra.smul_def, map_mul, Derivation.leibniz, (S.semi U).map_algebraMap,
          Derivation.map_algebraMap, smul_zero, add_zero] }
    fun a b ↦ by
      change D R₀ (Sec s₀ U.unop.1) (S.p U (a * b)) =
        S.p U a • D R₀ (Sec s₀ U.unop.1) (S.p U b) + S.p U b • D R₀ (Sec s₀ U.unop.1) (S.p U a)
      rw [map_mul, Derivation.leibniz]

theorem derP_apply (b : S.F.obj U) :
    (derP S U b : Ω[Sec s₀ U.unop.1⁄R₀]) = D R₀ (Sec s₀ U.unop.1) (S.p U b) := rfl

def inlHom : S.thickObj hI U ⟶ thickE S hI U where
  φ := TrivSqZeroExt.inlAlgHom R (S.F.obj U) (M S U)
  φ₀ := RingHom.id _
  comm _ := rfl
  dp := isDPMorphism_sqDP (map_sq hI _) (red_sq S U hI) _ fun b hb ↦
    show S.p U b = 0 from (S.ker U b).2 hb
  pt := by
    change spMap (RingHom.id _) ≫ affPt s₀ U.unop = affPt s₀ U.unop
    rw [spMap_id, Category.id_comp]

def derHom : S.thickObj hI U ⟶ thickE S hI U where
  φ := derSec (derP S U)
  φ₀ := RingHom.id _
  comm b := by
    change S.p U b = S.p U (derSec (derP S U) b).fst
    rw [fst_derSec]
  dp := isDPMorphism_sqDP (map_sq hI _) (red_sq S U hI) _ fun b hb ↦ by
    change S.p U (derSec (derP S U) b).fst = 0
    rw [fst_derSec]
    exact (S.ker U b).2 hb
  pt := by
    change spMap (RingHom.id _) ≫ affPt s₀ U.unop = affPt s₀ U.unop
    rw [spMap_id, Category.id_comp]

def fstHom : thickE S hI U ⟶ S.thickObj hI U where
  φ := TrivSqZeroExt.fstHom R (S.F.obj U) (M S U)
  φ₀ := RingHom.id _
  comm _ := rfl
  dp := isDPMorphism_sqDP (red_sq S U hI) (map_sq hI _) _ fun c hc ↦ (S.ker U _).1 hc
  pt := by
    change spMap (RingHom.id _) ≫ affPt s₀ U.unop = affPt s₀ U.unop
    rw [spMap_id, Category.id_comp]

end Homs

section More

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {X₀ : Scheme.{0}} {π : R →+* R₀}
  {s₀ : X₀ ⟶ Sp R₀} (S S' : Sys I π s₀) (hI : I ^ 2 = 0) (U V : AffOp X₀)

theorem mul_eq_zero_of_mem {B : Type} [CommRing B] {J : Ideal B} (hJ : J ^ 2 = 0) {a b : B} (ha : a ∈ J)
    (hb : b ∈ J) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rwa [← pow_two, hJ, Ideal.zero_eq_bot, Ideal.mem_bot] at this

variable {S S' hI U V}

def psiAlg {α β : S.F.obj U →ₐ[R] S'.F.obj V} {θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V}
    (hθ : IsTheta I (S.p U) α β θ) : E S U →ₐ[R] S'.F.obj V where
  toFun c := β c.fst + θ c.snd
  map_one' := by
    change β 1 + θ 0 = 1
    rw [map_one, map_zero, add_zero]
  map_zero' := by
    change β 0 + θ 0 = 0
    rw [map_zero, map_zero, add_zero]
  map_add' x y := by
    change β (x.fst + y.fst) + θ ((show Ω[Sec s₀ U.unop.1⁄R₀] from x.snd) + (show Ω[Sec s₀ U.unop.1⁄R₀] from y.snd)) = _
    rw [map_add, map_add]; abel
  map_mul' x y := by
    change β (x.fst * y.fst) + θ ((S.p U x.fst • (show Ω[Sec s₀ U.unop.1⁄R₀] from y.snd)) +
      S.p U y.fst • (show Ω[Sec s₀ U.unop.1⁄R₀] from x.snd)) = (β x.fst + θ x.snd) * (β y.fst + θ y.snd)
    have hI' := map_sq hI (S'.F.obj V)
    rw [map_add, hθ.smul, hθ.smul, map_mul]
    have ex := hθ.der x.fst
    have ey := hθ.der y.fst
    have z1 := mul_eq_zero_of_mem hI' (hθ.mem (D R₀ _ (S.p U x.fst))) (hθ.mem y.snd)
    have z2 := mul_eq_zero_of_mem hI' (hθ.mem (D R₀ _ (S.p U y.fst))) (hθ.mem x.snd)
    have z3 := mul_eq_zero_of_mem hI' (hθ.mem x.snd) (hθ.mem y.snd)
    linear_combination z1 + z2 - z3 - (θ y.snd) * ex - (θ x.snd) * ey
  commutes' r := by
    change β (algebraMap R (S.F.obj U) r) + θ 0 = _
    rw [map_zero, add_zero, β.commutes]

def psiHom (α β : S.thickObj hI U ⟶ S'.thickObj hI V) (θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V)
    (hθ : IsTheta I (S.p U) α.φ β.φ θ) : thickE S hI U ⟶ S'.thickObj hI V where
  φ := psiAlg (hI := hI) hθ
  φ₀ := β.φ₀
  comm c := by
    change β.φ₀ (S.p U c.fst) = S'.p V (β.φ c.fst + θ (show Ω[Sec s₀ U.unop.1⁄R₀] from c.snd))
    rw [map_add, (S'.ker V _).2 (hθ.mem _), add_zero]
    exact β.comm c.fst
  dp := isDPMorphism_sqDP (red_sq S U hI) (map_sq hI _) _ fun c hc ↦
    add_mem (β.mem (T := S.thickObj hI U) ((S.ker U _).1 hc)) (hθ.mem _)
  pt := β.pt

variable (S hI U)

def chiRing : E S U →+* TrivSqZeroExt (Sec s₀ U.unop.1) Ω[Sec s₀ U.unop.1⁄R₀] where
  toFun c := ((S.p U c.fst, (show Ω[Sec s₀ U.unop.1⁄R₀] from c.snd)) :
    TrivSqZeroExt (Sec s₀ U.unop.1) Ω[Sec s₀ U.unop.1⁄R₀])
  map_one' := by
    ext
    · exact map_one (S.p U)
    · rfl
  map_zero' := by
    ext
    · exact map_zero (S.p U)
    · rfl
  map_add' x y := by
    ext
    · exact map_add (S.p U) _ _
    · rfl
  map_mul' x y := by
    ext
    · exact map_mul (S.p U) _ _
    · rfl

theorem fst_chiRing (c : E S U) : (chiRing S U c).fst = S.p U c.fst := rfl

theorem snd_chiRing (c : E S U) : (chiRing S U c).snd = (show Ω[Sec s₀ U.unop.1⁄R₀] from c.snd) := rfl

variable {hI}

def chiHom (hk : RingHom.ker π = I) : thickE S hI U ⟶ (redMor hI hk s₀).obj
    ((diagExt R₀ (Sec s₀ U.unop.1)).thick (affPt s₀ U.unop) (affPt_w s₀ U.unop)) where
  φ := { chiRing S U with
    commutes' := fun r ↦ by
      change chiRing S U (algebraMap R (E S U) r) = algebraMap R₀ _ (π r)
      ext
      · rw [fst_chiRing]
        exact (S.semi U).map_algebraMap r
      · rw [snd_chiRing]; rfl }
  φ₀ := RingHom.id _
  comm c := (fst_chiRing S U c).symm
  dp := isDPMorphism_sqDP (red_sq S U hI) (diagExt R₀ (Sec s₀ U.unop.1)).sq _ fun c hc ↦ by
    change (chiRing S U c).fst = 0
    rw [fst_chiRing]; exact hc
  pt := by
    change spMap (RingHom.id _) ≫ affPt s₀ U.unop = affPt s₀ U.unop ≫ 𝟙 X₀
    rw [spMap_id, Category.id_comp, Category.comp_id]

def redHom (hk : RingHom.ker π = I) : S.thickObj hI U ⟶ (redMor hI hk s₀).obj
    (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop)) where
  φ := { S.p U with commutes' := fun r ↦ (S.semi U).map_algebraMap r }
  φ₀ := RingHom.id _
  comm _ := rfl
  dp := by
    have z : ∀ a ∈ I.map (algebraMap R (S.F.obj U)), S.p U a = 0 := fun a ha ↦ (S.ker U a).2 ha
    refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ z a ha, fun n hn a ha ↦ ?_⟩
    show (dp0 (Sec s₀ U.unop.1)).dpow n (S.p U a) = S.p U ((divided₂ (map_sq hI (S.F.obj U))).dpow n a)
    rw [z a ha, z _ ((divided₂ (map_sq hI _)).dpow_mem hn ha), dpow_eval_zero _ hn]
  pt := by
    change spMap (RingHom.id _) ≫ affPt s₀ U.unop = affPt s₀ U.unop ≫ 𝟙 X₀
    rw [spMap_id, Category.id_comp, Category.comp_id]

end More

section Main

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

theorem ev_sub_ev_eq : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀),
    ∀ (S S' : Sys I π s₀) (U V : AffOp X₀),
    (∃ Q : S.thickObj hI U ⟶ (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop)
        (affPt_w s₀ U.unop)), ∀ b, Q.φ b = S.p U b) ∧
    ∀ (Q : S.thickObj hI U ⟶ (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop)
        (affPt_w s₀ U.unop))), (∀ b, Q.φ b = S.p U b) →
    ∀ (α β : S.thickObj hI U ⟶ S'.thickObj hI V) (θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V),
    IsTheta I (S.p U) α.φ β.φ θ → ∀ f : Z1 (O (divided₂ hI) (s₀ ≫ spMap π)),
    ev f β - ev f α = θ (connForm ((redMor hI hk s₀).coef.pullbackOneCocycle f) (affPt s₀ U.unop) (affPt_w s₀ U.unop) -
      D R₀ (Sec s₀ U.unop.1) (ev f Q : Sec s₀ U.unop.1)) := by
  intro R R₀ _ _ I hI π _ hk X₀ s₀ S S' U V
  refine ⟨⟨redHom S U hk, fun _ ↦ rfl⟩, ?_⟩
  intro Q hQ α β θ hθ f
  let mi := (redMor hI hk s₀).functor.map ((diagExt R₀ (Sec s₀ U.unop.1)).secHom (affPt_w s₀ U.unop)
    (diagExt R₀ (Sec s₀ U.unop.1)).i fun _ ↦ rfl)
  let md := (redMor hI hk s₀).functor.map ((diagExt R₀ (Sec s₀ U.unop.1)).secHom (affPt_w s₀ U.unop)
    (diagSec R₀ (Sec s₀ U.unop.1)) (fst_derSec _))
  let ψ := psiHom α β θ hθ
  have k1 := ev_sq f (inlHom S hI U) (chiHom S U hk) Q mi fun c ↦ by
    rw [hQ]; rfl
  have k2 := ev_sq f (derHom S hI U) (chiHom S U hk) Q md fun c ↦ by
    rw [hQ]
    refine TrivSqZeroExt.ext ?_ ?_
    · change S.p U (derSec (derP S U) c).fst = (diagSec R₀ (Sec s₀ U.unop.1) (S.p U c)).fst
      rw [fst_derSec, fst_derSec]
    · change (show Ω[Sec s₀ U.unop.1⁄R₀] from (derSec (derP S U) c).snd) =
        (diagSec R₀ (Sec s₀ U.unop.1) (S.p U c)).snd
      rw [snd_derSec, snd_derSec]; rfl
  have k3 := ev_sq f (inlHom S hI U) (fstHom S hI U) (derHom S hI U) (fstHom S hI U) fun c ↦
    (fst_derSec (derP S U) c).symm
  have e1 : ev f β = ψ.φ (ev f (inlHom S hI U)) + ev f ψ := by
    rw [← ev_comp]
    congr 1
    refine Thick.hom_ext fun b ↦ ?_
    change β.φ b = β.φ b + θ 0
    rw [map_zero, add_zero]
  have e2 : ev f α = ψ.φ (ev f (derHom S hI U)) + ev f ψ := by
    rw [← ev_comp]
    congr 1
    refine Thick.hom_ext fun b ↦ ?_
    change α.φ b = β.φ (derSec (derP S U) b).fst + θ (show Ω[Sec s₀ U.unop.1⁄R₀] from (derSec (derP S U) b).snd)
    rw [fst_derSec, snd_derSec, derP_apply, hθ.der]
    abel
  have hc : connForm ((redMor hI hk s₀).coef.pullbackOneCocycle f) (affPt s₀ U.unop) (affPt_w s₀ U.unop) =
      (ev f mi - ev f md).snd := rfl
  have hA : ev f (inlHom S hI U) - ev f (derHom S hI U) = TrivSqZeroExt.inr
      (show M S U from connForm ((redMor hI hk s₀).coef.pullbackOneCocycle f) (affPt s₀ U.unop) (affPt_w s₀ U.unop) -
        D R₀ (Sec s₀ U.unop.1) (ev f Q : Sec s₀ U.unop.1)) := by
    ext
    · change (ev f (inlHom S hI U)).fst - (ev f (derHom S hI U)).fst = 0
      change (ev f (inlHom S hI U)).fst + ev f (fstHom S hI U) =
        (ev f (derHom S hI U)).fst + ev f (fstHom S hI U) at k3
      rw [add_left_inj] at k3
      rw [k3, sub_self]
    · have l1 := congrArg TrivSqZeroExt.snd k1
      have l2 := congrArg TrivSqZeroExt.snd k2
      change (show Ω[Sec s₀ U.unop.1⁄R₀] from (ev f (inlHom S hI U)).snd) + TrivSqZeroExt.snd (ev f (chiHom S U hk)) =
        (0 : Ω[Sec s₀ U.unop.1⁄R₀]) + TrivSqZeroExt.snd (ev f mi) at l1
      change (show Ω[Sec s₀ U.unop.1⁄R₀] from (ev f (derHom S hI U)).snd) + TrivSqZeroExt.snd (ev f (chiHom S U hk)) =
        (diagSec R₀ (Sec s₀ U.unop.1) (ev f Q : Sec s₀ U.unop.1)).snd + TrivSqZeroExt.snd (ev f md) at l2
      rw [show (diagSec R₀ (Sec s₀ U.unop.1) (ev f Q : Sec s₀ U.unop.1)).snd =
        D R₀ (Sec s₀ U.unop.1) (ev f Q : Sec s₀ U.unop.1) from snd_derSec _ _] at l2
      change (show Ω[Sec s₀ U.unop.1⁄R₀] from (ev f (inlHom S hI U)).snd) -
        (show Ω[Sec s₀ U.unop.1⁄R₀] from (ev f (derHom S hI U)).snd) = _
      rw [hc]
      change (show Ω[Sec s₀ U.unop.1⁄R₀] from (ev f (inlHom S hI U)).snd) -
        (show Ω[Sec s₀ U.unop.1⁄R₀] from (ev f (derHom S hI U)).snd) =
        (TrivSqZeroExt.snd (ev f mi) - TrivSqZeroExt.snd (ev f md)) - D R₀ (Sec s₀ U.unop.1) (ev f Q : Sec s₀ U.unop.1)
      have key : ∀ a b c d e q : Ω[Sec s₀ U.unop.1⁄R₀], a + e = 0 + c → b + e = q + d → a - b = c - d - q :=
        fun a b c d e q h1 h2 ↦ by linear_combination (norm := abel1) h1 - h2
      exact key _ _ _ _ _ _ l1 l2
  rw [e1, e2, add_sub_add_right_eq_sub, ← map_sub, hA]
  change β.φ 0 + θ _ = _
  rw [map_zero, zero_add]
  rfl

end Main

end GlobalTheory.LiftSys.Taylor
