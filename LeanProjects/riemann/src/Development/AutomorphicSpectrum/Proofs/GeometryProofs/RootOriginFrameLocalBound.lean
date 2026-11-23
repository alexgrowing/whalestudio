import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FrameValue

set_option backward.isDefEq.respectTransparency false

open Limits MonObj

section Grp

variable {S S' T T' : Scheme.{0}}

theorem one_left_pull {G : CategoryTheory.Over S} [GrpObj G] (a : T' ⟶ T) (x : T ⟶ S) (x' : T' ⟶ S) (h : a ≫ x = x') :
    a ≫ (1 : CategoryTheory.Over.mk x ⟶ G).left = (1 : CategoryTheory.Over.mk x' ⟶ G).left := by
  subst h
  exact congrArg (fun q => q.left) (comp_one (M := G) (CategoryTheory.Over.homMk a rfl : CategoryTheory.Over.mk (a ≫ x) ⟶ CategoryTheory.Over.mk x))

theorem one_left_grp {G' : CategoryTheory.Over S'} [GrpObj G'] {G : CategoryTheory.Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (x' : T ⟶ S') (x : T ⟶ S) (e : x' ≫ f = x) :
    (1 : CategoryTheory.Over.mk x' ⟶ G').left ≫ φ = (1 : CategoryTheory.Over.mk x ⟶ G).left := by
  subst e
  have hw : ((1 : CategoryTheory.Over.mk x' ⟶ G').left ≫ φ) ≫ G.hom = (CategoryTheory.Over.mk (x' ≫ f)).hom := by
    have h1 := CategoryTheory.Over.w (1 : CategoryTheory.Over.mk x' ⟶ G')
    rw [Category.assoc, h.1.w, ← Category.assoc, h1]
    rfl
  let x₀ : CategoryTheory.Over.mk (x' ≫ f) ⟶ G := CategoryTheory.Over.homMk _ hw
  have h2 := h.2 (CategoryTheory.Over.mk x') 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h2
  have h3 : x₀ * x₀ = x₀ := CategoryTheory.Over.OverMorphism.ext h2
  have h4 : x₀ = 1 := mul_eq_left.1 h3
  exact congrArg (fun q => q.left) h4

end Grp

section Ring

theorem exists_factor {O' R Ω C : Type} [CommRing O'] [CommRing R] [CommRing Ω] [CommRing C] (g : O' →+* Ω)
    (cl : O' →+* C) (hg : Function.Injective g) (φ : R →+* Ω) (ψ : R →+* C)
    (h : ∀ r, ∃ s, g s = φ r ∧ cl s = ψ r) : ∃ θ : R →+* O', g.comp θ = φ ∧ cl.comp θ = ψ := by
  choose θ h1 h2 using h
  exact ⟨{ toFun := θ
           map_one' := hg (by simp [h1])
           map_mul' := fun a b => hg (by simp [h1])
           map_zero' := hg (by simp [h1])
           map_add' := fun a b => hg (by simp [h1]) }, RingHom.ext h1, RingHom.ext h2⟩

theorem spec_dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (a : R →+* R') (b : R' →+* R'') :
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap b) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap a) = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (b.comp a)) := by
  rw [LieTangent.spec_comp]
  congr 2
  refine RingHom.ext fun t => ?_
  ext <;> simp

theorem spec_fst_alg (R : Type) [CommRing R] :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [LieTangent.spec_comp]
  have e1 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext a; simp
  rw [e1, CommRingCat.ofHom_id, Spec.map_id]

theorem pts_eq {O' Ω R₀ : Type} [CommRing O'] [Field Ω] [CommRing R₀] (g : O' →+* Ω) (hg : Function.Injective g)
    {B : Scheme.{0}} (s : B ⟶ Sp R₀) [IsSeparated s] {a b : Sp O' ⟶ B} (h : spMap g ≫ a = spMap g ≫ b) : a = b := by
  haveI : IsDomain O' := hg.isDomain g
  haveI : IsDominant (spMap g) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot g).1 hg]
    exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated s ?_ (spMap g) h
  refine ext_of_isDominant (spMap g) ?_
  rw [← Category.assoc, h, Category.assoc]

end Ring

section Lift

variable {X B : Scheme.{0}} {G : CategoryTheory.Over X} [GrpObj G] {G₀ : CategoryTheory.Over B} [GrpObj G₀] {f : X ⟶ B} {φ : G.left ⟶ G₀.left}

theorem exists_tan_lift (hc : IsGrpPullback G G₀ f φ) {O' R : Type} [CommRing O'] [CommRing R]
    (x : Sp O' ⟶ X) (θ : R →+* O') (P : Sp R ⟶ B) (t : Sp (DualNumber R) ⟶ G₀.left)
    (ht : t ≫ G₀.hom = spMap (algebraMap R (DualNumber R)) ≫ P)
    (h1 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t = (1 : CategoryTheory.Over.mk P ⟶ G₀).left)
    (he : x ≫ f = spMap θ ≫ P) :
    ∃ v : epsAt x ⟶ G, GlobalTheory.CompanionTheory.Ar.IsTanAt G x v ∧ v.left ≫ φ = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ t := by
  have hw : (spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ t) ≫ G₀.hom =
      (spMap (algebraMap O' (DualNumber O')) ≫ x) ≫ f := by
    rw [Category.assoc, ht, ← Category.assoc, LieTangent.spec_dual_alg, Category.assoc, Category.assoc, he]
  have l1 := hc.1.lift_fst _ _ hw
  have l2 := hc.1.lift_snd _ _ hw
  refine ⟨CategoryTheory.Over.homMk (hc.1.lift _ _ hw) l2, ?_, l1⟩
  show spMap (TrivSqZeroExt.fstHom O' O' O').toRingHom ≫ hc.1.lift _ _ hw = (1 : CategoryTheory.Over.mk x ⟶ G).left
  refine hc.1.hom_ext ?_ ?_
  · rw [Category.assoc, l1, ← Category.assoc, LieTangent.spec_fst_dual, Category.assoc, h1,
      one_left_pull _ P _ he.symm, one_left_grp hc x _ rfl]
  · rw [Category.assoc, l2, ← Category.assoc, spec_fst_alg, Category.id_comp]
    exact (CategoryTheory.Over.w (1 : CategoryTheory.Over.mk x ⟶ G)).symm

theorem extends_of (hc : IsGrpPullback G G₀ f φ) {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (M : LieModel G ξ E) (p : Cpt ξ) (e : E)
    (v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G)
    (hv : GlobalTheory.CompanionTheory.Ar.IsTanAt G _ v)
    (h : (M.pt e).left ≫ φ = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (genMap ξ p))) ≫ v.left ≫ φ) :
    M.Extends p e v := by
  refine ⟨hv, hc.1.hom_ext (h.trans (Category.assoc _ _ _).symm) ?_⟩
  have h2 : (M.pt e).left ≫ G.hom = spMap (algebraMap Ω (DualNumber Ω)) ≫ ξ := CategoryTheory.Over.w (M.pt e)
  have h3 : v.left ≫ G.hom = spMap (algebraMap (X.presheaf.stalk p.1) (DualNumber (X.presheaf.stalk p.1))) ≫
    X.fromSpecStalk p.1 := CategoryTheory.Over.w v
  have h4 : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (genMap ξ p))) ≫ v.left) ≫ G.hom =
      spMap (algebraMap Ω (DualNumber Ω)) ≫ ξ := by
    rw [Category.assoc, h3, ← Category.assoc, LieTangent.spec_dual_alg, Category.assoc, LieTangent.spec_genMap]
  exact h2.trans h4.symm

end Lift

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
  {S : Type} [CommRing S] [Algebra c.F S]

theorem tanY_one (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ Small.tanY Y y τ i =
      (1 : CategoryTheory.Over.mk (Small.ptY Y y) ⟶ Y.t.G).left := by
  have a : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ Small.tanF Y y τ i =
      (1 : CategoryTheory.Over.mk (Small.ptF y) ⟶ Y.oF.t.G).left := by
    refine Y.m0.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, Small.tanF_φ, (y.tan τ i).2]
      exact (one_left_grp Y.m0.cart (Small.ptF y) y.x (Small.ptF_fst y)).symm
    · rw [Category.assoc, Small.tanF_hom, ← Category.assoc, spec_fst_alg, Category.id_comp]
      exact (CategoryTheory.Over.w (1 : CategoryTheory.Over.mk (Small.ptF y) ⟶ Y.oF.t.G)).symm
  rw [Small.tanY, ← Category.assoc, a]
  exact one_left_grp Y.m.cart (Small.ptF y) (Small.ptY Y y) rfl

end Model

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FrameValue

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

open FrameValue in
set_option maxHeartbeats 600000 in

theorem frame_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)), ∃ w : EC, FinRd.Roots.IsFrameVec Or io zT MC w s i ∧ Or.𝔐.M.ValAt (FinRd.Roots.gen T zV) (Or.Fl.b s i) (MC.pt w) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hv hG la T io e y evT zT t hI zV hR EC _ _ MC s i
  letI := io.toAlgebra
  letI := Small.cstAlg Or
  obtain ⟨-, -, -, -, -, -, ⟨q, φ, ψ, yq, hφ, hψ, hr⟩, -⟩ := hI
  have hgen : genPt Or.𝔐.ξ ⤳ centre (gen T zV) := Or.𝔐.all _
  let P : Cpt Or.𝔐.ξ := ⟨centre (gen T zV), hgen⟩
  have hinj : Function.Injective (genMap Or.𝔐.ξ P) := Or.𝔐.tie.gen.inj P
  have hreg : ∀ r, ∃ s', genMap Or.𝔐.ξ P s' = φ.toRingHom r ∧
      (Scheme.stalkClosedPointTo (gen T zV)).hom s' = ψ.toRingHom r := fun r => by
    obtain ⟨h, e'⟩ := hr r
    obtain ⟨h', s', hs, hs'⟩ := hR ⟨φ r, h⟩
    exact ⟨s', hs, hs'.trans e'.symm⟩
  obtain ⟨θ, hθ1, hθ2⟩ := exists_factor _ _ hinj φ.toRingHom ψ.toRingHom hreg
  have hsep : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have he : Or.𝔐.X.fromSpecStalk P.1 ≫ Or.𝔐.f = spMap θ ≫ Small.ptY Y yq := by
    refine pts_eq (genMap Or.𝔐.ξ P) hinj Y.s ?_
    rw [← Category.assoc, ← Category.assoc]
    have e1 : spMap (genMap Or.𝔐.ξ P) ≫ Or.𝔐.X.fromSpecStalk P.1 = Or.𝔐.ξ := LieTangent.spec_genMap _ _
    rw [e1, ← Fr.pt_eq, Small.ptY_map Y hφ, ← hθ1, LieTangent.spec_comp]
  obtain ⟨v, hvt, hv'⟩ := exists_tan_lift Or.𝔐.m.cart (Or.𝔐.X.fromSpecStalk P.1) θ (Small.ptY Y yq)
    (Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i)) (Small.tanY_hom Y _ _ _) (tanY_one Y _ _ _) he
  have hext : Or.𝔐.M.Extends P (Or.Fl.b s i) v := by
    refine extends_of Or.𝔐.m.cart _ P _ v hvt ?_
    have e2 := Small.tanY_map Y hφ (Small.labelC s) (Small.labelFin Dw s i)
    have e3 := Fr.tan_eq s i
    have e4 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap (genMap Or.𝔐.ξ P)) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫
          Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := by
      rw [← Category.assoc, spec_dual_comp, hθ1]
    exact e3.symm.trans (e2.trans (e4.trans (congrArg (fun u => _ ≫ u) hv'.symm)))
  have hb := LieTangent.isTanAt_base _ (LieTangent.spec_centre (gen T zV)) hvt
  obtain ⟨w, hw⟩ := MC.onto _ hb
  refine ⟨w, ?_, (Or.𝔐.M.valAt_iff _ _ _).2 ⟨hgen, v, hext, hw⟩⟩
  show (MC.pt w).left ≫ Or.𝔐.m.φ = Small.tanY Y zT (Small.labelC s) (Small.labelFin Dw s i)
  have e5 : (MC.pt w).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo (gen T zV)).hom) ≫ v.left :=
    congrArg (fun u => u.left) hw
  have e6 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo (gen T zV)).hom) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫
        Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := by
    have e7 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo (gen T zV)).hom) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) := (spec_dual_comp θ _).trans (by rw [hθ2])
    exact (congrArg (fun u => u ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i)) e7.symm).trans
      (Category.assoc _ _ _)
  rw [e5, Small.tanY_map Y hψ, e6]
  exact (Category.assoc _ _ _).trans (congrArg (fun u => _ ≫ u) hv')

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
