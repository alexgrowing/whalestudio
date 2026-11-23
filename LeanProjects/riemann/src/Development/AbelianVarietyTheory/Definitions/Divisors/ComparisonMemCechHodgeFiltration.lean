import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNilDPOfCube
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.StructureHomApply

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CechDR

open CatCoh Cris

universe v u v' u'

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

section Points

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}

theorem connForm_add {B : Type} [CommRing B] [Algebra R B] (f g : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)) :
    connForm (f + g) x hx = connForm f x hx + connForm g x hx :=
  (congrArg (TrivSqZeroExt.snd (R := B))
    (add_sub_add_comm (α := TrivSqZeroExt B Ω[B⁄R]) _ _ _ _)).trans (TrivSqZeroExt.snd_add _ _)

theorem connForm_smul {B : Type} [CommRing B] [Algebra R B] (r : R) (f : Z1 (O (dp0 R) s))
    (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) :
    connForm (r • f) x hx = r • connForm f x hx :=
  (congrArg (TrivSqZeroExt.snd (R := B))
    (smul_sub r (_ : TrivSqZeroExt B Ω[B⁄R]) _).symm).trans (TrivSqZeroExt.snd_smul _ _)

theorem connForm_algHom {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (α : B →ₐ[R] B') (f : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B))
    (x' : Sp B' ⟶ X) (hx' : x' ≫ s = spMap (algebraMap R B')) (e : spMap (α : B →+* B') ≫ x = x') :
    connForm f x' hx' = (SemiHom.of_algHom α).m1 (connForm f x hx) +
      D R B' (ev f (Thick.trivHom (hx := hx) (T := Thick.triv B' x' hx') α e)) := by
  letI : Algebra B B' := (α : B →+* B').toAlgebra
  haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r ↦ (α.commutes r).symm
  rw [SemiHom.oneFormMap_eq_kaehlerDifferential_map _ fun _ ↦ rfl]
  exact eq_add_of_sub_eq' (connForm_map f x hx x' hx' e)

section Semi

variable {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R' B'] {α : B →+* B'}
  (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (ha : SemiHom σ α)
  {x : Sp B ⟶ X} (hx : x ≫ s = spMap (algebraMap R B))
  {x' : Sp B' ⟶ X'} (hx' : x' ≫ s' = spMap (algebraMap R' B')) (e : spMap α ≫ x = x' ≫ φ)

def semiTriv : Thick.triv B x hx ⟶ h.obj (Thick.triv B' x' hx') :=
  Thick.trivHom { α with commutes' := ha.map_algebraMap } e

def semiDiag : TrivSqZeroExt B Ω[B⁄R] →+* TrivSqZeroExt B' Ω[B'⁄R'] where
  toFun c := TrivSqZeroExt.inl (α c.fst) + TrivSqZeroExt.inr (ha.m1 c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp

theorem fst_semiDiag (c : TrivSqZeroExt B Ω[B⁄R]) : (semiDiag ha c).fst = α c.fst := add_zero _

theorem snd_semiDiag (c : TrivSqZeroExt B Ω[B⁄R]) : (semiDiag ha c).snd = ha.m1 c.snd := zero_add _

def semiDiagHom : (diagExt R B).thick x hx ⟶ h.obj ((diagExt R' B').thick x' hx') where
  φ := { semiDiag ha with
    commutes' := fun r ↦ by
      change semiDiag ha (algebraMap R _ r) = algebraMap R' _ (σ r)
      ext
      · rw [fst_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl', ha.map_algebraMap]
      · rw [snd_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl'] }
  φ₀ := α
  comm c := (fst_semiDiag ha c).symm
  dp := isDPMorphism_sqDP (diagExt R B).sq (diagExt R' B').sq _ fun a ha' ↦ by
    have h0 : a.fst = 0 := ha'
    change (semiDiag ha a).fst = 0
    rw [fst_semiDiag, h0, map_zero]
  pt := e

theorem connForm_pull (f : Z1 (O (dp0 R) s)) :
    connForm (h.coef.pullbackOneCocycle f) x' hx' =
      ha.m1 (connForm f x hx) + D R' B' (ev f (semiTriv h ha hx hx' e)) := by
  have k1 := ev_sq f (semiTriv h ha hx hx' e)
    (h.functor.map ((diagExt R' B').secHom hx' (diagExt R' B').i fun _ ↦ rfl))
    ((diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl) (semiDiagHom h ha hx hx' e) fun c ↦
      TrivSqZeroExt.ext (fst_semiDiag ha (TrivSqZeroExt.inl c)).symm
        ((snd_semiDiag ha (TrivSqZeroExt.inl c)).trans (map_zero _)).symm
  have k2 := ev_sq f (semiTriv h ha hx hx' e)
    (h.functor.map ((diagExt R' B').secHom hx' (diagSec R' B') (fst_derSec _)))
    ((diagExt R B).secHom hx (diagSec R B) (fst_derSec _)) (semiDiagHom h ha hx hx' e) fun c ↦ by
      change diagSec R' B' (α c) = semiDiag ha (diagSec R B c)
      ext
      · rw [fst_semiDiag, fst_derSec, fst_derSec]
      · rw [snd_semiDiag, snd_derSec, snd_derSec, SemiHom.m1_D]
  have l1 := congrArg (TrivSqZeroExt.snd (R := B')) k1
  have l2 := congrArg (TrivSqZeroExt.snd (R := B')) k2
  change 0 + _ = (semiDiag ha _).snd + _ at l1
  change (diagSec R' B' (ev f (semiTriv h ha hx hx' e))).snd + _ = (semiDiag ha _).snd + _ at l2
  rw [snd_semiDiag] at l1 l2
  have l3 : (diagSec R' B' (ev f (semiTriv h ha hx hx' e))).snd = D R' B' (ev f (semiTriv h ha hx hx' e)) :=
    snd_derSec _ _
  rw [l3] at l2
  simp only [connForm, TrivSqZeroExt.snd_sub, map_sub]
  have key : ∀ a b c d e f : Ω[B'⁄R'], 0 + a = c + e → f + b = d + e → a - b = c - d + f :=
    fun a b c d e f h1 h2 ↦ by linear_combination (norm := abel1) h1 - h2
  exact key _ _ _ _ _ _ l1 l2

end Semi

variable {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (x : ∀ T : C, Sp (F.obj T) ⟶ X) (hx : ∀ T, x T ≫ s = spMap (algebraMap R (F.obj T)))
  (hc : ∀ ⦃T T' : C⦄ (a : T ⟶ T'), spMap (mp F a : F.obj T →+* F.obj T') ≫ x T = x T')

def ptFunctor : C ⥤ (IsTriv s).FullSubcategory where
  obj T := ⟨Thick.triv (F.obj T) (x T) (hx T), rfl⟩
  map {T T'} a := ⟨Thick.trivHom (T := Thick.triv (F.obj T') (x T') (hx T')) (mp F a) (hc a)⟩
  map_id T := ObjectProperty.hom_ext _ (Thick.hom_ext (mp_id F T))
  map_comp a b := ObjectProperty.hom_ext _ (Thick.hom_ext (mp_comp F a b))

def ptCoef : CoefMap (RingHom.id R) ((IsTriv s).ι ⋙ O (dp0 R) s) F where
  G := ptFunctor x hx hc
  α T := RingHom.id (F.obj T)
  naturality _ _ := rfl
  smul _ _ _ := rfl

def ptZZ : Z1 (O (dp0 R) s) →ₗ[R] cechDeRhamTotalCocyclesOne F where
  toFun f := ⟨(fun _ _ a ↦ ev f ((ptFunctor x hx hc).map a).hom, fun T ↦ connForm f (x T) (hx T)),
    mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨fun T T' T'' a b ↦ by
      change ev f ((ptFunctor x hx hc).map (a ≫ b)).hom = _
      rw [Functor.map_comp]
      exact ev_comp f _ _,
      fun T T' a ↦ connForm_algHom (mp F a) f _ _ _ _ (hc a), fun T ↦ dOne_connForm f _ _⟩⟩
  map_add' f g := Subtype.ext (Tot1.ext (fun _ _ _ ↦ rfl) fun T ↦ connForm_add f g _ _)
  map_smul' r f := Subtype.ext (Tot1.ext (fun _ _ _ ↦ rfl) fun T ↦ connForm_smul r f _ _)

def ptCmp : FirstDeRham s →ₗ[R] Hyp1 F :=
  Submodule.mapQ _ _ (ptZZ x hx hc) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨fun T ↦ g (Thick.triv (F.obj T) (x T) (hx T)),
      Subtype.ext (Tot1.ext (fun _ _ _ ↦ rfl) fun T ↦ (crystallineConnectionForm_coboundaryZero g _ _).symm)⟩)

theorem pullHyp1_ptCmp {C' : Type u'} [Category.{v'} C'] {F' : C' ⥤ CommAlgCat.{0} R'}
    (x' : ∀ T : C', Sp (F'.obj T) ⟶ X') (hx' : ∀ T, x' T ≫ s' = spMap (algebraMap R' (F'.obj T)))
    (hc' : ∀ ⦃T T' : C'⦄ (a : T ⟶ T'), spMap (mp F' a : F'.obj T →+* F'.obj T') ≫ x' T = x' T')
    (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (m : CoefMap σ F F')
    (e : ∀ T, spMap (m.α T) ≫ x (m.G.obj T) = x' T ≫ φ) (c : FirstDeRham s) :
    pullHyp1 m (ptCmp x hx hc c) = ptCmp x' hx' hc' (h.pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  let g : Tot0 F' := fun T ↦ ev f (semiTriv h (semiHom_coef m T) (hx _) (hx' T) (e T))
  refine Hyp1.mk_eq_mk.2 ⟨-g, (map_neg _ g).trans (Tot1.ext (fun T T' a ↦ ?_) fun T ↦ ?_)⟩
  · have k := ev_sq f (semiTriv h (semiHom_coef m T) (hx _) (hx' T) (e T))
      (h.functor.map ((ptFunctor x' hx' hc').map a).hom) ((ptFunctor x hx hc).map (m.G.map a)).hom
      (semiTriv h (semiHom_coef m T') (hx _) (hx' T') (e T')) fun b ↦ (m.naturality a b).symm
    have key : ∀ a b c d : F'.obj T', a + b = c + d → -(d - a) = c - b :=
      fun a b c d h1 ↦ by linear_combination h1
    exact key _ _ _ _ k
  · have k := connForm_pull h (semiHom_coef m T) (hx _) (hx' T) (e T) f
    have key : ∀ a b c : Ω[F'.obj T⁄R'], a = b + c → -c = b - a :=
      fun a b c h1 ↦ by rw [h1]; abel
    exact key _ _ _ k

end Points

def Sec (_s : X ⟶ Sp R) (U : X.Opens) : Type := GlobalTheory.SectionsCommRing.Sections _s U

def secMap (s : X ⟶ Sp R) (U : X.Opens) : CommRingCat.of R ⟶ Γ(X, U) :=
  CommRingCat.ofHom (GlobalTheory.SectionsCommRing.structureHom s U)

instance (s : X ⟶ Sp R) (U : X.Opens) : CommRing (Sec s U) := inferInstanceAs (CommRing Γ(X, U))

instance (s : X ⟶ Sp R) (U : X.Opens) : Algebra R (Sec s U) :=
  RingHom.toAlgebra (S := Sec s U) (secMap s U).hom

def Sec.res (s : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) : Sec s U →ₐ[R] Sec s V :=
  GlobalTheory.SectionsCommRing.Sections.restrict s h

theorem Sec.res_res (s : X ⟶ Sp R) {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (c : Sec s U) :
    Sec.res s (h'.trans h) c = Sec.res s h' (Sec.res s h c) :=
  congrArg (fun q ↦ q.hom c) (X.presheaf.map_comp (homOfLE h).op (homOfLE h').op)

abbrev AffOp (X : Scheme.{0}) : Type := (X.affineOpens)ᵒᵖ

@[reducible] def OAff (s : X ⟶ Sp R) : AffOp X ⥤ CommAlgCat.{0} R where
  obj U := CommAlgCat.of R (Sec s U.unop.1)
  map a := CommAlgCat.ofHom (Sec.res s (leOfHom a.unop))
  map_id U := CommAlgCat.hom_ext (AlgHom.ext fun b ↦
    congrArg (fun q ↦ q.hom b) (X.presheaf.map_id (op U.unop.1)))
  map_comp a b := CommAlgCat.hom_ext (AlgHom.ext fun c ↦
    Sec.res_res s (leOfHom a.unop) (leOfHom b.unop) c)

abbrev OmU (s : X ⟶ Sp R) (U : X.Opens) (j : ℕ) : Type := Om R (Sec s U) j

abbrev HH1 (s : X ⟶ Sp R) : Type := Hyp1 (OAff s)

abbrev HH2 (s : X ⟶ Sp R) : Type := Hyp2 (OAff s)

abbrev cupHH (s : X ⟶ Sp R) : HH1 s →ₗ[R] HH1 s →ₗ[R] HH2 s := cupHyp (OAff s)

abbrev HO1 (s : X ⟶ Sp R) : Type := CatCoh.H1 (OAff s)

abbrev toHO1 (s : X ⟶ Sp R) : HH1 s →ₗ[R] HO1 s := toO (OAff s)

abbrev CechHodgeFiltration (s : X ⟶ Sp R) : Submodule R (HH1 s) := Fil1 (OAff s)

abbrev GlobForm (s : X ⟶ Sp R) : Submodule R (A0 (OAff s)) := Glob1 (OAff s)

abbrev ClosedForm (s : X ⟶ Sp R) : Submodule R (GlobForm s) := Closed1 (OAff s)

abbrev clForm (s : X ⟶ Sp R) : ClosedForm s →ₗ[R] HH1 s := ofForm (OAff s)

theorem cechHodgeFiltration_eq_range (s : X ⟶ Sp R) : CechHodgeFiltration s = LinearMap.range (clForm s) := Fil1_eq_range _

def affPt (s : X ⟶ Sp R) (U : X.affineOpens) : Sp (Sec s U.1) ⟶ X := U.2.fromSpec

theorem affPt_w (s : X ⟶ Sp R) (U : X.affineOpens) :
    affPt s U ≫ s = spMap (algebraMap R (Sec s U.1)) := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) U.2 le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at this
  exact this.symm

theorem affPt_res (s : X ⟶ Sp R) {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    spMap (Sec.res s h : Sec s U.1 →+* Sec s V.1) ≫ affPt s U = affPt s V :=
  IsAffineOpen.map_fromSpec U.2 V.2 (homOfLE h).op

def cmpZZ (s : X ⟶ Sp R) : Z1 (O (dp0 R) s) →ₗ[R] cechDeRhamTotalCocyclesOne (OAff s) :=
  ptZZ (F := OAff s) (fun U ↦ affPt s U.unop) (fun U ↦ affPt_w s U.unop)
    fun _ _ a ↦ affPt_res s (leOfHom a.unop)

theorem cmpZZ_ω (s : X ⟶ Sp R) (f : Z1 (O (dp0 R) s)) (U : AffOp X) :
    (cmpZZ s f).1.2 U = connForm f (affPt s U.unop) (affPt_w s U.unop) := rfl

theorem cmpZZ_f (s : X ⟶ Sp R) (f : Z1 (O (dp0 R) s)) {U V : AffOp X} (a : U ⟶ V) :
    (cmpZZ s f).1.1 U V a = ev f (Thick.trivHom (hx := affPt_w s U.unop)
      (T := Thick.triv _ _ (affPt_w s V.unop)) (Sec.res s (leOfHom a.unop))
      (affPt_res s (leOfHom a.unop))) := rfl

def cmp1 (s : X ⟶ Sp R) : FirstDeRham s →ₗ[R] HH1 s :=
  ptCmp (F := OAff s) (fun U ↦ affPt s U.unop) (fun U ↦ affPt_w s U.unop)
    fun _ _ a ↦ affPt_res s (leOfHom a.unop)

theorem comparison_mk (s : X ⟶ Sp R) (f : Z1 (O (dp0 R) s)) :
    cmp1 s (H1.mk _ f) = Hyp1.mk _ (cmpZZ s f) := rfl

def cmpO (s : X ⟶ Sp R) : FirstCohomStructureSheaf s →ₗ[R] HO1 s :=
  (ptCoef (F := OAff s) (fun U ↦ affPt s U.unop) (fun U ↦ affPt_w s U.unop)
    fun _ _ a ↦ affPt_res s (leOfHom a.unop)).pull1

theorem structureSheaf_comparison_comm (s : X ⟶ Sp R) (c : FirstDeRham s) : toHO1 s (cmp1 s c) = cmpO s (toH1O s c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c; rfl

theorem comparison_mem_cechHodgeFiltration (s : X ⟶ Sp R) {c : FirstDeRham s} (hc : c ∈ F1 s) : cmp1 s c ∈ CechHodgeFiltration s := by
  change toHO1 s (cmp1 s c) = 0
  rw [structureSheaf_comparison_comm, show toH1O s c = 0 from hc, map_zero]

def cmpForm (s : X ⟶ Sp R) : Form s →ₗ[R] ClosedForm s where
  toFun f := ⟨⟨(cmpZZ s f.1).1.2, fun U V a ↦ by
    rw [cechDeRhamTotalCocyclesOne.conn _ a, show (cmpZZ s f.1).1.1 U V a = 0 from f.2 _ rfl rfl, map_zero, add_zero]⟩,
    cechDeRhamTotalCocyclesOne.closed (cmpZZ s f.1)⟩
  map_add' f g := Subtype.ext (Subtype.ext (funext fun _ ↦ connForm_add f.1 g.1 _ _))
  map_smul' r f := Subtype.ext (Subtype.ext (funext fun _ ↦ connForm_smul r f.1 _ _))

theorem cmpForm_apply (s : X ⟶ Sp R) (f : Form s) (U : AffOp X) :
    (cmpForm s f).1.1 U = connForm f.1 (affPt s U.unop) (affPt_w s U.unop) := rfl

theorem comparison_formClass (s : X ⟶ Sp R) (f : Form s) : cmp1 s (Form.cl s f) = clForm s (cmpForm s f) :=
  congrArg (Hyp1.mk _) (Subtype.ext (Tot1.ext (fun _ _ _ ↦ f.2 _ rfl rfl) fun _ ↦ rfl))

section Pull

abbrev Pair (φ : X' ⟶ X) : Type :=
  {p : X'.affineOpens × X.affineOpens // p.1.1 ≤ φ ⁻¹ᵁ p.2.1}

theorem Pair.le_fst {φ : X' ⟶ X} {p q : Pair φ} (h : p ≤ q) : p.1.1 ≤ q.1.1 :=
  (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1

theorem Pair.le_snd {φ : X' ⟶ X} {p q : Pair φ} (h : p ≤ q) : p.1.2 ≤ q.1.2 :=
  (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2

def pairFst (φ : X' ⟶ X) : (Pair φ)ᵒᵖ ⥤ AffOp X' :=
  (Monotone.functor (f := fun p : Pair φ ↦ p.1.1) fun _ _ h ↦ Pair.le_fst h).op

def pairSnd (φ : X' ⟶ X) : (Pair φ)ᵒᵖ ⥤ AffOp X :=
  (Monotone.functor (f := fun p : Pair φ ↦ p.1.2) fun _ _ h ↦ Pair.le_snd h).op

abbrev OPair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : (Pair φ)ᵒᵖ ⥤ CommAlgCat.{0} R' := pairFst φ ⋙ OAff s'

def pairRes (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OAff s') (OPair φ s') :=
  CoefMap.restrict _ _

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}

def secPull (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (p : Pair φ) : Sec s p.1.2.1 →+* Sec s' p.1.1.1 :=
  (φ.appLE _ _ p.2).hom

theorem secPull_affPt (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (p : Pair φ) :
    spMap (secPull s s' p) ≫ affPt s p.1.2 = affPt s' p.1.1 ≫ φ :=
  IsAffineOpen.SpecMap_appLE_fromSpec φ p.1.2.2 p.1.1.2 p.2

theorem semiHom_secPull (h : φ ≫ s = s' ≫ spMap σ) (p : Pair φ) : SemiHom σ (secPull s s' p) := by
  have e : spMap ((secPull s s' p).comp (algebraMap R _)) = spMap ((algebraMap R' _).comp σ) := by
    rw [spMap_comp, spMap_comp, ← affPt_w, ← affPt_w, ← Category.assoc, secPull_affPt,
      Category.assoc, h, Category.assoc]
  intro r b
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  exact congrArg (· * _) (congrArg (fun q ↦ q.hom r) (Spec.map_injective e))

def pairPull (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (OAff s) (OPair φ s') where
  G := pairSnd φ
  α p := secPull s s' p.unop
  naturality {p q} a b :=
    (congrArg (fun t ↦ t.hom b) (φ.map_appLE q.unop.2 (homOfLE (Pair.le_snd (leOfHom a.unop))).op)).trans
      (congrArg (fun t ↦ t.hom b) (φ.appLE_map p.unop.2 (homOfLE (Pair.le_fst (leOfHom a.unop))).op)).symm
  smul p := semiHom_secPull h p.unop

variable (h : φ ≫ s = s' ≫ spMap σ)

def IsPull1 (c : HH1 s) (c' : HH1 s') : Prop := pullHyp1 (pairPull h) c = pullHyp1 (pairRes φ s') c'

def IsPull2 (c : HH2 s) (c' : HH2 s') : Prop := pullHyp2 (pairPull h) c = pullHyp2 (pairRes φ s') c'

def IsPullO (c : HO1 s) (c' : HO1 s') : Prop := (pairPull h).pull1 c = (pairRes φ s').pull1 c'

def IsPullForm (ω : GlobForm s) (ω' : GlobForm s') : Prop :=
  pullGlob1 (pairPull h) ω = pullGlob1 (pairRes φ s') ω'

variable {h}

theorem isPullForm_iff {ω : GlobForm s} {ω' : GlobForm s'} : IsPullForm h ω ω' ↔
    ∀ p : Pair φ, (semiHom_secPull h p).m1 (ω.1 (op p.1.2)) = ω'.1 (op p.1.1) := by
  have k : ∀ p : (Pair φ)ᵒᵖ, (pullGlob1 (pairRes φ s') ω').1 p = ω'.1 (op p.unop.1.1) := fun p ↦
    cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) p (ω'.1 (op p.unop.1.1))
  have k' : ∀ p : (Pair φ)ᵒᵖ, (pullGlob1 (pairPull h) ω).1 p =
      (semiHom_secPull h p.unop).m1 (ω.1 (op p.unop.1.2)) := fun p ↦ rfl
  refine ⟨fun e p ↦ ?_, fun e ↦ Subtype.ext (funext fun p ↦ ?_)⟩
  · exact (k' (op p)).symm.trans
      ((congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 (op p)) e).trans (k (op p)))
  · exact (k' p).trans ((e p.unop).trans (k p).symm)

theorem IsPull1.zero : IsPull1 h 0 0 := (map_zero _).trans (map_zero _).symm

theorem IsPull1.add {a b : HH1 s} {a' b' : HH1 s'} (ha : IsPull1 h a a') (hb : IsPull1 h b b') :
    IsPull1 h (a + b) (a' + b') := by
  unfold IsPull1 at *; rw [map_add, map_add, ha, hb]

theorem IsPull1.smul {a : HH1 s} {a' : HH1 s'} (ha : IsPull1 h a a') (r : R) :
    IsPull1 h (r • a) (σ r • a') := by
  unfold IsPull1 at *; rw [map_smulₛₗ, map_smulₛₗ, ha]; rfl

theorem IsPull2.zero : IsPull2 h 0 0 := (map_zero _).trans (map_zero _).symm

theorem IsPull2.add {a b : HH2 s} {a' b' : HH2 s'} (ha : IsPull2 h a a') (hb : IsPull2 h b b') :
    IsPull2 h (a + b) (a' + b') := by
  unfold IsPull2 at *; rw [map_add, map_add, ha, hb]

theorem IsPull2.smul {a : HH2 s} {a' : HH2 s'} (ha : IsPull2 h a a') (r : R) :
    IsPull2 h (r • a) (σ r • a') := by
  unfold IsPull2 at *; rw [map_smulₛₗ, map_smulₛₗ, ha]; rfl

theorem IsPull1.cup {a b : HH1 s} {a' b' : HH1 s'} (ha : IsPull1 h a a') (hb : IsPull1 h b b') :
    IsPull2 h (cupHH s a b) (cupHH s' a' b') := by
  unfold IsPull1 IsPull2 at *; rw [pullHyp2_cup, pullHyp2_cup, ha, hb]

theorem IsPull1.toO {a : HH1 s} {a' : HH1 s'} (ha : IsPull1 h a a') :
    IsPullO h (toHO1 s a) (toHO1 s' a') := by
  unfold IsPull1 IsPullO at *; rw [← toO_pullHyp1, ← toO_pullHyp1, ha]

theorem IsPullForm.cl {ω : ClosedForm s} {ω' : ClosedForm s'} (e : IsPullForm h ω.1 ω'.1) :
    IsPull1 h (clForm s ω) (clForm s' ω') := by
  unfold IsPull1
  rw [pullHyp1_ofForm, pullHyp1_ofForm]
  exact congrArg _ (Subtype.ext e)

theorem comparison_pullback (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (c : FirstDeRham s) :
    IsPull1 h.w (cmp1 s c) (cmp1 s' (h.pull1 c)) := by
  let x' : ∀ p : (Pair φ)ᵒᵖ, Sp ((OPair φ s').obj p) ⟶ X' := fun p ↦ affPt s' p.unop.1.1
  have hx' : ∀ p, x' p ≫ s' = spMap (algebraMap R' ((OPair φ s').obj p)) := fun p ↦ affPt_w s' _
  have hc' : ∀ ⦃p q : (Pair φ)ᵒᵖ⦄ (a : p ⟶ q), spMap (mp (OPair φ s') a : _ →+* _) ≫ x' p = x' q :=
    fun _ _ a ↦ affPt_res s' (Pair.le_fst (leOfHom a.unop))
  refine (pullHyp1_ptCmp _ _ _ x' hx' hc' h (pairPull h.w) (fun p ↦ secPull_affPt s s' p.unop) c).trans ?_
  refine ((pullHyp1_ptCmp _ _ _ x' hx' hc' (IsMor.id _ s') (pairRes φ s') (fun p ↦ ?_) _).trans ?_).symm
  · change spMap (RingHom.id _) ≫ _ = _
    rw [spMap_id, Category.id_comp, Category.comp_id]; rfl
  · rw [IsMor.pullCohomologyOne_id]

def pairIdTrans (X : Scheme.{0}) : pairSnd (𝟙 X) ⟶ pairFst (𝟙 X) where
  app p := (homOfLE (show p.unop.1.1 ≤ p.unop.1.2 from p.unop.2)).op

theorem isPull1_id (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HH1 s) : IsPull1 h c c :=
  pullHyp1_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X) (fun _ _ ↦ rfl) c

theorem isPull2_id (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HH2 s) : IsPull2 h c c :=
  pullHyp2_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X) (fun _ _ ↦ rfl) c

end Pull

section Affine

variable (R) (B : Type) [CommRing B] [Algebra R B]

abbrev algStr : Sp B ⟶ Sp R := spMap (algebraMap R B)

theorem affPt_eq (U : (Sp B).affineOpens) :
    affPt (algStr R B) U = Spec.map (secMap (𝟙 (Sp B)) U.1) :=
  (Category.comp_id _).symm.trans (affPt_w (𝟙 (Sp B)) U)

def toSec (U : (Sp B).affineOpens) : B →ₐ[R] Sec (algStr R B) U.1 :=
  { (secMap (𝟙 (Sp B)) U.1).hom with
    commutes' := fun r ↦ by
      have e : Spec.map (CommRingCat.ofHom (algebraMap R B) ≫ secMap (𝟙 (Sp B)) U.1) =
          spMap (algebraMap R (Sec (algStr R B) U.1)) := (Spec.map_comp _ _).trans
        ((congrArg (· ≫ algStr R B) (affPt_eq R B U)).symm.trans (affPt_w _ U))
      exact congrArg (fun q ↦ q.hom r) (Spec.map_injective e) }

theorem res_toSec ⦃U V : AffOp (Sp B)⦄ (a : U ⟶ V) (b : B) :
    mp (OAff (algStr R B)) a (toSec R B U.unop b) = toSec R B V.unop b :=
  (Sec.res (𝟙 (Sp B)) (leOfHom a.unop)).commutes b

def affEquiv : AlgebraFirstDeRham R B ≃ₗ[R] HH1 (algStr R B) :=
  LinearEquiv.ofBijective (coneMap (F := OAff (algStr R B)) (fun U ↦ toSec R B U.unop) (res_toSec R B))
    (coneMap_bijective _ _ (T₀ := op ⟨⊤, isAffineOpen_top _⟩)
      (Limits.IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, isAffineOpen_top _⟩ from
        le_top (a := U.unop.1))).op) fun _ _ ↦ rfl)
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv))

theorem affEquiv_mk (ω : LinearMap.ker (dOne R B)) : affEquiv R B (Submodule.Quotient.mk ω) =
    clForm _ (coneForm (F := OAff (algStr R B)) (fun U ↦ toSec R B U.unop) (res_toSec R B) ω) := rfl

open Polynomial

theorem dOne_line (ω : Ω[R[X]⁄R]) : dOne R R[X] ω = 0 := by
  induction ω using ind1 with
  | h b c =>
    rw [dOne_smul_D, polynomial_D_apply R b, polynomial_D_apply R c]
    simp
  | h0 => simp
  | ha x y hx hy => rw [map_add, hx, hy, add_zero]

def lineEquiv : (Ω[R[X]⁄R] ⧸ LinearMap.range (D R R[X]).toLinearMap) ≃ₗ[R] HH1 (lineStr R) :=
  (Submodule.Quotient.equiv (exact1 R R[X]) _
    (LinearEquiv.ofTop _ (eq_top_iff.2 fun ω _ ↦ dOne_line R ω)) (by
      ext ω
      exact ⟨fun ⟨x, hx, e⟩ ↦ e ▸ hx, fun hω ↦ ⟨⟨ω, dOne_line R ω⟩, hω, rfl⟩⟩)).symm.trans
    (affEquiv R R[X])

theorem lineEquiv_mk (ω : Ω[R[X]⁄R]) : lineEquiv R (Submodule.Quotient.mk ω) =
    affEquiv R R[X] (Submodule.Quotient.mk ⟨ω, dOne_line R ω⟩) := rfl

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler in
variable {R B} in

theorem connForm_tdt (x : Sp B ⟶ Sp R[X]) (hx : x ≫ lineStr R = spMap (algebraMap R B)) :
    connForm (tdt R).1 x hx =
      (Spec.preimage x).hom Polynomial.X • D R B ((Spec.preimage x).hom Polynomial.X) := by
  have c0 : coordLift (Thick.triv B x hx) = (Spec.preimage x).hom Polynomial.X :=
    π_coordLift (Thick.triv B x hx)
  have c1 : (coordLift ((diagExt R B).thick x hx)).fst = (Spec.preimage x).hom Polynomial.X :=
    π_coordLift ((diagExt R B).thick x hx)
  change TrivSqZeroExt.snd (R := B) ((TrivSqZeroExt.inl (coordLift (Thick.triv B x hx)) *
    (_ - TrivSqZeroExt.inl (coordLift (Thick.triv B x hx))) + (divided₂ (diagExt R B).sq).dpow 2 _) -
    (diagSec R B (coordLift (Thick.triv B x hx)) * (_ - diagSec R B (coordLift (Thick.triv B x hx))) +
      (divided₂ (diagExt R B).sq).dpow 2 _)) = _
  rw [squareZeroDividedPowers_dpow _ le_rfl, squareZeroDividedPowers_dpow _ le_rfl, c0]
  have key : ∀ (c : TrivSqZeroExt B Ω[B⁄R]) (b : B), c.fst = b →
      TrivSqZeroExt.snd ((TrivSqZeroExt.inl b * (c - TrivSqZeroExt.inl b) + 0) -
        (diagSec R B b * (c - diagSec R B b) + 0)) = b • D R B b := by
    intro c b h
    simp [h, smul_sub]
  exact key _ _ c1

theorem comparison_tdt_line : cmp1 (lineStr R) (Form.cl _ (tdt R)) =
    lineEquiv R (Submodule.Quotient.mk ((Polynomial.X : R[X]) • D R R[X] Polynomial.X)) := by
  rw [comparison_formClass, lineEquiv_mk, affEquiv_mk]
  refine congrArg _ (Subtype.ext (Subtype.ext (funext fun U ↦ ?_)))
  rw [cmpForm_apply, connForm_tdt, coneForm_apply, SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D]
  have : Spec.preimage (affPt (lineStr R) U.unop) = secMap (𝟙 (Sp R[X])) U.unop.1 := by
    rw [affPt_eq]; exact Spec.preimage_map _
  rw [this]; rfl

example (r : R) (h : r * 2 = 1) : cmp1 (lineStr R) (Form.cl _ (tdt R)) = 0 := by
  rw [comparison_tdt_line, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  refine ⟨r • (Polynomial.X * Polynomial.X), ?_⟩
  rw [map_smul, Derivation.coeFn_coe, Derivation.leibniz, ← two_smul R, smul_smul, h, one_smul]

end Affine

end GlobalTheory.CechDR
