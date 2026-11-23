import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ActGeneratorZero
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CompListProd
import Development.WeilBound.CoreStatements.HodgeTatePoints.CdChart
import Development.WeilBound.CoreStatements.HodgeTatePoints.CdFrame
import Development.WeilBound.CoreStatements.HodgeTatePoints.Comp1IdentityLeft
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace PositivityTheory.Xgn.GermSystem

section Alg
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw comp1)
open PositivityTheory.HtPt.Ca
variable {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ}

theorem lin_inv {φ ψ : Pt R 1 d} (hψ : Z ψ) (h : comp1 φ ψ = pt R (n := 1) d 0) : lin φ 1 * lin ψ 1 = 1 := by
  rw [← lin_comp1 φ hψ, h, lin_pt_eq_one]

theorem transH_comp {φ ψ φ' ψ' : Pt R 1 d} {lam lam' : PS R 2 d} (hφ' : Z φ') (hψ : Z ψ) (hl : AxOne lam)
    (hl' : AxOne lam') (hi : lin φ' 1 * lin ψ' 1 = 1) :
    transH (comp1 φ φ') (comp1 ψ' ψ) (lam' * ev (n := 2) ![comp1 φ' (pt R d 0), comp1 φ' (pt R d 1)] lam) =
      transH φ ψ lam ∘ₗ transH φ' ψ' lam' := by
  refine LinearMap.ext fun y => ?_
  have ht : (lin ψ' 1).transpose * (lin φ' 1).transpose = 1 := by
    rw [← Matrix.transpose_mul, hi, Matrix.transpose_one]
  rw [LinearMap.comp_apply, transH_apply, transH_apply, transH_apply, lin_comp1 φ hφ', lin_comp1 ψ' hψ,
    bil_mul_left hl' (axOne_comp hl hφ' hφ'), bil_comp hl hφ' hφ']
  refine Prod.ext (by simp only [Matrix.mulVec_mulVec]) ?_
  simp only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_transpose, Matrix.mulVec_add,
    Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (lin ψ' 1).transpose (lin φ' 1).transpose, ht, Matrix.one_mul, add_assoc]

theorem transH_surj {φ ψ : Pt R 1 d} (lam : PS R 2 d) (hi : lin φ 1 * lin ψ 1 = 1) :
    Function.Surjective (transH φ ψ lam) := fun y => by
  have ht : (lin ψ 1).transpose * (lin φ 1).transpose = 1 := by
    rw [← Matrix.transpose_mul, hi, Matrix.transpose_one]
  refine ⟨((lin ψ 1).mulVec y.1, (lin φ 1).transpose.mulVec y.2 - (bil lam 1 1).transpose.mulVec ((lin ψ 1).mulVec y.1)), ?_⟩
  rw [transH_apply]
  simp only [sub_add_cancel, Matrix.mulVec_mulVec, hi, ht, Matrix.one_mulVec]

theorem transH_map (f : R →+* R') (φ ψ : Pt R 1 d) (lam : PS R 2 d) (y : (Fin d → R) × (Fin d → R)) :
    transH (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i)) (MvPowerSeries.map f lam)
      (fun i => f (y.1 i), fun i => f (y.2 i)) =
      (fun i => f ((transH φ ψ lam y).1 i), fun i => f ((transH φ ψ lam y).2 i)) := by
  rw [transH_apply, transH_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [Matrix.mulVec, dotProduct, lin, bil, MvPowerSeries.coeff_map]

theorem stdLat_comp {Ω : Type} [Field Ω] (f : R →+* Ω) {φ ψ : Pt R 1 d} (lam : PS R 2 d)
    (hi : lin φ 1 * lin ψ 1 = 1) (T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)) :
    stdLat f.range (T ∘ₗ transH (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i))
      (MvPowerSeries.map f lam)) = stdLat f.range T := by
  unfold stdLat
  congr 1
  ext y
  constructor
  · rintro ⟨y₀, h, rfl⟩
    choose a ha using fun i => (h i).1
    choose b hb using fun i => (h i).2
    have e : y₀ = (fun i => f ((a, b).1 i), fun i => f ((a, b).2 i)) :=
      Prod.ext (funext fun i => (ha i).symm) (funext fun i => (hb i).symm)
    refine ⟨_, ?_, rfl⟩
    rw [e, transH_map]
    exact fun i => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨y₀, h, rfl⟩
    choose a ha using fun i => (h i).1
    choose b hb using fun i => (h i).2
    obtain ⟨w, hw⟩ := transH_surj lam hi (a, b)
    refine ⟨(fun i => f (w.1 i), fun i => f (w.2 i)), fun i => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, ?_⟩
    rw [LinearMap.comp_apply, transH_map, hw]
    exact congrArg T (Prod.ext (funext fun i => (ha i).symm) (funext fun i => (hb i).symm))

theorem isMapOf_cancel {R₂ R₃ O : Type} [CommRing R₂] [CommRing R₃] [CommRing O] [StarRing O]
    {f : R →+* R₂} {g : R₂ →+* R₃} {B : Germ.FB R d O} {B₂ : Germ.FB R₂ d O} {B₃ : Germ.FB R₃ d O}
    (h : IsMapOf f B B₂) (h' : IsMapOf (g.comp f) B B₃) : IsMapOf g B₂ B₃ where
  F := fun i => by rw [h'.F, h.F, MvPowerSeries.map_comp]; rfl
  act := fun a i => by rw [h'.act, h.act, MvPowerSeries.map_comp]; rfl
  ph1 := by rw [h'.ph1, h.ph1, MvPowerSeries.map_comp]; rfl
  ph2 := by rw [h'.ph2, h.ph2, MvPowerSeries.map_comp]; rfl
  sy := by rw [h'.sy, h.sy, MvPowerSeries.map_comp]; rfl
  ad := fun a => by rw [h'.ad, h.ad, MvPowerSeries.map_comp]; rfl

theorem dualMap_comp {R₂ R₃ : Type} [CommRing R₂] [CommRing R₃] (f : R →+* R₂) (g : R₂ →+* R₃) :
    (GlobalTheory.CompanionTheory.Ar.dualMap g).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) = GlobalTheory.CompanionTheory.Ar.dualMap (g.comp f) := by
  ext r <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

end Alg

section Geo
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 PositivityTheory.HtPt.Cd
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd
open Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw comp1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X0 : Scheme.{0}}
  {t : SAB H X0} {S S₂ S₃ : Type} [CommRing S] [CommRing S₂] [CommRing S₃] {x : Sp S ⟶ X0} {x₂ : Sp S₂ ⟶ X0}
  {x₃ : Sp S₃ ⟶ X0} {d : ℕ}

theorem jetCoef_comp (f : S →+* S₂) (g : S₂ →+* S₃) (κ : Type) (m : ℕ) :
    (jetCoef g κ m).comp (jetCoef f κ m) = jetCoef (g.comp f) κ m := by
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, jetCoef_mk, MvPolynomial.map_map]

structure IsBC (f : S →+* S₂) (g : GermAt t x d) (g₂ : GermAt t x₂ d) : Prop where
  map : IsMapOf f g.B g₂.B
  tg : ∀ l, g₂.tg l = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l
  jet : ∀ m, (g₂.x m).left = spMap (jetCoef f (Fin 1 × Fin d) m) ≫ (g.x m).left
  fr : ∀ m (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet S₂ (Fin 2 × Fin d) m)) (z : Z) (J), Good t.PP.L z J →
    vE g₂ m r z J = vE g m (r ≫ spMap (jetCoef f (Fin 2 × Fin d) m)) z J

theorem exists_bc (f : S →+* S₂) (e : x₂ = spMap f ≫ x) (g : GermAt t x d) : ∃ g₂ : GermAt t x₂ d, IsBC f g g₂ := by
  subst e
  obtain ⟨e₂, h1, h2⟩ := Bc.exists_frBC t f x g.x g.e g.frame.gen
  exact ⟨⟨FBMap.mapFB f g.B, Bc.yBC t f x g.x, e₂, fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l,
    Bc.chart_bc t f x g.x g.chart, fun l => Bc.tan_bc t f x (g.tan l), Bc.basis_bc t f x g.tan g.basis,
    h2.frame h1 g.frame, h2.trunc g.trunc, h2.axes g.axes⟩,
    ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩, fun _ => rfl, fun _ => rfl, h2⟩

theorem IsBC.cancel {f : S →+* S₂} {k : S₂ →+* S₃} {g : GermAt t x d} {g₂ : GermAt t x₂ d} {g₃ : GermAt t x₃ d}
    (h : IsBC f g g₂) (h' : IsBC (k.comp f) g g₃) : IsBC k g₂ g₃ where
  map := isMapOf_cancel h.map h'.map
  tg l := by rw [h'.tg, h.tg, ← Category.assoc, Bc.spMap_cp, dualMap_comp]
  jet m := by rw [h'.jet, h.jet, ← jetCoef_comp, ← Bc.spMap_cp, Category.assoc]
  fr m Z r z J hJ := by
    rw [h'.fr m Z r z J hJ, h.fr m Z _ z J hJ, Category.assoc, Bc.spMap_cp, jetCoef_comp]

theorem IsBC.trans {f : S →+* S₂} {k : S₂ →+* S₃} {g : GermAt t x d} {g₂ : GermAt t x₂ d} {g₃ : GermAt t x₃ d}
    (h : IsBC f g g₂) (h' : IsBC k g₂ g₃) : IsBC (k.comp f) g g₃ where
  map := h.map.trans h'.map
  tg l := by rw [h'.tg, h.tg, ← Category.assoc, Bc.spMap_cp, dualMap_comp]
  jet m := by rw [h'.jet, h.jet, ← jetCoef_comp, ← Bc.spMap_cp, Category.assoc]
  fr m Z r z J hJ := by
    rw [h'.fr m Z r z J hJ, h.fr m Z _ z J hJ, Category.assoc, Bc.spMap_cp, jetCoef_comp]

structure Cmp (g g₂ : GermAt t x d) (φ ψ : Q S d 1) (lam : PS S 2 d) : Prop where
  hφ : ∀ m, g₂.x m = PP m g.x φ
  hψ : ∀ m, g.x m = PP m g₂.x ψ
  hl : LamEq g g₂ φ lam

theorem exists_cmp (g g₂ : GermAt t x d) : ∃ φ ψ lam, Cmp g g₂ φ ψ lam := by
  obtain ⟨φ, hφ⟩ := exists_coord g g₂
  obtain ⟨ψ, hψ⟩ := exists_coord g₂ g
  obtain ⟨lam, h⟩ := exists_lam hφ
  exact ⟨φ, ψ, lam, hφ, hψ, h⟩

def mQ (f : S →+* S₂) {n : ℕ} (u : Q S d n) : Q S₂ d n :=
  ⟨fun i => MvPowerSeries.map f (u.1 i), fun i => by
    rw [MvPowerSeries.constantCoeff_map, u.2 i, map_zero]⟩

theorem mQ_ac (f : S →+* S₂) {n : ℕ} (φ : Q S d 1) (j : Fin n) : mQ f (ac φ (gen j)) = ac (mQ f φ) (gen j) :=
  Subtype.ext (by
    rw [ac_val]
    have := FBMap.mp_comp1 f φ.1 (pt S d j) (gen j : Q S d n).2
    rw [FBMap.mp_pt] at this
    exact (congrArg (FBMap.mp f) (ac_val φ (gen j))).trans this)

theorem coef_jQ' (f : S →+* S₂) {k n : ℕ} (m : ℕ) (b : Fin k → Q S d n) :
    (jQ m (fun j => mQ f (b j)) : Jet S₂ (Fin k × Fin d) m →+* Jet S₂ (Fin n × Fin d) m).comp
      (jetCoef f (Fin k × Fin d) m) =
    (jetCoef f (Fin n × Fin d) m).comp (jQ m b : Jet S (Fin k × Fin d) m →+* Jet S (Fin n × Fin d) m) := by
  have e : (fun s : Fin k × Fin d => psTrunc m ((mQ f (b s.1)).1 s.2)) =
      fun s => MvPolynomial.map f (psTrunc m ((b s.1).1 s.2)) := funext fun s => psTrunc_map f m _
  have h : ∀ s : Fin k × Fin d, MvPolynomial.map f (psTrunc m ((b s.1).1 s.2)) ∈ orig S₂ (Fin n × Fin d) :=
    fun s => congrFun e s ▸ FBIdJet.psTrunc_mem_orig m _ ((mQ f (b s.1)).2 s.2)
  have e₂ : jQ m (fun j => mQ f (b j)) = jetMap _ h := by
    unfold jQ
    congr 1
  rw [e₂]
  exact (jetCoef_map f m _ _ h).symm

theorem coef_jQ (f : S →+* S₂) {k n : ℕ} (m : ℕ) (b : Fin k → Q S d n) (b' : Fin k → Q S₂ d n)
    (h : ∀ j, b' j = mQ f (b j)) :
    (homAt x₂ (jQ m b')).left ≫ spMap (jetCoef f (Fin k × Fin d) m) =
      spMap (jetCoef f (Fin n × Fin d) m) ≫ (homAt x (jQ m b)).left := by
  obtain rfl : b' = fun j => mQ f (b j) := funext h
  exact (Bc.spMap_cp _ _).trans ((congrArg spMap (coef_jQ' f m b)).trans (Bc.spMap_cp _ _).symm)

theorem PP_bc {f : S →+* S₂} {g g₂ : GermAt t x d} {g' g₂' : GermAt t x₂ d} (h : IsBC f g g') (h₂ : IsBC f g₂ g₂')
    {φ : Q S d 1} (hφ : ∀ m, g₂.x m = PP m g.x φ) (m : ℕ) : g₂'.x m = PP m g'.x (mQ f φ) := by
  apply Over.OverMorphism.ext
  rw [h₂.jet, hφ, PP, PP, Over.comp_left, Over.comp_left, h.jet, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ (g.x m).left) (coef_jQ f m ![φ] ![mQ f φ] fun j => by fin_cases j; rfl).symm

theorem Cmp.bc {f : S →+* S₂} {g g₂ : GermAt t x d} {g' g₂' : GermAt t x₂ d} (h : IsBC f g g') (h₂ : IsBC f g₂ g₂')
    {φ ψ : Q S d 1} {lam : PS S 2 d} (c : Cmp g g₂ φ ψ lam) :
    Cmp g' g₂' (mQ f φ) (mQ f ψ) (MvPowerSeries.map f lam) where
  hφ := PP_bc h h₂ c.hφ
  hψ := PP_bc h₂ h c.hψ
  hl m := by
    obtain ⟨U, hU, k⟩ := c.hl m
    refine ⟨Units.map (jetCoef f _ m).toMonoidHom U, by rw [← Bc.coef_psJet, ← hU]; rfl, fun Z r z J hJ => ?_⟩
    have e := coef_jQ (x := x) (x₂ := x₂) f m (bb φ) (bb (mQ f φ)) fun j => by
      fin_cases j <;> exact (mQ_ac f φ _).symm
    refine (h₂.fr m Z r z J hJ).trans ((k Z _ z J hJ).trans (congrArg₂ (· * ·) (Bc.gm_unit_bc f x U r z).symm ?_))
    refine Eq.trans ?_ (h.fr m Z _ z J hJ).symm
    exact congrArg (fun s => vE g m s z J) ((Category.assoc _ _ _).trans
      ((congrArg (r ≫ ·) e.symm).trans (Category.assoc _ _ _).symm))

theorem Cmp.iso (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {g g₂ : GermAt t x d} {φ ψ : Q S d 1}
    {lam : PS S 2 d} (c : Cmp g g₂ φ ψ lam) : GlobalTheory.CompanionTheory.Ar.Conj.IsIso g.B g₂.B φ.1 ψ.1 lam :=
  iso_of_coord c.hφ hs hp c.hψ c.hl

theorem Cmp.trans (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {g g₂ g₃ : GermAt t x d}
    {φ ψ φ' ψ' φ'' ψ'' : Q S d 1} {lam lam' lam'' : PS S 2 d} (c : Cmp g g₂ φ ψ lam) (c' : Cmp g₂ g₃ φ' ψ' lam')
    (c'' : Cmp g g₃ φ'' ψ'' lam'') : transH φ''.1 ψ''.1 lam'' = transH φ.1 ψ.1 lam ∘ₗ transH φ'.1 ψ'.1 lam' := by
  have e₁ : φ'' = ac φ φ' := PP_inj g fun m => by rw [← c''.hφ, ← PP_coord c.hφ, ← c'.hφ]
  have e₂ : ψ'' = ac ψ' ψ := PP_inj g₃ fun m => by rw [← c''.hψ, ← PP_coord c'.hψ, ← c.hψ]
  have e₃ : ∀ u : Q S d 2, ac φ'' u = ac φ (ac φ' u) := fun u => PP_inj g fun m => by
    rw [← PP_coord c''.hφ, ← PP_coord c.hφ, ← PP_coord c'.hφ]
  have e₄ : E2 lam'' (gen 0 : Q S d 2) (gen 1) =
      E2 lam' (gen 0) (gen 1) * E2 lam (ac φ' (gen 0)) (ac φ' (gen 1)) :=
    VV_ext (x0 := x) t.PP.isLB fun m y J hJ => by
      rw [VV_mul, c.hl.dL hJ, c'.hl.dL hJ, c''.hl.dL hJ, ← Units.val_mul, e₃, e₃, _root_.mul_assoc,
        inv_mul_cancel_left]
  rw [formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_eq_ev, ac_val, ac_val] at e₄
  rw [e₁, e₂, e₄, ac_val, ac_val]
  exact transH_comp φ'.2 ψ.2 (c.iso hs hp).ax (c'.iso hs hp).ax (lin_inv ψ'.2 (c'.iso hs hp).inv₁)

def lieM (g : GermAt t x d) : GlobalTheory.CompanionTheory.Ar.LieModel t.G x (Fin d → S) where
  pt v := (tanModel t x).pt (gd g v)
  tan v := (tanModel t x).tan _
  inj := (tanModel t x).inj.comp (gd_bij g).1
  onto v hv := by
    obtain ⟨e, he⟩ := (tanModel t x).onto v hv
    obtain ⟨w, rfl⟩ := (gd_bij g).2 e
    exact ⟨w, he⟩
  add v w := by rw [map_add, (tanModel t x).add]
  smul c v := by rw [map_smul, (tanModel t x).smul]

theorem germ_aff (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) (z : X0) :
    ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X0) (d : ℕ), IsOpenImmersion j ∧ z ∈ Set.range j ∧
      Nonempty (GermAt t j d) := by
  obtain ⟨S, _, x0, d, G, A, tg, x, c, hj, hz, hc, ht, hb, hU⟩ := chart_affine E H X0 t z
  obtain ⟨e, ph1, ph2, sy, ad, hfr, htr, hfa, had⟩ := frame_affine E H X0 t S x0 d G A tg _ x c hc hU
  obtain ⟨hax, hr⟩ := FBIdAd.fbId E H X0 t hp hs S x0 _ G A _ tg _ x e ph1 ph2 sy ad hc hfr hfa had
  exact ⟨S, _, x0, d, hj, hz, ⟨⟨mkFB G A ph1 ph2 sy ad hax hr, x, e, tg, hc, ht, hb, hfr, htr, hfa⟩⟩⟩

theorem exists_factor {R A : Type} [CommRing R] [IsLocalRing R] [CommRing A] {X : Scheme.{0}} (x : Sp R ⟶ X)
    (j : Sp A ⟶ X) [IsOpenImmersion j] (h : x (IsLocalRing.closedPoint R) ∈ Set.range j) :
    ∃ a : A →+* R, x = spMap a ≫ j := by
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint q).map x.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j x hr)).hom, ?_⟩
  show x = Spec.map (Spec.preimage (IsOpenImmersion.lift j x hr)) ≫ j
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

variable {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X0}

abbrev stPt (X0 : Scheme.{0}) (p : X0) : Sp (X0.presheaf.stalk p) ⟶ X0 := X0.fromSpecStalk p

theorem genMap_from (p : Cpt ξ) : ξ = spMap (genMap ξ p) ≫ stPt X0 p.1 := by
  obtain ⟨p, hp⟩ := p
  symm
  show Spec.map (X0.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ) ≫ X0.fromSpecStalk p = ξ
  exact (congrArg (· ≫ X0.fromSpecStalk p) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
    ((congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·)
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hp)).trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)))

theorem st_spec {p q : X0} (h : q ⤳ p) : stPt X0 q = spMap (X0.presheaf.stalkSpecializes h).hom ≫ stPt X0 p :=
  (Scheme.SpecMap_stalkSpecializes_fromSpecStalk h).symm

theorem genMap_comp (p q : Cpt ξ) (h : q.1 ⤳ p.1) :
    (genMap ξ q).comp (X0.presheaf.stalkSpecializes h).hom = genMap ξ p := by
  have e : spMap ((genMap ξ q).comp (X0.presheaf.stalkSpecializes h).hom) = spMap (genMap ξ p) := by
    haveI : Mono (stPt X0 p.1) := inferInstanceAs (Mono (X0.fromSpecStalk p.1))
    rw [← cancel_mono (stPt X0 p.1), ← Bc.spMap_cp, Category.assoc, ← st_spec h, ← genMap_from p, ← genMap_from q]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem eq_mul_inverse_pow {A : Type} [CommRing A] {j : Sp A ⟶ X0} [Mono j] {gA : GermAt t j d} {k : S →+* S₃} {k' : S₂ →+* S₃}
    {a : A →+* S} {a' : A →+* S₂} (ha : x = spMap a ≫ j) (ha' : x₂ = spMap a' ≫ j) (hk : x₃ = spMap k ≫ x)
    (hk' : x₃ = spMap k' ≫ x₂) {gK : GermAt t x₃ d} (hK : IsBC (k.comp a) gA gK) :
    ∃ g' : GermAt t x₂ d, IsBC k' g' gK := by
  obtain ⟨g', hb'⟩ := exists_bc a' ha' gA
  have e : spMap (k'.comp a') = spMap (k.comp a) := by
    rw [← cancel_mono j, ← Bc.spMap_cp, ← Bc.spMap_cp, Category.assoc, Category.assoc, ← ha, ← ha', ← hk, ← hk']
  have e' : k'.comp a' = k.comp a := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [← e'] at hK
  exact ⟨g', hb'.cancel hK⟩

theorem loc_aux₀ (hs : ∀ a : 𝓞 E, star a = H.bar a) [IsLocalRing S₃] {A : Type} [CommRing A] {j : Sp A ⟶ X0} {d' : ℕ}
    (gA : GermAt t j d') {k : S →+* S₃} {a : A →+* S} (ha : x = spMap a ≫ j) (hk : x₃ = spMap k ≫ x)
    (g₀ : GermAt t x₃ d) : d = d' ∧ ∃ gK : GermAt t x₃ d', IsBC (k.comp a) gA gK := by
  obtain ⟨gK, hK⟩ := exists_bc (x₂ := x₃) (k.comp a) (by rw [← Bc.spMap_cp, Category.assoc, ← ha, ← hk]) gA
  exact ⟨(germ_univ E H hs X0 t S₃ x₃ d g₀).1 d' gK, gK, hK⟩

theorem st_factor {A : Type} [CommRing A] (j : Sp A ⟶ X0) [IsOpenImmersion j] (q : X0) (hq : q ∈ Set.range j) :
    ∃ a : A →+* X0.presheaf.stalk q, stPt X0 q = spMap a ≫ j :=
  exists_factor _ j (by
    have : stPt X0 q (IsLocalRing.closedPoint _) = q := Scheme.fromSpecStalk_closedPoint
    exact this.symm ▸ hq)

theorem exists_loc (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) (g₀ : GermAt t ξ d) (p : Cpt ξ) :
    ∃ (gK : GermAt t ξ d) (U : X0.Opens), p.1 ∈ U ∧
      ∀ q : Cpt ξ, q.1 ∈ U → ∃ g' : GermAt t (stPt X0 q.1) d, IsBC (genMap ξ q) g' gK := by
  obtain ⟨A, _, j, d', _, hj, ⟨gA⟩⟩ := germ_aff hs hp p.1
  obtain ⟨a, ha⟩ := st_factor j p.1 hj
  obtain ⟨rfl, gK, hK⟩ := loc_aux₀ hs gA ha (genMap_from p) g₀
  refine ⟨gK, j.opensRange, hj, fun q hq => ?_⟩
  obtain ⟨b, hb⟩ := st_factor j q.1 hq
  exact eq_mul_inverse_pow ha hb (genMap_from p) (genMap_from q) hK

theorem key (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {f : S →+* S₂} {g g' : GermAt t x d}
    {g₀ gq gp : GermAt t x₂ d} (h : IsBC f g gq) (h' : IsBC f g' gp) {φ ψ φ'' ψ'' : Q S₂ d 1} {lam lam'' : PS S₂ 2 d}
    (c : Cmp g₀ gq φ ψ lam) (c'' : Cmp g₀ gp φ'' ψ'' lam'') :
    ∃ (φ' ψ' : Pt S 1 d) (lam' : PS S 2 d), GlobalTheory.CompanionTheory.Ar.Conj.IsIso g.B g'.B φ' ψ' lam' ∧
      transH φ''.1 ψ''.1 lam'' = transH φ.1 ψ.1 lam ∘ₗ
        transH (fun i => MvPowerSeries.map f (φ' i)) (fun i => MvPowerSeries.map f (ψ' i))
          (MvPowerSeries.map f lam') := by
  obtain ⟨φ', ψ', lam', c'⟩ := exists_cmp g g'
  have k := c.trans hs hp (c'.bc h h') c''
  have e : ∀ u : Q S d 1, (mQ f u).1 = fun i => MvPowerSeries.map f (u.1 i) := fun _ => rfl
  rw [e, e] at k
  exact ⟨φ'.1, ψ'.1, lam', c'.iso hs hp, k⟩

theorem key_gen (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {s : S₃ →+* S} (hx : x = spMap s ≫ x₃)
    {f : S →+* S₂} {k : S₃ →+* S₂} (hk : f.comp s = k) {g : GermAt t x d} {g₃ : GermAt t x₃ d}
    {g₀ gq gp : GermAt t x₂ d} (h : IsBC f g gq) (h' : IsBC k g₃ gp) {φ ψ φ'' ψ'' : Q S₂ d 1} {lam lam'' : PS S₂ 2 d}
    (c : Cmp g₀ gq φ ψ lam) (c'' : Cmp g₀ gp φ'' ψ'' lam'') :
    ∃ (B' : Germ.FB S d (𝓞 E)) (φ' ψ' : Pt S 1 d) (lam' : PS S 2 d), IsMapOf s g₃.B B' ∧
      GlobalTheory.CompanionTheory.Ar.Conj.IsIso g.B B' φ' ψ' lam' ∧
      transH φ''.1 ψ''.1 lam'' = transH φ.1 ψ.1 lam ∘ₗ
        transH (fun i => MvPowerSeries.map f (φ' i)) (fun i => MvPowerSeries.map f (ψ' i))
          (MvPowerSeries.map f lam') := by
  subst hk
  obtain ⟨g', hg'⟩ := exists_bc s hx g₃
  obtain ⟨φ', ψ', lam', h1, h2⟩ := key hs hp h (hg'.cancel h') c c''
  exact ⟨g'.B, φ', ψ', lam', hg'.map, h1, h2⟩

theorem key_loc (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {f : S →+* Ω} {g g' : GermAt t x d}
    {g₀ gq gp : GermAt t ξ d} (h : IsBC f g gq) (h' : IsBC f g' gp) {φ ψ φ'' ψ'' : Q Ω d 1} {lam lam'' : PS Ω 2 d}
    (c : Cmp g₀ gq φ ψ lam) (c'' : Cmp g₀ gp φ'' ψ'' lam'') :
    stdLat f.range (transH φ''.1 ψ''.1 lam'') = stdLat f.range (transH φ.1 ψ.1 lam) := by
  obtain ⟨φ', ψ', lam', h1, h2⟩ := key hs hp h h' c c''
  rw [h2]
  exact stdLat_comp f lam' (lin_inv h1.c₂ h1.inv₁) _

theorem key_dir {f : S →+* S₂} {g : GermAt t x d} {g₀ gq : GermAt t x₂ d} (h : IsBC f g gq) {φ ψ : Q S₂ d 1}
    {lam : PS S₂ 2 d} (c : Cmp g₀ gq φ ψ lam) (l : Fin d) :
    ((lieM g₀).pt ((lin φ.1 1).mulVec (Pi.single l 1))).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l := by
  have := (comb_iff g₀ _ _).1 (coord_tan c.hφ l)
  have e₂ : (fun j => lin φ.1 1 j l) = (lin φ.1 1).mulVec (Pi.single l 1) := by
    funext j; simp
  rw [e₂, h.tg] at this
  exact this

theorem lieM_dir (g : GermAt t x d) (l : Fin d) : ((lieM g).pt (Pi.single l 1)).left = g.tg l := (tg_eq g l).symm

theorem lieM_act (g : GermAt t x d) (a : 𝓞 E) (v : Fin d → S) :
    (lieM g).pt ((rho g.B a).mulVec v) = (lieM g).pt v ≫ t.act.act a := (gd_act g a v).symm

theorem exists_germ (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) (ξ : Sp Ω ⟶ X0) :
    ∃ d, Nonempty (GermAt t ξ d) := by
  obtain ⟨A, _, j, d, _, hj, ⟨gA⟩⟩ := germ_aff hs hp (ξ (IsLocalRing.closedPoint Ω))
  obtain ⟨a, ha⟩ := exists_factor ξ j hj
  obtain ⟨g₀, -⟩ := exists_bc a ha gA
  exact ⟨d, ⟨g₀⟩⟩

theorem main (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) (ξ : Sp Ω ⟶ X0) :
    ∃ (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)), Nonempty (GermSys t ξ M) := by
  obtain ⟨d, ⟨g₀⟩⟩ := exists_germ hs hp ξ
  choose gK U hU hq using exists_loc hs hp g₀
  choose g hK using fun p => hq p p (hU p)
  choose φ ψ lam hc using fun p => exists_cmp g₀ (gK p)
  exact ⟨d, lieM g₀, ⟨
    { g₀ := g₀
      dir₀ := lieM_dir g₀
      act₀ := lieM_act g₀
      g := g
      BK := fun p => (gK p).B
      mapK := fun p => (hK p).map
      φ := fun p => (φ p).1
      ψ := fun p => (ψ p).1
      lam := lam
      iso := fun p => (hc p).iso hs hp
      dir := fun p l => key_dir (hK p) (hc p) l
      gen := fun p q h => key_gen hs hp (st_spec h) (genMap_comp p q h) (hK q) (hK p) (hc q) (hc p)
      loc := fun p => ⟨U p, hU p, fun q hqU => (hq p q hqU).elim fun _ hg' =>
        key_loc hs hp (hK q) hg' (hc q) (hc p)⟩ }⟩⟩

end Geo

end PositivityTheory.Xgn.GermSystem
end

theorem PositivityTheory.Xgn.germ_system_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X], PowFns t → IsCptGen ξ → ∃ (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)), Nonempty (GermSys t ξ M) := by
  intro E _ _ _ H _ hs X t Ω _ _ ξ _ hp _
  exact PositivityTheory.Xgn.GermSystem.main hs hp ξ
