import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwistStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

noncomputable section
namespace UpperTheory.MayerVietorisKummerChernClass

abbrev um {V U : Scheme.{0}} (g : V ⟶ U) : (Γ(U, ⊤))ˣ →* (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom

theorem um_id {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) : um (𝟙 U) u = u := by
  ext; simp [um]

theorem um_comp {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    um (f ≫ g) u = um f (um g u) := by
  ext
  change (f ≫ g).appTop.hom (u : Γ(U, ⊤)) = f.appTop.hom (g.appTop.hom (u : Γ(U, ⊤)))
  rw [Scheme.Hom.comp_appTop]
  rfl

def EG (q : ℕ) : Spc where
  obj n :=
    { obj := fun U => {h : Fin (n.unop.len + 1) → (Γ(U.unop, ⊤))ˣ // IsUnit (q : Γ(U.unop, ⊤))}
      map := fun g => TypeCat.ofHom fun h => ⟨fun i => um g.unop (h.1 i), by simpa using h.2.map g.unop.appTop.hom⟩
      map_id := fun U => by
        ext h x
        exact congrArg Units.val (um_id (h.1 x))
      map_comp := fun f g => by
        ext h x
        exact congrArg Units.val (um_comp g.unop f.unop (h.1 x)) }
  map θ :=
    { app := fun U => TypeCat.ofHom fun h => ⟨fun i => h.1 (θ.unop.toOrderHom i), h.2⟩
      naturality := fun U V g => by
        ext h
        rfl }
  map_id n := by
    ext U h
    rfl
  map_comp f g := by
    ext U h
    rfl

def cob {A : Type} [CommRing A] {ι : Type} [Preorder ι] (h : ι → Aˣ) : ι ⥤ SingleObj (GL (Fin 1) A) where
  obj _ := SingleObj.star _
  map {i j} _ := Matrix.GeneralLinearGroup.scalar (Fin 1) (h i / h j)
  map_id i := by
    change Matrix.GeneralLinearGroup.scalar (Fin 1) (h i / h i) = 1
    rw [div_self', map_one]
  map_comp {i j k} _ _ := by
    change Matrix.GeneralLinearGroup.scalar (Fin 1) (h i / h k) =
      Matrix.GeneralLinearGroup.scalar (Fin 1) (h j / h k) * Matrix.GeneralLinearGroup.scalar (Fin 1) (h i / h j)
    rw [← map_mul, mul_comm, div_mul_div_cancel]

theorem fext {ι : Type} [Category ι] {M : Type} [Monoid M] (F G : ι ⥤ SingleObj M)
    (h : ∀ (i j : ι) (f : i ⟶ j), F.map f = G.map f) : F = G := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun i j f => ?_
  rw [eqToHom_refl _ rfl, Category.id_comp]
  exact (h i j f).trans (Category.comp_id _).symm

theorem map_scalar {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (u : Aˣ) :
    Matrix.GeneralLinearGroup.map φ (Matrix.GeneralLinearGroup.scalar (Fin 1) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map φ.toMonoidHom u) := by
  ext a b
  obtain rfl := Subsingleton.elim a b
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map_apply]

theorem cob_nat {U V : Schemeᵒᵖ} (g : U ⟶ V) {ι : Type} [Preorder ι] (h : ι → (Γ(U.unop, ⊤))ˣ) :
    cob (fun i => um g.unop (h i)) = cob h ⋙ ((glCat 1).map (Scheme.Γ.map g)).toFunctor := by
  refine fext _ _ fun i j f => ?_
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (um g.unop (h i) / um g.unop (h j)) =
    Matrix.GeneralLinearGroup.map (Scheme.Γ.map g).hom (Matrix.GeneralLinearGroup.scalar (Fin 1) (h i / h j))
  rw [← map_div]
  exact (map_scalar (Scheme.Γ.map g).hom (h i / h j)).symm

def pr (q : ℕ) : EG q ⟶ ofCat (glCat 1) where
  app n :=
    { app := fun U => TypeCat.ofHom fun h =>
        (show Fin (n.unop.len + 1) ⥤ SingleObj (GL (Fin 1) Γ(U.unop, ⊤)) from cob h.1)
      naturality := fun U V g => by
        ext h
        exact cob_nat g h.1 }
  naturality m n θ := by
    ext U h
    exact fext _ _ fun i j f => rfl

theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) : Sec.res g (unitSec u) = unitSec (um g u) :=
  (ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op)
    (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op U))).symm

theorem sec_zsmul {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (n : ℤ) (a : Sec F U) :
    Sec.map (n • 𝟙 F) a = n • a := by
  have h1 : (n • 𝟙 F).hom = n • 𝟙 F.obj := (sheafToPresheaf Scheme.etaleTopology _).map_zsmul
  simp only [Sec.map, h1, NatTrans.app_zsmul]
  simp

theorem unitSec_pow {U : Scheme.{0}} (v : (Γ(U, ⊤))ˣ) (n : ℕ) : ((n : ℤ) • unitSec v) = unitSec (v ^ n) := by
  have := map_zsmul ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom (n : ℤ)
    (ULift.up (Additive.ofMul v) : (Scheme.Γ ⋙ unitsF).obj (op U))
  refine this.symm.trans ?_
  refine congrArg ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom ?_
  refine ULift.ext _ _ ?_
  change (n : ℤ) • Additive.ofMul v = Additive.ofMul (v ^ n)
  simp

theorem locRoot (q : ℕ) [NeZero q] {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = um g u := by
  obtain ⟨κ, -, -, -, -, h⟩ := GlobalTheory.T.kummer_sequence_etale_tateTwist q
  refine loc_trans U _ (loc_mono U _ _ (h U hq (unitSec u)) ?_)
  rintro V g ⟨c, hc⟩
  rw [sec_zsmul] at hc
  refine loc_trans V _ (loc_mono V _ _ ((GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).1 V c) ?_)
  rintro W k ⟨x, hx⟩
  obtain ⟨x⟩ := x
  obtain ⟨v, hv⟩ : ∃ v : (Γ(W, ⊤))ˣ, x = Additive.ofMul v := ⟨Additive.toMul x, rfl⟩
  have e1 : unitSec (v ^ q) = unitSec (um k (um g u)) := by
    rw [← unitSec_pow, ← unitSec_res, ← unitSec_res, ← hc]
    have hx' : unitSec v = Sec.res k c :=
      (congrArg (fun z => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op W)).hom (ULift.up z)) hv).symm.trans hx
    rw [hx']
    exact (map_zsmul (Gm.obj.map k.op).hom (q : ℤ) c).symm
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} ℤ) := Scheme.Γ ⋙ unitsF
  let a : P.obj (op W) := ULift.up (Additive.ofMul (v ^ q))
  let b : P.obj (op W) := ULift.up (Additive.ofMul (um k (um g u)))
  have hab : ((toSheafify Scheme.etaleTopology P).app (op W)).hom (a - b) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact e1
  refine loc_mono W _ _ ((GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ P).2.1 W (a - b) hab) ?_
  intro Y m hm
  refine ⟨um m v, ?_⟩
  rw [map_sub, sub_eq_zero] at hm
  have h2 : um m (v ^ q) = um m (um k (um g u)) := congrArg (fun z : P.obj (op Y) => Additive.toMul z.down) hm
  exact (map_pow (um m) v q).symm.trans (h2.trans (by rw [← um_comp, ← um_comp]))

theorem inv_EG (q : ℕ) : Inv q (EG q) := fun _ ⟨x⟩ => x.2

theorem det_scalar1 {A : Type} [CommRing A] (u : Aˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) u) = u := by
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

theorem lineUnit_pr {q : ℕ} {U : Scheme.{0}} (x : Sx (EG q) 1 U) : lineUnit (pr q) x = x.1 0 / x.1 1 :=
  det_scalar1 _

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = um g (lineUnit L x) := by
  have h : (L.app (op (SimplexCategory.mk 1))).app (op V) (x.res g) =
      ((ofCat (glCat 1)).obj (op (SimplexCategory.mk 1))).map g.op ((L.app (op (SimplexCategory.mk 1))).app (op U) x) :=
    ConcreteCategory.congr_hom ((L.app (op (SimplexCategory.mk 1))).naturality g.op) x
  unfold lineUnit
  rw [h]
  have h2 : ∀ y : Sx (ofCat (glCat 1)) 1 U, glMat (y.res g) = Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) :=
    fun y => rfl
  refine (congrArg _ (h2 _)).trans ?_
  exact Matrix.GeneralLinearGroup.map_det _ _

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g :=
  (ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x)

theorem sub_map {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.map f).sub j l h = (x.sub j l h).map f :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x).symm

theorem face_map {E E' : Spc} (f : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (x : Sx E (p + 1) U) (i : Fin (p + 2)) :
    (x.map f).face i = (x.face i).map f :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.δ i).op) (op U)) x).symm

theorem res_map {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    (x.map f).res g = (x.res g).map f :=
  (ConcreteCategory.congr_hom ((f.app (op (SimplexCategory.mk p))).naturality g.op) x).symm

def Wmap {q : ℕ} {A : Spc} (w : ∀ T : Scheme.{0}, Sx A 0 T → (Γ(T, ⊤))ˣ) (hq : Inv q A)
    (hw : ∀ {T' T : Scheme.{0}} (g : T' ⟶ T) (x : Sx A 0 T), w T' (x.res g) = um g (w T x)) : A ⟶ EG q where
  app n :=
    { app := fun U => TypeCat.ofHom fun y =>
        ⟨fun i => w U.unop ((A.map (SimplexCategory.const (SimplexCategory.mk 0) n.unop i).op).app U y),
          hq U.unop ⟨(A.map (SimplexCategory.const (SimplexCategory.mk 0) n.unop 0).op).app U y⟩⟩
      naturality := fun U V g => by
        ext y
        refine Subtype.ext (funext fun i => ?_)
        have h := ConcreteCategory.congr_hom ((A.map (SimplexCategory.const (SimplexCategory.mk 0) n.unop i).op).naturality g) y
        exact (congrArg (w V.unop) h).trans (hw g.unop _) }
  naturality m n θ := by
    ext U y
    refine Subtype.ext (funext fun i => ?_)
    have h2 : θ ≫ (SimplexCategory.const (SimplexCategory.mk 0) n.unop i).op =
        (SimplexCategory.const (SimplexCategory.mk 0) m.unop (θ.unop.toOrderHom i)).op :=
      Quiver.Hom.unop_inj (SimplexCategory.const_comp _ _ _)
    have h3 := ConcreteCategory.congr_hom
      (NatTrans.congr_app (A.map_comp θ (SimplexCategory.const (SimplexCategory.mk 0) n.unop i).op) U) y
    rw [h2] at h3
    exact congrArg (w U.unop) h3.symm

def IsC (q : ℕ) [NeZero q] {E : Spc} (ℓ : ∀ U : Scheme.{0}, Sx E 1 U → (Γ(U, ⊤))ˣ)
    (γ : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ 0 2 (by simp) U x = 0) ∧
  (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = ℓ U x →
    ev γ 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
  ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = ℓ U (x.sub 0 1 (by omega)) →
    w ^ q = ℓ U (x.sub 1 1 (by omega)) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

theorem sep_root (q : ℕ) [NeZero q] {F : Shv (ZMod q)} {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ)
    (a b : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = um g u → Sec.res g a = Sec.res g b) : a = b :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue _ F U).1 a b (loc_mono U _ _ (locRoot q hq u) fun V g ⟨v, hv⟩ => h V g v hv)

theorem sep_root2 (q : ℕ) [NeZero q] {F : Shv (ZMod q)} {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (u u' : (Γ(U, ⊤))ˣ)
    (a b : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U) (v v' : (Γ(V, ⊤))ˣ), v ^ q = um g u → v' ^ q = um g u' →
      Sec.res g a = Sec.res g b) : a = b :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue _ F U).1 a b (loc_mono U _ _ (loc_and U _ _ (locRoot q hq u) (locRoot q hq u'))
    fun V g ⟨⟨v, hv⟩, ⟨v', hv'⟩⟩ => h V g v v' hv hv')

theorem ev_res {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.1 α p s h V U g x

theorem ev_ext {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (h : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 α β h

theorem ev_pull {R : Type} [CommRing R] {E E' : Spc} {I : Cx R} {n : ℤ} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.2.1 f α p s h U x

theorem isC_pull {q : ℕ} [NeZero q] {E E' : Spc} (f : E' ⟶ E) {ℓ : ∀ U : Scheme.{0}, Sx E 1 U → (Γ(U, ⊤))ˣ}
    {γ : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2} (h : IsC q ℓ γ) :
    IsC q (fun U x => ℓ U (x.map f)) ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) := by
  refine ⟨fun U x => ?_, fun U x v hv => ?_, fun U x v w hv hw => ?_⟩
  · rw [ev_pull]
    exact h.1 U _
  · rw [ev_pull]
    exact h.2.1 U _ v hv
  · rw [ev_pull]
    refine h.2.2 U _ v w ?_ ?_
    · rw [sub_map]; exact hv
    · rw [sub_map]; exact hw

theorem isC_unique {q : ℕ} [NeZero q] {E : Spc} (hE : Inv q E) {ℓ : ∀ U : Scheme.{0}, Sx E 1 U → (Γ(U, ⊤))ˣ}
    (hℓ : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U), ℓ V (x.res g) = um g (ℓ U x))
    {γ γ' : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2} (h : IsC q ℓ γ) (h' : IsC q ℓ γ') : γ = γ' := by
  refine ev_ext _ _ fun p s hs U x => ?_
  rcases p with _ | _ | _ | p
  · obtain rfl : s = 2 := by omega
    exact (h.1 U x).trans (h'.1 U x).symm
  · obtain rfl : s = 1 := by omega
    have hq := hE U ⟨x.face 0⟩
    refine sep_root q hq (ℓ U x) _ _ fun V g v hv => ?_
    rw [ev_res, ev_res]
    have hv' : v ^ q = ℓ V (x.res g) := hv.trans (hℓ g x).symm
    exact (h.2.1 V _ v hv').trans (h'.2.1 V _ v hv').symm
  · obtain rfl : s = 0 := by omega
    have hq := hE U ⟨(x.face 0).face 0⟩
    refine sep_root2 q hq (ℓ U (x.sub 0 1 (by omega))) (ℓ U (x.sub 1 1 (by omega))) _ _ fun V g v v' hv hv' => ?_
    rw [ev_res, ev_res]
    have e1 : v ^ q = ℓ V ((x.res g).sub 0 1 (by omega)) := by rw [sub_res, hℓ]; exact hv
    have e2 : v' ^ q = ℓ V ((x.res g).sub 1 1 (by omega)) := by rw [sub_res, hℓ]; exact hv'
    exact (h.2.2 V _ v v' e1 e2).trans (h'.2.2 V _ v v' e1 e2).symm
  · have : Subsingleton (Sec ((res _ (tw q 1)).X s) U) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness _ (tw q 1) U).2.2.2 s (by omega)
    exact Subsingleton.elim _ _

section Simplices
variable {q : ℕ} {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤)))

def s2 (a b : (Γ(U, ⊤))ˣ) : Sx (EG q) 1 U := ⟨![a, b], hq⟩
def s3 (a b c : (Γ(U, ⊤))ˣ) : Sx (EG q) 2 U := ⟨![a, b, c], hq⟩
def s4 (a b c d : (Γ(U, ⊤))ˣ) : Sx (EG q) 3 U := ⟨![a, b, c, d], hq⟩

variable (a b c d : (Γ(U, ⊤))ˣ)

theorem unitsSimplexTwo_face_zero : (s3 hq a b c).face 0 = s2 hq b c := Subtype.ext (funext fun i => by fin_cases i <;> rfl)
theorem unitsSimplexTwo_face_one : (s3 hq a b c).face 1 = s2 hq a c := Subtype.ext (funext fun i => by fin_cases i <;> rfl)
theorem unitsSimplexTwo_face_two : (s3 hq a b c).face 2 = s2 hq a b := Subtype.ext (funext fun i => by fin_cases i <;> rfl)
theorem unitsSimplexThree_face_zero : (s4 hq a b c d).face 0 = s3 hq b c d := Subtype.ext (funext fun i => by fin_cases i <;> rfl)
theorem unitsSimplexThree_face_one : (s4 hq a b c d).face 1 = s3 hq a c d := Subtype.ext (funext fun i => by fin_cases i <;> rfl)
theorem unitsSimplexThree_face_two : (s4 hq a b c d).face 2 = s3 hq a b d := Subtype.ext (funext fun i => by fin_cases i <;> rfl)
theorem unitsSimplexThree_face_three : (s4 hq a b c d).face 3 = s3 hq a b c := Subtype.ext (funext fun i => by fin_cases i <;> rfl)
theorem unitsSimplexTwo_sub_initial : (s3 hq a b c).sub 0 1 (by omega) = s2 hq a b := Subtype.ext (funext fun i => by fin_cases i <;> rfl)
theorem unitsSimplex_three_face_eq_unitsSimplex_two : (s3 hq a b c).sub 1 1 (by omega) = s2 hq b c := Subtype.ext (funext fun i => by fin_cases i <;> rfl)
theorem lineUnit_unitsSimplexOne : lineUnit (pr q) (s2 hq a b) = a / b := lineUnit_pr _

theorem unitsSimplexOne_restrict {V : Scheme.{0}} (g : V ⟶ U) : (s2 hq a b).res g = s2 (by simpa using hq.map g.appTop.hom) (um g a) (um g b) :=
  Subtype.ext (funext fun i => by fin_cases i <;> rfl)
theorem unitsSimplexTwo_restrict {V : Scheme.{0}} (g : V ⟶ U) : (s3 hq a b c).res g = s3 (by simpa using hq.map g.appTop.hom) (um g a) (um g b) (um g c) :=
  Subtype.ext (funext fun i => by fin_cases i <;> rfl)

end Simplices

section Facts
variable {q : ℕ} [NeZero q] {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤)))
  (Z : Cocycle ((chains (ZMod q)).obj (EG q)) (res _ (tw q 1)) 2) (hZ : IsC q (fun _ x => lineUnit (pr q) x) Z.1)
  (a b c d : (Γ(U, ⊤))ˣ)

abbrev G1 : Sec ((res _ (tw q 1)).X 1) U := ev Z.1 1 1 (by simp) U (s2 hq a b)
abbrev G2 : Sec ((res _ (tw q 1)).X 0) U := ev Z.1 2 0 (by simp) U (s3 hq a b c)

theorem delta_zero : δ 2 3 Z.1 = 0 := (Cocycle.mem_iff 2 3 (by norm_num) _).1 Z.2

theorem ev_zero {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (V : Scheme.{0}) (x : Sx E p V) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h V x = 0 :=
  (((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 0 0 p s h V x).2).2.1

theorem neg3 : Int.negOnePow 3 = -1 := by decide

include hZ

theorem F1 : Sec.map ((res _ (tw q 1)).d 1 2) (G1 hq Z a b) = 0 := by
  have h := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (n := 2) (m := 3) (by norm_num) Z.1 U).2 0 1 2 (by simp) (by simp) (s2 hq a b)
  rw [delta_zero, ev_zero, Fin.sum_univ_two, hZ.1, hZ.1] at h
  simpa using h.symm

theorem F2 : Sec.map ((res _ (tw q 1)).d 0 1) (G2 hq Z a b c) = G1 hq Z b c - G1 hq Z a c + G1 hq Z a b := by
  have h := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (n := 2) (m := 3) (by norm_num) Z.1 U).2 1 0 1 (by simp) (by simp) (s3 hq a b c)
  rw [delta_zero, ev_zero, neg3, Fin.sum_univ_three, unitsSimplexTwo_face_zero, unitsSimplexTwo_face_one, unitsSimplexTwo_face_two] at h
  refine eq_of_sub_eq_zero ?_
  refine Eq.trans ?_ h.symm
  simp [G1, G2]
  abel

theorem F3 : G2 hq Z b c d - G2 hq Z a c d + G2 hq Z a b d - G2 hq Z a b c = 0 := by
  have h := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (n := 2) (m := 3) (by norm_num) Z.1 U).2 2 (-1) 0 (by simp) (by simp) (s4 hq a b c d)
  have hs : Subsingleton (Sec ((res _ (tw q 1)).X (-1)) U) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness _ (tw q 1) U).2.2.2 (-1) (by omega)
  rw [delta_zero, ev_zero, neg3, Fin.sum_univ_four, unitsSimplexThree_face_zero, unitsSimplexThree_face_one, unitsSimplexThree_face_two, unitsSimplexThree_face_three, Subsingleton.elim (ev Z.1 (2 + 1) (-1) _ U _) 0] at h
  simp at h
  rw [← neg_eq_zero]
  refine Eq.trans ?_ h.symm
  simp only [G2]
  abel

theorem F5 {a' b' c' : (Γ(U, ⊤))ˣ} (h1 : a / b = b' / c') (h2 : b / c = a' / b') : G2 hq Z a b c = G2 hq Z a' b' c' := by
  refine sep_root2 q hq (a / b) (b / c) _ _ fun V g v w hv hw => ?_
  rw [ev_res, ev_res, unitsSimplexTwo_restrict, unitsSimplexTwo_restrict]
  have hV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map g.appTop.hom
  have e1 := hZ.2.2 V (s3 hV (um g a) (um g b) (um g c)) v w
    (by rw [unitsSimplexTwo_sub_initial]; change _ = lineUnit (pr q) _; rw [lineUnit_unitsSimplexOne, ← map_div]; exact hv)
    (by rw [unitsSimplex_three_face_eq_unitsSimplex_two]; change _ = lineUnit (pr q) _; rw [lineUnit_unitsSimplexOne, ← map_div]; exact hw)
  have e2 := hZ.2.2 V (s3 hV (um g a') (um g b') (um g c')) w v
    (by rw [unitsSimplexTwo_sub_initial]; change _ = lineUnit (pr q) _; rw [lineUnit_unitsSimplexOne, ← map_div, ← h2]; exact hw)
    (by rw [unitsSimplex_three_face_eq_unitsSimplex_two]; change _ = lineUnit (pr q) _; rw [lineUnit_unitsSimplexOne, ← map_div, ← h1]; exact hv)
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [mul_comm, add_comm]

end Facts

theorem ev_neg {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (V : Scheme.{0}) (x : Sx E p V) : ev (-α) p s h V x = -ev α p s h V x := by
  rw [← zero_sub, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 0 α p s h V x).2.1, ev_zero, zero_sub]

theorem sec_map_neg {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map φ (-a) = -Sec.map φ a := map_neg (φ.hom.app (op U)).hom a

theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero (φ.hom.app (op U)).hom

theorem neg2 : Int.negOnePow 2 = 1 := by decide

theorem oneSimplex_eq_mkOfVertices {q : ℕ} {U : Scheme.{0}} (x : Sx (EG q) 1 U) : x = s2 x.2 (x.1 0) (x.1 1) :=
  Subtype.ext (funext fun i => by fin_cases i <;> rfl)

theorem twoSimplex_eq_mkOfVertices {q : ℕ} {U : Scheme.{0}} (x : Sx (EG q) 2 U) : x = s3 x.2 (x.1 0) (x.1 1) (x.1 2) :=
  Subtype.ext (funext fun i => by fin_cases i <;> rfl)

section Theta
variable {q : ℕ} [NeZero q]

def thetaFam (Z : Cocycle ((chains (ZMod q)).obj (EG q)) (res _ (tw q 1)) 2) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx (EG q) p U → Sec ((res _ (tw q 1)).X s) U
  | 0, s, h, U, x => ev Z.1 1 s (by omega) U (s2 x.2 (x.1 0) 1)
  | 1, s, h, U, x => -ev Z.1 2 s (by omega) U (s3 x.2 (x.1 0) (x.1 1) 1)
  | _ + 2, _, _, _, _ => 0

theorem exists_theta (Z : Cocycle ((chains (ZMod q)).obj (EG q)) (res _ (tw q 1)) 2)
    (hZ : IsC q (fun _ x => lineUnit (pr q) x) Z.1) :
    ∃ Θ : Cochain ((chains (ZMod q)).obj (EG q)) (res _ (tw q 1)) 1,
      (∀ (U : Scheme.{0}) (x : Sx (EG q) 0 U), ev Θ 0 1 (by simp) U x = G1 x.2 Z (x.1 0) 1) ∧
      (∀ (U : Scheme.{0}) (x : Sx (EG q) 1 U), ev Θ 1 0 (by simp) U x = -G2 x.2 Z (x.1 0) (x.1 1) 1) ∧
      δ 1 2 Θ = -Z.1 := by
  obtain ⟨Θ, hΘ⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' (ZMod q) (E := EG q) (I := res _ (tw q 1)) (n := 1) (thetaFam Z) (by
    intro p s h V U g x
    rcases p with _ | _ | p
    · obtain rfl : s = 1 := by omega
      change Sec.res g (ev Z.1 1 1 _ U _) = ev Z.1 1 1 _ V _
      rw [ev_res, unitsSimplexOne_restrict, map_one]
      rfl
    · obtain rfl : s = 0 := by omega
      change Sec.res g (-ev Z.1 2 0 _ U _) = -ev Z.1 2 0 _ V _
      refine (map_neg _ _).trans (congrArg Neg.neg ?_)
      refine (ev_res _ _ _ _ g _).trans ?_
      rw [unitsSimplexTwo_restrict, map_one]
      rfl
    · exact map_zero _)
  have h0 : ∀ (U : Scheme.{0}) (x : Sx (EG q) 0 U), ev Θ 0 1 (by simp) U x = G1 x.2 Z (x.1 0) 1 :=
    fun U x => hΘ 0 1 _ U x
  have h1 : ∀ (U : Scheme.{0}) (x : Sx (EG q) 1 U), ev Θ 1 0 (by simp) U x = -G2 x.2 Z (x.1 0) (x.1 1) 1 :=
    fun U x => hΘ 1 0 _ U x
  refine ⟨Θ, h0, h1, ev_ext _ _ fun p s hs U x => ?_⟩
  rw [ev_neg]
  rcases p with _ | _ | _ | p
  · obtain rfl : s = 2 := by omega
    have h := ((GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (n := 1) (m := 2) (by norm_num) Θ U).1 x)
    rw [h, h0, F1 _ Z hZ, hZ.1, neg_zero]
  · obtain rfl : s = 1 := by omega
    have h := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (n := 1) (m := 2) (by norm_num) Θ U).2 0 0 1 (by simp) (by simp) x
    rw [h, h1, Fin.sum_univ_two]
    have e0 : ev Θ 0 1 _ U (x.face 0) = G1 x.2 Z (x.1 1) 1 := h0 U _
    have e1 : ev Θ 0 1 _ U (x.face 1) = G1 x.2 Z (x.1 0) 1 := h0 U _
    rw [e0, e1]
    have h2 := F2 x.2 Z hZ (x.1 0) (x.1 1) 1
    have e3 : ev Z.1 (0 + 1) 1 hs U x = G1 x.2 Z (x.1 0) (x.1 1) := congrArg _ (oneSimplex_eq_mkOfVertices x)
    rw [e3, sec_map_neg, h2, neg2]
    simp
    abel
  · obtain rfl : s = 0 := by omega
    have h := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (n := 1) (m := 2) (by norm_num) Θ U).2 1 (-1) 0 (by simp) (by simp) x
    have hs' : Subsingleton (Sec ((res _ (tw q 1)).X (-1)) U) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness _ (tw q 1) U).2.2.2 (-1) (by omega)
    have f0 : ev Θ 1 0 _ U (x.face 0) = -G2 x.2 Z (x.1 1) (x.1 2) 1 := h1 U _
    have f1 : ev Θ 1 0 _ U (x.face 1) = -G2 x.2 Z (x.1 0) (x.1 2) 1 := h1 U _
    have f2 : ev Θ 1 0 _ U (x.face 2) = -G2 x.2 Z (x.1 0) (x.1 1) 1 := h1 U _
    rw [h, Fin.sum_univ_three, Subsingleton.elim (ev Θ (1 + 1) (-1) _ U x) 0, f0, f1, f2, sec_map_zero, neg2]
    have h3 := F3 x.2 Z hZ (x.1 0) (x.1 1) (x.1 2) 1
    have e3 : ev Z.1 (1 + 1) 0 hs U x = G2 x.2 Z (x.1 0) (x.1 1) (x.1 2) := congrArg _ (twoSimplex_eq_mkOfVertices x)
    rw [e3, ← sub_eq_zero.1 h3]
    simp
    abel
  · have : Subsingleton (Sec ((res _ (tw q 1)).X s) U) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness _ (tw q 1) U).2.2.2 s (by omega)
    exact Subsingleton.elim _ _

end Theta

section Core
variable {q : ℕ} [NeZero q]

theorem cmp_kappa (Z : Cocycle ((chains (ZMod q)).obj (EG q)) (res _ (tw q 1)) 2)
    (hZ : IsC q (fun _ x => lineUnit (pr q) x) Z.1)
    (κ : Cochain ((chains (ZMod q)).obj (sch.obj (Gq q))) (res _ (tw q 1)) 1)
    (hκ : ∀ (U : Scheme.{0}) (x : U ⟶ Gq q) (v : (Γ(U, ⊤))ˣ), v ^ q = um x (tq q) →
      ev κ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (x : U ⟶ Gq q) (a b : (Γ(U, ⊤))ˣ) (h : um x (tq q) = a / b) :
    ev κ 0 1 (by simp) U x = G1 hq Z a b := by
  refine sep_root q hq (a / b) _ _ fun V g v hv => ?_
  have e1 : v ^ q = um (g ≫ x) (tq q) := by rw [um_comp, h]; exact hv
  have e2 : v ^ q = lineUnit (pr q) (s2 (by simpa using hq.map g.appTop.hom) (um g a) (um g b)) := by
    rw [lineUnit_unitsSimplexOne, ← map_div]; exact hv
  have l := (ev_res κ 0 1 (by simp) g (show Sx (sch.obj (Gq q)) 0 U from x)).trans (hκ V (g ≫ x) v e1)
  refine l.trans (Eq.symm ?_)
  refine (ev_res _ _ _ _ g _).trans ?_
  rw [unitsSimplexOne_restrict]
  exact hZ.2.1 V _ v e2

def tauFam {D : Spc} (Z : Cocycle ((chains (ZMod q)).obj (EG q)) (res _ (tw q 1)) 2) (V₁ V₂ : D ⟶ EG q) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 0 = s → ∀ U : Scheme.{0}, Sx D p U → Sec ((res _ (tw q 1)).X s) U
  | 0, s, h, U, y => -ev Z.1 2 s (by omega) U (s3 (y.map V₁).2 ((y.map V₁).1 0) ((y.map V₂).1 0) 1)
  | _ + 1, _, _, _, _ => 0

theorem exists_tau {D : Spc} (Z : Cocycle ((chains (ZMod q)).obj (EG q)) (res _ (tw q 1)) 2) (V₁ V₂ : D ⟶ EG q) :
    ∃ τ : Cochain ((chains (ZMod q)).obj D) (res _ (tw q 1)) 0,
      (∀ (U : Scheme.{0}) (y : Sx D 0 U), ev τ 0 0 (by simp) U y =
        -G2 (y.map V₁).2 Z ((y.map V₁).1 0) ((y.map V₂).1 0) 1) := by
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' (ZMod q) (E := D) (I := res _ (tw q 1)) (n := 0) (tauFam Z V₁ V₂) (by
    intro p s h V U g x
    rcases p with _ | p
    · obtain rfl : s = 0 := by omega
      change Sec.res g (-ev Z.1 2 0 _ U _) = -ev Z.1 2 0 _ V _
      refine (map_neg _ _).trans (congrArg Neg.neg ?_)
      refine (ev_res _ _ _ _ g _).trans ?_
      rw [unitsSimplexTwo_restrict, map_one, ← res_map, ← res_map]
      rfl
    · exact map_zero _)
  exact ⟨τ, fun U y => hτ 0 0 _ U y⟩

end Core

section Core2
variable {q : ℕ} [NeZero q]

theorem comb {M : Type*} [AddCommGroup M] (P Q R S T Y : M) (g1 : P - Q + R - S = 0) (g2 : T - Q + Y - S = 0) :
    -R - -T = P - Y := by
  have h : (P - Q + R - S) - (T - Q + Y - S) = 0 := by rw [g1, g2, sub_zero]
  rw [← sub_eq_zero]
  exact Eq.trans (by abel) (neg_eq_zero.2 h)

theorem neg1 : Int.negOnePow 1 = -1 := by decide

theorem mv_core {D : Spc} (Z : Cocycle ((chains (ZMod q)).obj (EG q)) (res _ (tw q 1)) 2)
    (hZ : IsC q (fun _ x => lineUnit (pr q) x) Z.1)
    (Θ : Cochain ((chains (ZMod q)).obj (EG q)) (res _ (tw q 1)) 1)
    (hΘ0 : ∀ (U : Scheme.{0}) (x : Sx (EG q) 0 U), ev Θ 0 1 (by simp) U x = G1 x.2 Z (x.1 0) 1)
    (hΘ1 : ∀ (U : Scheme.{0}) (x : Sx (EG q) 1 U), ev Θ 1 0 (by simp) U x = -G2 x.2 Z (x.1 0) (x.1 1) 1)
    (κ : Cochain ((chains (ZMod q)).obj (sch.obj (Gq q))) (res _ (tw q 1)) 1)
    (hκ : ∀ (U : Scheme.{0}) (x : U ⟶ Gq q) (v : (Γ(U, ⊤))ˣ), v ^ q = um x (tq q) →
      ev κ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (hκ1 : ∀ (U : Scheme.{0}) (x : U ⟶ Gq q), ev κ 1 0 (by simp) U x = 0)
    (V₁ V₂ : D ⟶ EG q) (u : D ⟶ sch.obj (Gq q))
    (hr : ∀ (T : Scheme.{0}) (y : Sx D 0 T), um (show T ⟶ Gq q from y.map u) (tq q) = (y.map V₁).1 0 / (y.map V₂).1 0) :
    ∃ τ : Cochain ((chains (ZMod q)).obj D) (res _ (tw q 1)) 0,
      (Cochain.ofHom ((chains (ZMod q)).map V₁)).comp Θ (zero_add 1) -
        (Cochain.ofHom ((chains (ZMod q)).map V₂)).comp Θ (zero_add 1) =
      (Cochain.ofHom ((chains (ZMod q)).map u)).comp κ (zero_add 1) + δ 0 1 τ := by
  obtain ⟨τ, hτ⟩ := exists_tau Z V₁ V₂
  refine ⟨τ, ev_ext _ _ fun p s hs U y => ?_⟩
  have hsub := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 ((Cochain.ofHom ((chains (ZMod q)).map V₁)).comp Θ (zero_add 1))
    ((Cochain.ofHom ((chains (ZMod q)).map V₂)).comp Θ (zero_add 1)) p s hs U y).2.1
  have hadd := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 ((Cochain.ofHom ((chains (ZMod q)).map u)).comp κ (zero_add 1))
    (δ 0 1 τ) p s hs U y).1
  rw [hsub, hadd, ev_pull, ev_pull, ev_pull]
  rcases p with _ | _ | p
  · obtain rfl : s = 1 := by omega
    have hq := (y.map V₁).2
    have e1 : ev Θ 0 1 _ U (y.map V₁) = G1 hq Z ((y.map V₁).1 0) 1 := hΘ0 U _
    have e2 : ev Θ 0 1 _ U (y.map V₂) = G1 hq Z ((y.map V₂).1 0) 1 := hΘ0 U _
    have e3 : ev κ 0 1 _ U (y.map u) = G1 hq Z ((y.map V₁).1 0) ((y.map V₂).1 0) :=
      cmp_kappa Z hZ κ hκ hq _ _ _ (hr U y)
    have e4 := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (n := 0) (m := 1) (by norm_num) τ U).1 y
    rw [e1, e2, e3, e4, hτ, sec_map_neg, F2 hq Z hZ]
    abel
  · obtain rfl : s = 0 := by omega
    have hq := (y.map V₁).2
    have hs' : Subsingleton (Sec ((res _ (tw q 1)).X (-1)) U) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness _ (tw q 1) U).2.2.2 (-1) (by omega)
    have e1 : ev Θ (0 + 1) 0 hs U (y.map V₁) = -G2 hq Z ((y.map V₁).1 0) ((y.map V₁).1 1) 1 := hΘ1 U _
    have e2 : ev Θ (0 + 1) 0 hs U (y.map V₂) = -G2 hq Z ((y.map V₂).1 0) ((y.map V₂).1 1) 1 := hΘ1 U _
    have e3 : ev κ (0 + 1) 0 hs U (y.map u) = 0 := hκ1 U _
    have e4 := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (n := 0) (m := 1) (by norm_num) τ U).2 0 (-1) 0 (by simp) (by simp) y
    have x0 : ((y.face 1).map V₁).1 0 = (y.map V₁).1 0 := congrArg (fun z : Sx (EG q) 0 U => z.1 0) (face_map V₁ y 1).symm
    have x1 : ((y.face 0).map V₁).1 0 = (y.map V₁).1 1 := congrArg (fun z : Sx (EG q) 0 U => z.1 0) (face_map V₁ y 0).symm
    have z0 : ((y.face 1).map V₂).1 0 = (y.map V₂).1 0 := congrArg (fun z : Sx (EG q) 0 U => z.1 0) (face_map V₂ y 1).symm
    have z1 : ((y.face 0).map V₂).1 0 = (y.map V₂).1 1 := congrArg (fun z : Sx (EG q) 0 U => z.1 0) (face_map V₂ y 0).symm
    have t0 : ev τ 0 0 (by simp) U (y.face 0) = -G2 hq Z ((y.map V₁).1 1) ((y.map V₂).1 1) 1 := by
      rw [hτ, x1, z1]
    have t1 : ev τ 0 0 (by simp) U (y.face 1) = -G2 hq Z ((y.map V₁).1 0) ((y.map V₂).1 0) 1 := by
      rw [hτ, x0, z0]
    have hu01 : (show U ⟶ Gq q from (y.face 0).map u) = (show U ⟶ Gq q from (y.face 1).map u) :=
      (face_map u y 0).symm.trans (face_map u y 1)
    have rr : (y.map V₁).1 1 / (y.map V₂).1 1 = (y.map V₁).1 0 / (y.map V₂).1 0 := by
      have r0 := hr U (y.face 0)
      have r1 := hr U (y.face 1)
      rw [x1, z1] at r0
      rw [x0, z0] at r1
      rw [← r0, ← r1, hu01]
    have rs : (y.map V₁).1 0 / (y.map V₁).1 1 = (y.map V₂).1 0 / (y.map V₂).1 1 := by
      rw [div_eq_div_iff_mul_eq_mul] at rr ⊢
      rw [← rr, mul_comm]
    have g1 := F3 hq Z hZ ((y.map V₁).1 0) ((y.map V₁).1 1) ((y.map V₂).1 1) 1
    have g2 := F3 hq Z hZ ((y.map V₁).1 0) ((y.map V₂).1 0) ((y.map V₂).1 1) 1
    rw [← F5 hq Z hZ _ _ _ rs rr] at g2
    rw [e1, e2, e3, e4, Subsingleton.elim (ev τ (0 + 1) (-1) _ U y) 0, sec_map_zero, neg1, Fin.sum_univ_two, t0, t1,
      comb _ _ _ _ _ _ g1 g2]
    simp
    abel
  · have : Subsingleton (Sec ((res _ (tw q 1)).X s) U) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness _ (tw q 1) U).2.2.2 s (by omega)
    exact Subsingleton.elim _ _

end Core2

section Final
variable {q : ℕ} [NeZero q]

theorem inv_map {A X : Spc} (f : A ⟶ X) (h : Inv q X) : Inv q A := fun U ⟨x⟩ => h U ⟨x.map f⟩

theorem isUnit_Gq (q : ℕ) [NeZero q] : IsUnit (q : Γ(Gq q, ⊤)) := by
  have h1 : IsUnit (algebraMap ℤ (Localization.Away (q : ℤ)) (q : ℤ)) := IsLocalization.Away.algebraMap_isUnit (q : ℤ)
  have h2 : IsUnit ((q : Localization.Away (q : ℤ))) := by simpa using h1
  have h3 : IsUnit ((q : LqR q)) := by simpa using h2.map (LaurentPolynomial.C (R := Localization.Away (q : ℤ)))
  simpa using h3.map (Scheme.ΓSpecIso (CommRingCat.of (LqR q))).inv.hom

theorem vert_one {A : Spc} {T : Scheme.{0}} (x : Sx A 1 T) :
    (A.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0).op).app (op T) x = x.face 1 := by
  have h : SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0 = SimplexCategory.δ 1 := by
    ext i
    fin_cases i
    rfl
  rw [h]
  rfl

theorem vert_zero {A : Spc} {T : Scheme.{0}} (x : Sx A 1 T) :
    (A.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1).op).app (op T) x = x.face 0 := by
  have h : SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1 = SimplexCategory.δ 0 := by
    ext i
    fin_cases i
    rfl
  rw [h]
  rfl

theorem vert_self {A : Spc} {T : Scheme.{0}} (x : Sx A 0 T) :
    (A.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0).op).app (op T) x = x := by
  have h : SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0 = 𝟙 _ := by
    ext i
    fin_cases i
    rfl
  rw [h]
  simp

theorem pull_pull {D E E' : Spc} {I : Cx (ZMod q)} (a : D ⟶ E) (b : E ⟶ E') {n : ℤ} (θ : Cochain ((chains (ZMod q)).obj E') I n) :
    (Cochain.ofHom ((chains (ZMod q)).map (a ≫ b))).comp θ (zero_add n) =
      (Cochain.ofHom ((chains (ZMod q)).map a)).comp ((Cochain.ofHom ((chains (ZMod q)).map b)).comp θ (zero_add n)) (zero_add n) := by
  rw [Functor.map_comp, Cochain.ofHom_comp]
  exact Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add n)

theorem pull_eq {A X : Spc} (f : A ⟶ X) (L : X ⟶ ofCat (glCat 1)) (w : ∀ T : Scheme.{0}, Sx A 0 T → (Γ(T, ⊤))ˣ)
    (hX : Inv q X) (h : IsTrivBy (f ≫ L) w)
    (Z : Cocycle ((chains (ZMod q)).obj (EG q)) (res _ (tw q 1)) 2) (hZ : IsC q (fun _ x => lineUnit (pr q) x) Z.1)
    (ζ : Cocycle ((chains (ZMod q)).obj X) (res _ (tw q 1)) 2) (hζ : IsC q (fun _ x => lineUnit L x) ζ.1) :
    (Cochain.ofHom ((chains (ZMod q)).map f)).comp ζ.1 (zero_add 2) =
      (Cochain.ofHom ((chains (ZMod q)).map (Wmap w (inv_map f hX) h.1))).comp Z.1 (zero_add 2) := by
  have hA := inv_map (q := q) f hX
  have e : (fun (U : Scheme.{0}) (x : Sx A 1 U) => lineUnit (pr q) (x.map (Wmap w hA h.1))) =
      fun (U : Scheme.{0}) (x : Sx A 1 U) => lineUnit L (x.map f) := by
    funext U x
    have a0 : (x.map (Wmap w hA h.1)).1 0 = w U (x.face 1) := congrArg (w U) (vert_one x)
    have a1 : (x.map (Wmap w hA h.1)).1 1 = w U (x.face 0) := congrArg (w U) (vert_zero x)
    have t : lineUnit L (x.map f) * w U (x.face 0) = w U (x.face 1) := h.2 U x
    rw [lineUnit_pr, a0, a1, ← t, mul_div_cancel_right]
  have c2 : IsC q (fun (U : Scheme.{0}) (x : Sx A 1 U) => lineUnit (pr q) (x.map (Wmap w hA h.1))) _ :=
    isC_pull (Wmap w hA h.1) hZ
  rw [e] at c2
  refine isC_unique hA (ℓ := fun U x => lineUnit L (x.map f)) (fun g x => ?_) (isC_pull f hζ) c2
  rw [← lineUnit_res, res_map]

theorem mv_main (q : ℕ) [NeZero q] {A B X : Spc} (f : A ⟶ X) (g : B ⟶ X) (L : X ⟶ ofCat (glCat 1))
    (w₁ : ∀ T : Scheme.{0}, Sx A 0 T → (Γ(T, ⊤))ˣ) (w₂ : ∀ T : Scheme.{0}, Sx B 0 T → (Γ(T, ⊤))ˣ)
    (u : pullback f g ⟶ sch.obj (Gq q)) (hX : Inv q X) (h₁ : IsTrivBy (f ≫ L) w₁) (h₂ : IsTrivBy (g ≫ L) w₂)
    (hu : ∀ (T : Scheme.{0}) (y : Sx (pullback f g) 0 T), Units.map (show T ⟶ Gq q from y.map u).appTop.hom.toMonoidHom (tq q) =
      w₁ T (y.map (pullback.fst f g)) * (w₂ T (y.map (pullback.snd f g)))⁻¹) :
    IsMVd f g (tw q 1) 1 (pull _ u _ _ (kappa q)) (-(c1 q L).cast (by norm_num) rfl) := by
  obtain ⟨Z, -, a, b, c⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 (pr q) (inv_EG q)
  have hZ : IsC q (fun _ x => lineUnit (pr q) x) Z.1 := ⟨a, b, c⟩
  obtain ⟨Θ, hΘ0, hΘ1, hΘ⟩ := exists_theta Z hZ
  obtain ⟨ζ, hζ, z0, z1, z2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hX
  have hζC : IsC q (fun _ x => lineUnit L x) ζ.1 := ⟨z0, z1, z2⟩
  obtain ⟨κ, hκc, k1, k2⟩ := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).1 (Gq q) (tq q) (isUnit_Gq q)
  have hA := inv_map (q := q) f hX
  have hB := inv_map (q := q) g hX
  let V₁ := Wmap w₁ hA h₁.1
  let V₂ := Wmap w₂ hB h₂.1
  obtain ⟨τ, hτ⟩ := mv_core Z hZ Θ hΘ0 hΘ1 κ.1 k2 k1 (pullback.fst f g ≫ V₁) (pullback.snd f g ≫ V₂) u (by
    intro T y
    have a1 : (y.map (pullback.fst f g ≫ V₁)).1 0 = w₁ T (y.map (pullback.fst f g)) :=
      congrArg (w₁ T) (vert_self (y.map (pullback.fst f g)))
    have a2 : (y.map (pullback.snd f g ≫ V₂)).1 0 = w₂ T (y.map (pullback.snd f g)) :=
      congrArg (w₂ T) (vert_self (y.map (pullback.snd f g)))
    rw [a1, a2, div_eq_mul_inv]
    exact hu T y)
  let zc := zcomp (Cocycle.ofHom ((chains (ZMod q)).map u)) κ (zero_add 1)
  have hzc : δ 1 2 zc.1 = 0 := (Cocycle.mem_iff 1 2 (by norm_num) _).1 zc.2
  let γ : Cocycle ((chains (ZMod q)).obj (pullback f g)) (res _ (tw q 1)) 1 :=
    Cocycle.mk (zc.1 + δ 0 1 τ) 2 (by norm_num) (by rw [δ_add, hzc, δ_δ, add_zero])
  have hγ : CohomologyClass.mk γ = CohomologyClass.mk zc := by
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
    refine ⟨0, by norm_num, τ, ?_⟩
    change δ 0 1 τ = (zc.1 + δ 0 1 τ) - zc.1
    abel
  have hd : ∀ {E : Spc} (V : E ⟶ EG q), δ 1 2 ((Cochain.ofHom ((chains (ZMod q)).map V)).comp Θ (zero_add 1)) =
      -(Cochain.ofHom ((chains (ZMod q)).map V)).comp Z.1 (zero_add 2) := by
    intro E V
    rw [δ_ofHom_comp, hΘ, Cochain.comp_neg]
  refine ⟨γ, -ζ, (Cochain.ofHom ((chains (ZMod q)).map V₁)).comp Θ (zero_add 1),
    (Cochain.ofHom ((chains (ZMod q)).map V₂)).comp Θ (zero_add 1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hγ]
    change _ = pull _ u _ _ (kum q (tq q))
    rw [← hκc]
    rfl
  · exact (CohomologyClass.mk_neg ζ).trans (congrArg Neg.neg hζ)
  · rw [← pull_pull, ← pull_pull]
    exact hτ
  · refine (hd V₁).trans ?_
    rw [← pull_eq f L w₁ hX h₁ Z hZ ζ hζC]
    exact (Cochain.comp_neg _ _ _).symm
  · refine (hd V₂).trans ?_
    rw [← pull_eq g L w₂ hX h₂ Z hZ ζ hζC]
    exact (Cochain.comp_neg _ _ _).symm

end Final

end UpperTheory.MayerVietorisKummerChernClass

theorem UpperTheory.kummer_cocycle_mayerVietoris_of_cover :
    ∀ (q : ℕ) [NeZero q] {A B X : Spc} (f : A ⟶ X) (g : B ⟶ X) (L : X ⟶ ofCat (glCat 1)) (w₁ : ∀ T : Scheme.{0}, Sx A 0 T → (Γ(T, ⊤))ˣ)
        (w₂ : ∀ T : Scheme.{0}, Sx B 0 T → (Γ(T, ⊤))ˣ) (u : pullback f g ⟶ sch.obj (Gq q)), Inv q X → Cover2 (ZMod q) f g →
        IsTrivBy (f ≫ L) w₁ → IsTrivBy (g ≫ L) w₂ →
        (∀ (T : Scheme.{0}) (y : Sx (pullback f g) 0 T), Units.map (show T ⟶ Gq q from y.map u).appTop.hom.toMonoidHom (tq q) =
          w₁ T (y.map (pullback.fst f g)) * (w₂ T (y.map (pullback.snd f g)))⁻¹) →
        IsMVd f g (tw q 1) 1 (pull _ u _ _ (kappa q)) ((c1 q L).cast (by norm_num) rfl) ∨
          IsMVd f g (tw q 1) 1 (pull _ u _ _ (kappa q)) (-(c1 q L).cast (by norm_num) rfl) := by
  intro q _ A B X f g L w₁ w₂ u hX _ h₁ h₂ hu
  exact Or.inr (UpperTheory.MayerVietorisKummerChernClass.mv_main q f g L w₁ w₂ u hX h₁ h₂ hu)
