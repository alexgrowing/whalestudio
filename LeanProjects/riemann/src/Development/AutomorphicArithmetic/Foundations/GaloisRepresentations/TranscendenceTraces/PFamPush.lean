import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def sqPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) (A : Sq p) : Sq (h ≫ p) :=
  ⟨A.U, pullback h A.v, A.u, pullback.fst h A.v, pullback.snd h A.v ≫ A.r,
    (IsPullback.of_hasPullback h A.v).paste_vert A.pb⟩

private def resHom {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec F U →+ Sec F V :=
  (F.obj.map g.op).hom.toAddMonoidHom

private theorem pushK_w {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pullback.fst h A.v ≫ h = (pullback.snd h A.v ≫ t.k) ≫ B.v := by
  rw [Category.assoc, t.hv]
  exact pullback.condition

private noncomputable def pushK {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pullback h A.v ⟶ pullback h B.v :=
  pullback.lift (pullback.fst h A.v) (pullback.snd h A.v ≫ t.k) (pushK_w h t)

private theorem pushK_fst {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.fst h B.v = pullback.fst h A.v := pullback.lift_fst _ _ _

private theorem pushK_snd {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.snd h B.v = pullback.snd h A.v ≫ t.k := pullback.lift_snd _ _ _

private theorem pushK_r {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.snd h B.v ≫ B.r = (pullback.snd h A.v ≫ A.r) ≫ t.g := by
  rw [← Category.assoc, pushK_snd, Category.assoc, t.hr, Category.assoc]

private noncomputable def toPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {A B : Sq p} (t : A.To B) :
    (sqPush h p A).To (sqPush h p B) :=
  ⟨t.g, pushK h t, t.hu, pushK_fst h t, pushK_r h t⟩

private theorem res_pushK {R : Type} [CommRing R] {F : Shv R} {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S}
    {A B : Sq p} (t : A.To B) (a : Sec F B.V) :
    Sec.res (pushK h t) (Sec.res (pullback.snd h B.v) a) = Sec.res (pullback.snd h A.v) (Sec.res t.k a) := by
  rw [res_res, res_res, pushK_snd]

private noncomputable def familyPushforward {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {R' R : Type} [CommRing R']
    [CommRing R] {F : Shv R'} {G : Shv R} (τ : Fam0 (h ≫ p) F G) : Fam0 p F G where
  app A := (τ.app (sqPush h p A)).comp (resHom F (pullback.snd h A.v))
  nat {A B} t a := (τ.nat (toPush h p t) (Sec.res (pullback.snd h B.v) a)).trans
    (congrArg (τ.app (sqPush h p A)) (res_pushK h t a))

private noncomputable def famPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {R' R : Type} [CommRing R']
    [CommRing R] {I : Cx R'} {J : Cx R} (τ : Fam (h ≫ p) I J) : Fam p I J where
  deg s := familyPushforward h p (τ.deg s)
  comm A s t a := (τ.comm (sqPush h p A) s t (Sec.res (pullback.snd h A.v) a)).trans
    (congrArg ((τ.deg t).app (sqPush h p A)) (map_res (I.d s t) (pullback.snd h A.v) a))

private theorem sum_push (hS : SumComp) (hF : FibFin) {q : ℕ} {i : ℤ} {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S)
    [IsFinite h] [IsFinite p] (w : Wt Z) (A : Sq p) (a : Sec (tw q i) A.V) (b : Sec (tw q i) A.U)
    (hb : IsSum w (sqPush h p A) (Sec.res (pullback.snd h A.v) a) b) : IsSum (w.push h) A a b := by
  intro Ω _ _ x
  haveI := A.finite
  refine (hb Ω x).trans ((hS (pullback.snd h A.v) A.r Ω x _
    (fun z => w Ω (z ≫ pullback.fst h A.v) • Sec.res z (Sec.res (pullback.snd h A.v) a))).trans ?_)
  refine finsum_congr fun y => finsum_congr fun hy => ?_
  have hfin := hF (pullback.snd h A.v) Ω y
  have hbij := fib_bijOn (IsPullback.of_hasPullback h A.v) (Ω := Ω) y
  have hsum := finsum_mem_eq_of_bijOn (f := fun z => w Ω (z ≫ pullback.fst h A.v))
    (g := fun z' => w Ω z') _ hbij (fun _ _ => rfl)
  show _ = (∑ᶠ (z' : gp Ω ⟶ Z) (_ : z' ∈ fib h (y ≫ A.v)), w Ω z') • Sec.res y a
  rw [← hsum, finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Set.Finite.mem_toFinset] at hz
  rw [res_res]
  congr 2

private theorem self_r {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) :
    pullback.fst h (𝟙 Z') ≫ h ≫ p = (pullback.snd h (𝟙 Z') ≫ p) ≫ 𝟙 S := by
  rw [Category.comp_id, ← Category.assoc, pullback.condition, Category.comp_id]

private theorem res_self {R : Type} [CommRing R] {F : Shv R} {Z Z' : Scheme.{0}} (h : Z ⟶ Z') (a : Sec F Z') :
    Sec.res (pullback.fst h (𝟙 Z')) (Sec.res h a) = Sec.res (pullback.snd h (𝟙 Z')) a := by
  rw [res_res, pullback.condition, Category.comp_id]

theorem UpperTheory.Gal.TranscendenceTraces.famPush_of :
    SumComp → FibFin → FamPush := by
  intro hS hF q i Z Z' S h p _ _ w τ hτ
  refine ⟨famPush h p τ, ?_, ?_⟩
  · intro A a
    obtain ⟨b, hb, hbs⟩ := hτ (sqPush h p A) (Sec.res (pullback.snd h A.v) a)
    refine ⟨b, ?_, sum_push hS hF h p w A a b hbs⟩
    show (τ.deg 0).app (sqPush h p A)
      (Sec.res (pullback.snd h A.v) (Sec.map (resι (ZMod q) (tw q i)) a)) = _
    exact (congrArg ((τ.deg 0).app (sqPush h p A)) (map_res _ _ a)).symm.trans hb
  · intro n a
    let t : (sqPush h p (Sq.self p)).To (Sq.self (h ≫ p)) :=
      ⟨𝟙 S, pullback.fst h (𝟙 Z'), Category.id_comp _, Category.comp_id _, self_r h p⟩
    have hn : Sec.res (𝟙 S) ((τ.deg n).app (Sq.self (h ≫ p)) (Sec.res h a)) =
        (τ.deg n).app (sqPush h p (Sq.self p)) (Sec.res (pullback.fst h (𝟙 Z')) (Sec.res h a)) :=
      (τ.deg n).nat t (Sec.res h a)
    show (τ.deg n).app (sqPush h p (Sq.self p)) (Sec.res (pullback.snd h (𝟙 Z')) a) = _
    exact (congrArg ((τ.deg n).app (sqPush h p (Sq.self p))) (res_self h a).symm).trans
      (hn.symm.trans (res_id _))
