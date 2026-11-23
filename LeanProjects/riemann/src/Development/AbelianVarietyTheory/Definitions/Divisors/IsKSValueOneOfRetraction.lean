import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding epsScale
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.GrpTangent GlobalTheory.CatCoh GlobalTheory.Cris

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRham

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {I : Ideal R} {I' : Ideal R'}
  {I'' : Ideal R''} {S S' S'' : Scheme.{0}}

section Prim

variable (κ : DividedPowers I) (t : S ⟶ Sp R)

def pullOver {Y X : Over S} (f : Y ⟶ X) : Cris.H1 κ (X.hom ≫ t) →ₗ[R] Cris.H1 κ (Y.hom ≫ t) :=
  (IsMor.of_over κ (φ := f.left) (by rw [← Category.assoc, Over.w])).pull1

def prim (A : Over S) [GrpObj A] : Submodule R (Cris.H1 κ (A.hom ≫ t)) where
  carrier := {c | ∀ (Y : Over S) (f g : Y ⟶ A),
    pullOver κ t (f * g) c = pullOver κ t f c + pullOver κ t g c}
  add_mem' {a b} ha hb Y f g := by rw [map_add, ha, hb, map_add, map_add]; abel
  zero_mem' Y f g := by simp
  smul_mem' r c hc Y f g := by rw [map_smul, hc, map_smul, map_smul, smul_add]

theorem pullOver_pullOver {Z Y X : Over S} (g : Z ⟶ Y) (f : Y ⟶ X) (c : Cris.H1 κ (X.hom ≫ t)) :
    pullOver κ t g (pullOver κ t f c) = pullOver κ t (g ≫ f) c :=
  IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) rfl c

theorem mem_prim_iff (A : Over S) [GrpObj A] (c : Cris.H1 κ (A.hom ≫ t)) :
    c ∈ prim κ t A ↔ pullOver κ t μ[A] c = pullOver κ t (fst A A) c + pullOver κ t (snd A A) c := by
  constructor
  · intro hc
    have hc' : ∀ (Y : Over S) (f g : Y ⟶ A),
        pullOver κ t (f * g) c = pullOver κ t f c + pullOver κ t g c := hc
    have h := hc' (A ⊗ A) (fst A A) (snd A A)
    rwa [← MonObj.mul_eq_mul] at h
  · intro hc
    show ∀ (Y : Over S) (f g : Y ⟶ A), pullOver κ t (f * g) c = pullOver κ t f c + pullOver κ t g c
    intro Y f g
    have e : f * g = lift f g ≫ μ[A] := by
      rw [MonObj.mul_eq_mul, MonObj.comp_mul, lift_fst, lift_snd]
    rw [e, ← pullOver_pullOver, hc, map_add, pullOver_pullOver, pullOver_pullOver, lift_fst,
      lift_snd]

def AllPrim (A : Over S) [GrpObj A] : Prop := prim κ t A = ⊤

abbrev Crys (A : Over S) [GrpObj A] : Type 1 := Module.Dual R (prim κ t A)

def AllPrim.dualEquiv {A : Over S} [GrpObj A] (h : AllPrim κ t A) :
    Module.Dual R (Cris.H1 κ (A.hom ≫ t)) ≃ₗ[R] Crys κ t A :=
  (LinearEquiv.ofTop _ h).dualMap

end Prim

structure GrpMor (κ : DividedPowers I) (t : S ⟶ Sp R) (A : Over S) [GrpObj A]
    (κ' : DividedPowers I') (t' : S' ⟶ Sp R') (A' : Over S') [GrpObj A'] (σ : R →+* R')
    (b : S' ⟶ S) (φ : A'.left ⟶ A.left) : Prop where
  dp : IsDPMorphism κ κ' σ
  base : b ≫ t = t' ≫ spMap σ
  w : φ ≫ A.hom = A'.hom ≫ b
  mul : ∀ (T : Over S') (x y : T ⟶ A') (x₀ y₀ : Over.mk (T.hom ≫ b) ⟶ A),
    x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (x₀ * y₀).left = (x * y).left ≫ φ

namespace GrpMor

variable {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' : Over S'} [GrpObj A']
  {κ'' : DividedPowers I''} {t'' : S'' ⟶ Sp R''} {A'' : Over S''} [GrpObj A'']
  {σ : R →+* R'} {b : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem of_isGrpPullback (hσ : IsDPMorphism κ κ' σ) (hb : b ≫ t = t' ≫ spMap σ)
    (h : IsGrpPullback A' A b φ) : GrpMor κ t A κ' t' A' σ b φ :=
  ⟨hσ, hb, h.1.w, h.2⟩

private theorem mul_left_eq_lift_comp_mu {X : Scheme.{0}} {G : Over X} [GrpObj G] {T : Over X} (x y : T ⟶ G) :
    (x * y).left = pullback.lift x.left y.left ((Over.w x).trans (Over.w y).symm) ≫ μ[G].left := by
  rw [Hom.mul_def, Over.comp_left, Over.lift_left]

theorem of_hom {u : S ⟶ Sp R'} {B : Over S} [GrpObj B] (hσ : IsDPMorphism κ κ' σ)
    (hb : t = u ≫ spMap σ) (f : B ⟶ A) [IsMonHom f] : GrpMor κ t A κ' u B σ (𝟙 S) f.left where
  dp := hσ
  base := by rw [Category.id_comp]; exact hb
  w := by rw [Category.comp_id]; exact Over.w f
  mul T x y x₀ y₀ hx hy := by
    rw [← Over.comp_left, MonObj.mul_comp, mul_left_eq_lift_comp_mu, mul_left_eq_lift_comp_mu]
    congr 1
    apply pullback.hom_ext
    · simp only [pullback.lift_fst]; exact hx
    · simp only [pullback.lift_snd]; exact hy

theorem isMor (m : GrpMor κ t A κ' t' A' σ b φ) : IsMor κ (A.hom ≫ t) κ' (A'.hom ≫ t') σ φ :=
  ⟨m.dp, by rw [← Category.assoc, m.w, Category.assoc, m.base, Category.assoc]⟩

private theorem grpMor_isMor_comp (m : GrpMor κ t A κ' t' A' σ b φ) {Y : Over S'} (f : Y ⟶ A') :
    IsMor κ (A.hom ≫ t) κ' (Y.hom ≫ t') σ (f.left ≫ φ) :=
  ⟨m.dp, by simp only [Category.assoc]; rw [reassoc_of% m.w, reassoc_of% (Over.w f), m.base]⟩

theorem pullback_mem_primitive (m : GrpMor κ t A κ' t' A' σ b φ) {c : Cris.H1 κ (A.hom ≫ t)} (hc : c ∈ prim κ t A) :
    m.isMor.pull1 c ∈ prim κ' t' A' := by
  have hc' : ∀ (Y : Over S) (f g : Y ⟶ A),
      pullOver κ t (f * g) c = pullOver κ t f c + pullOver κ t g c := hc
  show ∀ (Y : Over S') (f g : Y ⟶ A'), pullOver κ' t' (f * g) (m.isMor.pull1 c) =
    pullOver κ' t' f (m.isMor.pull1 c) + pullOver κ' t' g (m.isMor.pull1 c)
  intro Y f g
  have k : IsMor κ ((Over.mk (Y.hom ≫ b)).hom ≫ t) κ' (Y.hom ≫ t') σ (𝟙 Y.left) :=
    ⟨m.dp, by simp only [Over.mk_hom, Category.id_comp, Category.assoc, m.base]⟩
  have key : ∀ (f₀ : Over.mk (Y.hom ≫ b) ⟶ A) (f : Y ⟶ A'), f₀.left = f.left ≫ φ →
      pullOver κ' t' f (m.isMor.pull1 c) = k.pull1 (pullOver κ t f₀ c) := by
    intro f₀ f hf
    exact (IsMor.pullback1_comp m.isMor (IsMor.of_over κ' (φ := f.left) (by rw [← Category.assoc, Over.w f]))
      (grpMor_isMor_comp m f) (fun _ ↦ rfl) rfl c).trans
      (IsMor.pullback1_comp (IsMor.of_over κ (φ := f₀.left) (by rw [← Category.assoc, Over.w f₀])) k
        (grpMor_isMor_comp m f) (fun _ ↦ rfl) (by rw [Category.id_comp, hf]) c).symm
  have pt : ∀ f : Y ⟶ A', (f.left ≫ φ) ≫ A.hom = (Over.mk (Y.hom ≫ b)).hom := fun f ↦ by
    simp only [Over.mk_hom, Category.assoc]; rw [m.w, reassoc_of% (Over.w f)]
  let f₀ : Over.mk (Y.hom ≫ b) ⟶ A := Over.homMk (f.left ≫ φ) (pt f)
  let g₀ : Over.mk (Y.hom ≫ b) ⟶ A := Over.homMk (g.left ≫ φ) (pt g)
  have hfg : (f₀ * g₀).left = (f * g).left ≫ φ := m.mul Y f g f₀ g₀ rfl rfl
  rw [key f₀ f rfl, key g₀ g rfl, key (f₀ * g₀) (f * g) hfg, hc' _ f₀ g₀, map_add]

def pull (m : GrpMor κ t A κ' t' A' σ b φ) : prim κ t A →ₛₗ[σ] prim κ' t' A' :=
  (m.isMor.pull1.domRestrict _).codRestrict _ fun c ↦ m.pullback_mem_primitive c.2

theorem coe_pull (m : GrpMor κ t A κ' t' A' σ b φ) (c : prim κ t A) :
    (m.pull c : Cris.H1 κ' (A'.hom ≫ t')) = m.isMor.pull1 c := rfl

theorem pull_pull {τ : R' →+* R''} {b' : S'' ⟶ S'} {ψ : A''.left ⟶ A'.left} {ρ : R →+* R''}
    {b'' : S'' ⟶ S} {χ : A''.left ⟶ A.left} (m : GrpMor κ t A κ' t' A' σ b φ)
    (m' : GrpMor κ' t' A' κ'' t'' A'' τ b' ψ) (m'' : GrpMor κ t A κ'' t'' A'' ρ b'' χ)
    (e : ∀ r, τ (σ r) = ρ r) (e' : ψ ≫ φ = χ) (c : prim κ t A) : m'.pull (m.pull c) = m''.pull c :=
  Subtype.ext (IsMor.pullback1_comp m.isMor m'.isMor m''.isMor e e' c.1)

theorem comp {τ : R' →+* R''} {b' : S'' ⟶ S'} {ψ : A''.left ⟶ A'.left}
    (m : GrpMor κ t A κ' t' A' σ b φ) (m' : GrpMor κ' t' A' κ'' t'' A'' τ b' ψ) :
    GrpMor κ t A κ'' t'' A'' (τ.comp σ) (b' ≫ b) (ψ ≫ φ) where
  dp := IsDPMorphism.comp _ m'.dp m.dp
  base := by rw [Category.assoc, m.base, ← Category.assoc, m'.base, Category.assoc, Cris.spMap_comp]
  w := by rw [Category.assoc, m.w, ← Category.assoc, m'.w, Category.assoc]
  mul T x y x₀ y₀ hx hy := by
    let x₁ : Over.mk (T.hom ≫ b') ⟶ A' := Over.homMk (x.left ≫ ψ) (by
      simp only [Over.mk_hom, Category.assoc]; rw [m'.w, reassoc_of% (Over.w x)])
    let y₁ : Over.mk (T.hom ≫ b') ⟶ A' := Over.homMk (y.left ≫ ψ) (by
      simp only [Over.mk_hom, Category.assoc]; rw [m'.w, reassoc_of% (Over.w y)])
    let x₂ : Over.mk ((Over.mk (T.hom ≫ b')).hom ≫ b) ⟶ A := Over.homMk x₀.left (by
      simpa using Over.w x₀)
    let y₂ : Over.mk ((Over.mk (T.hom ≫ b')).hom ≫ b) ⟶ A := Over.homMk y₀.left (by
      simpa using Over.w y₀)
    have h₁ : (x₁ * y₁).left = (x * y).left ≫ ψ := m'.mul T x y x₁ y₁ rfl rfl
    have h₂ : (x₂ * y₂).left = (x₁ * y₁).left ≫ φ :=
      m.mul _ x₁ y₁ x₂ y₂ (by simp [x₂, x₁, hx]) (by simp [y₂, y₁, hy])
    have h₃ : (x₀ * y₀).left = (x₂ * y₂).left :=
      (mul_left_eq_lift_comp_mu x₀ y₀).trans (mul_left_eq_lift_comp_mu x₂ y₂).symm
    rw [h₃, h₂, h₁, Category.assoc]

def Corr (m : GrpMor κ t A κ' t' A' σ b φ) (h : Crys κ t A) (h' : Crys κ' t' A') : Prop :=
  ∀ c, h' (m.pull c) = σ (h c)

end GrpMor

section Push

variable (κ : DividedPowers I) (t : S ⟶ Sp R) {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]

theorem homMor (f : A ⟶ B) [IsMonHom f] : GrpMor κ t B κ t A (RingHom.id R) (𝟙 S) f.left :=
  GrpMor.of_hom (σ := RingHom.id R) (DPMorphism.id κ).isDPMorphism (by rw [Cris.spMap_id, Category.comp_id]) f

def primPull (f : A ⟶ B) [IsMonHom f] : prim κ t B →ₗ[R] prim κ t A := (homMor κ t f).pull

def push (f : A ⟶ B) [IsMonHom f] : Crys κ t A →ₗ[R] Crys κ t B := (primPull κ t f).dualMap

theorem push_apply (f : A ⟶ B) [IsMonHom f] (h : Crys κ t A) (c : prim κ t B) :
    push κ t f h c = h (primPull κ t f c) := rfl

theorem push_id : push κ t (𝟙 A) = LinearMap.id := by
  ext h c
  show h (primPull κ t (𝟙 A) c) = h c
  exact congrArg h (Subtype.ext (IsMor.pullCohomologyOne_id (homMor κ t (𝟙 A)).isMor c.1))

theorem push_comp (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g] :
    push κ t (f ≫ g) = push κ t g ∘ₗ push κ t f := by
  ext h c
  show h (primPull κ t (f ≫ g) c) = h (primPull κ t f (primPull κ t g c))
  exact congrArg h (Subtype.ext (IsMor.pullback1_comp (homMor κ t g).isMor (homMor κ t f).isMor
    (homMor κ t (f ≫ g)).isMor (fun _ ↦ rfl) rfl c.1).symm)

theorem push_mul (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)] :
    push κ t (f * g) = push κ t f + push κ t g := by
  ext h c
  have hc : ∀ (Y : Over S) (f g : Y ⟶ B),
      pullOver κ t (f * g) c.1 = pullOver κ t f c.1 + pullOver κ t g c.1 := c.2
  show h (primPull κ t (f * g) c) = h (primPull κ t f c) + h (primPull κ t g c)
  rw [← map_add]
  exact congrArg h (Subtype.ext (hc A f g))

theorem push_congr {f g : A ⟶ B} [IsMonHom f] [IsMonHom g] (e : f = g) : push κ t f = push κ t g := by
  subst e; rfl

def ringAct [IsCommMonObj A] {O : Type} [Ring O] (a : ReciprocityTheory.ChartRestriction.G.Out.RingAct A O) :
    O →+* Module.End R (Crys κ t A) :=
  RingHom.mk'
    { toFun x := haveI := a.hom x; push κ t (a.act x)
      map_one' := haveI := a.hom 1; (push_congr κ t a.map_one).trans (push_id κ t)
      map_mul' x y := by
        haveI := a.hom
        exact (push_congr κ t (a.map_mul x y)).trans (push_comp κ t _ _) }
    fun x y ↦ by
      haveI := a.hom
      have e : a.act (x + y) = a.act x * a.act y := a.map_add x y
      haveI : IsMonHom (a.act x * a.act y) := e ▸ a.hom _
      exact (push_congr κ t e).trans (push_mul κ t _ _)

variable {O : Type} [CommRing O] (a : OAct O A)

def act : O →+* Module.End R (Crys κ t A) :=
  RingHom.mk'
    { toFun x := haveI := a.hom x; push κ t (a.act x)
      map_one' := haveI := a.hom 1; (push_congr κ t a.one).trans (push_id κ t)
      map_mul' x y := by
        haveI := a.hom
        exact (push_congr κ t ((congrArg a.act (mul_comm x y)).trans (a.mul y x))).trans
          (push_comp κ t _ _) }
    fun x y ↦ by
      haveI := a.hom
      haveI : IsMonHom (a.act x * a.act y) := a.add x y ▸ a.hom _
      exact (push_congr κ t (a.add x y)).trans (push_mul κ t _ _)

theorem act_apply (x : O) [IsMonHom (a.act x)] : act κ t a x = push κ t (a.act x) := rfl

def actAlg : R ⊗[ℤ] O →ₐ[R] Module.End R (Crys κ t A) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (act κ t a).toIntAlgHom
    fun r _ ↦ Algebra.commutes r _

theorem actAlg_tmul (r : R) (x : O) (h : Crys κ t A) :
    actAlg κ t a (r ⊗ₜ x) h = r • act κ t a x h := rfl

@[reducible] def tensorModule : Module (R ⊗[ℤ] O) (Crys κ t A) :=
  Module.compHom _ (actAlg κ t a).toRingHom

theorem isScalarTower_tensorModule :
    letI := tensorModule κ t a
    IsScalarTower R (R ⊗[ℤ] O) (Crys κ t A) := by
  letI := tensorModule κ t a
  exact ⟨fun r z h ↦ show actAlg κ t a (r • z) h = r • actAlg κ t a z h by rw [map_smul]; rfl⟩

end Push

section BaseChange

variable [Algebra R R']

def liftSemi {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[algebraMap R R'] M') : R' ⊗[R] M →ₗ[R'] M' :=
  letI : Module R M' := Module.compHom M' (algebraMap R R')
  haveI : IsScalarTower R R' M' := ⟨fun r x m ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
  LinearMap.liftBaseChange R' ({ f with } : M →ₗ[R] M')

@[simp] theorem liftSemi_tmul {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R' M'] (f : M →ₛₗ[algebraMap R R'] M') (x : R') (m : M) :
    liftSemi f (x ⊗ₜ m) = x • f m := rfl

variable {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' : Over S'} [GrpObj A']
  {b : S' ⟶ S} {φ : A'.left ⟶ A.left} (m : GrpMor κ t A κ' t' A' (algebraMap R R') b φ)

def GrpMor.IsBC : Prop := Function.Bijective (liftSemi m.pull)

variable {m}

theorem GrpMor.IsBC.unique (hm : m.IsBC) {h : Crys κ t A} {h₁ h₂ : Crys κ' t' A'} (e₁ : m.Corr h h₁)
    (e₂ : m.Corr h h₂) : h₁ = h₂ := by
  ext y
  obtain ⟨z, rfl⟩ := hm.2 y
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, e₁ c, e₂ c]
  | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]

theorem GrpMor.IsBC.exists (hm : m.IsBC) (h : Crys κ t A) : ∃ h', m.Corr h h' := by
  let g : prim κ t A →ₛₗ[algebraMap R R'] R' :=
    { toFun := fun c ↦ algebraMap R R' (h c)
      map_add' := fun c d ↦ by simp
      map_smul' := fun r c ↦ by simp }
  let E := LinearEquiv.ofBijective (liftSemi m.pull) hm
  refine ⟨liftSemi g ∘ₗ E.symm.toLinearMap, fun c ↦ ?_⟩
  have hE : E.symm (m.pull c) = 1 ⊗ₜ c := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    show m.pull c = liftSemi m.pull (1 ⊗ₜ c)
    rw [liftSemi_tmul, one_smul]
  show liftSemi g (E.symm (m.pull c)) = algebraMap R R' (h c)
  rw [hE, liftSemi_tmul, one_smul]
  rfl

def GrpMor.IsBC.bcMap (hm : m.IsBC) : Crys κ t A →ₛₗ[algebraMap R R'] Crys κ' t' A' where
  toFun h := (hm.exists h).choose
  map_add' h k := hm.unique (hm.exists _).choose_spec fun c ↦ by
    rw [LinearMap.add_apply, (hm.exists h).choose_spec, (hm.exists k).choose_spec,
      LinearMap.add_apply, map_add]
  map_smul' r h := hm.unique (hm.exists _).choose_spec fun c ↦ by
    rw [LinearMap.smul_apply, (hm.exists h).choose_spec, LinearMap.smul_apply, smul_eq_mul,
      smul_eq_mul, map_mul]

theorem GrpMor.IsBC.corr_iff (hm : m.IsBC) {h : Crys κ t A} {h' : Crys κ' t' A'} :
    m.Corr h h' ↔ hm.bcMap h = h' := by
  constructor
  · exact fun e ↦ hm.unique (hm.exists h).choose_spec e
  · rintro rfl
    exact (hm.exists h).choose_spec

end BaseChange

theorem GrpMor.Corr.push {κ : DividedPowers I} {t : S ⟶ Sp R} {A B : Over S} [GrpObj A] [GrpObj B]
    {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' B' : Over S'} [GrpObj A'] [GrpObj B']
    {σ : R →+* R'} {b : S' ⟶ S} {φ : A'.left ⟶ A.left} {ψ : B'.left ⟶ B.left}
    {m : GrpMor κ t A κ' t' A' σ b φ} (n : GrpMor κ t B κ' t' B' σ b ψ) (f : A ⟶ B) (f' : A' ⟶ B')
    [IsMonHom f] [IsMonHom f'] (e : φ ≫ f.left = f'.left ≫ ψ) {h : Crys κ t A} {h' : Crys κ' t' A'}
    (hh : m.Corr h h') : n.Corr (push κ t f h) (push κ' t' f' h') := by
  intro c
  have H : IsMor κ (B.hom ≫ t) κ' (A'.hom ≫ t') σ (f'.left ≫ ψ) :=
    ⟨n.dp, by simp only [Category.assoc]; rw [reassoc_of% n.w, reassoc_of% (Over.w f'), n.base]⟩
  show h' (primPull κ' t' f' (n.pull c)) = σ (h (primPull κ t f c))
  have e' : primPull κ' t' f' (n.pull c) = m.pull (primPull κ t f c) := Subtype.ext
    ((IsMor.pullback1_comp n.isMor (homMor κ' t' f').isMor H (fun _ ↦ rfl) rfl c.1).trans
      (IsMor.pullback1_comp (homMor κ t f).isMor m.isMor H (fun _ ↦ rfl) e c.1).symm)
  rw [e']
  exact hh _

section Hodge

abbrev primDR (A : Over (Sp R)) [GrpObj A] : Submodule R (FirstDeRham (A.hom ≫ 𝟙 _)) := prim (dp0 R) (𝟙 _) A

abbrev HdR (A : Over (Sp R)) [GrpObj A] : Type 1 := Crys (dp0 R) (𝟙 _) A

variable (A B : Over (Sp R)) [GrpObj A] [GrpObj B]

def PrimitiveSubmodule : Submodule R (primDR A) := (F1 (A.hom ≫ 𝟙 _)).comap (primDR A).subtype

def Fil : Submodule R (HdR A) := (PrimitiveSubmodule A).dualAnnihilator

variable {A B}

theorem mem_Fil {h : HdR A} :
    h ∈ Fil A ↔ ∀ (f : Form (A.hom ≫ 𝟙 _)) (hf : Form.cl _ f ∈ primDR A), h ⟨_, hf⟩ = 0 := by
  rw [Fil, Submodule.mem_dualAnnihilator]
  constructor
  · intro H f hf
    exact H _ (by rw [PrimitiveSubmodule, Submodule.mem_comap, hodgeFiltration_eq_range]; exact ⟨f, rfl⟩)
  · rintro H ⟨w, hw⟩ hw'
    rw [PrimitiveSubmodule, Submodule.mem_comap, hodgeFiltration_eq_range] at hw'
    obtain ⟨f, hf⟩ := hw'
    have e : w = Form.cl _ f := hf.symm
    subst e
    exact H f hw

theorem push_mem_Fil (f : A ⟶ B) [IsMonHom f] {h : HdR A} (hh : h ∈ Fil A) :
    push (dp0 R) (𝟙 _) f h ∈ Fil B := by
  rw [mem_Fil] at hh ⊢
  intro g hg
  have e := (homMor (dp0 R) (𝟙 _) f).isMor.cl_pullForm g
  have hg' : Form.cl _ ((homMor (dp0 R) (𝟙 _) f).isMor.pullForm g) ∈ primDR A := by
    rw [e]; exact (homMor (dp0 R) (𝟙 _) f).pullback_mem_primitive hg
  have e' : primPull (dp0 R) (𝟙 _) f ⟨_, hg⟩ = ⟨_, hg'⟩ := Subtype.ext e.symm
  show h (primPull (dp0 R) (𝟙 _) f ⟨_, hg⟩) = 0
  rw [e']
  exact hh _ hg'

omit [GrpObj A] in

theorem pt_w {D : Type} [CommRing D] [Algebra R D] (v : Over.mk (spMap (algebraMap R D)) ⟶ A) :
    v.left ≫ A.hom ≫ 𝟙 _ = spMap (algebraMap R D) := by
  rw [Category.comp_id]
  exact Over.w v

def tanVal {A : Over (Sp R)} (v : epsR R ⟶ A) : Form (A.hom ≫ 𝟙 _) →ₗ[R] R :=
  TrivSqZeroExt.sndHom R R ∘ₗ (SqExt.dual R).val v.left (pt_w v) ∘ₗ (Form _).subtype

omit [GrpObj A] in

theorem tanVal_apply (v : epsR R ⟶ A) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal v f = TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val v.left (pt_w v) f.1) := rfl

omit [GrpObj A] in

theorem tanVal_epsScale (r : R) (v : epsR R ⟶ A) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal (epsScale r ≫ v) f = r * tanVal v f := by
  have hl : (epsScale r).left = spMap (TrivSqZeroExt.map (r • (LinearMap.id : R →ₗ[R] R))).toRingHom :=
    rfl
  have e := SqExt.val_map (SqExt.dual R) (SqExt.dual R)
    (TrivSqZeroExt.map (r • (LinearMap.id : R →ₗ[R] R))) (AlgHom.id R R) (fun c ↦ by simp)
    (fun b ↦ by simp) v.left (pt_w v) (epsScale r ≫ v).left (pt_w _)
    (by rw [Over.comp_left, hl]; rfl) f
  rw [tanVal_apply, tanVal_apply, e]
  simp

theorem tanVal_one (f : Form (A.hom ≫ 𝟙 _)) : tanVal (1 : epsR R ⟶ A) f = 0 := by
  have hx : η[A].left ≫ A.hom ≫ 𝟙 _ = spMap (algebraMap R (SqExt.dual R).B) := by
    rw [Category.comp_id, Over.w η[A]]
    exact (Cris.spMap_id R).symm
  have hy : spMap ((SqExt.dual R).i : (SqExt.dual R).B →+* (SqExt.dual R).C) ≫ η[A].left =
      (1 : epsR R ⟶ A).left := by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rfl
  rw [tanVal_apply, SqExt.val_const (SqExt.dual R) η[A].left hx _ _ hy f]
  rfl

omit [GrpObj A] [GrpObj B] in

theorem tanVal_comp (v : epsR R ⟶ A) (g : A ⟶ B)
    (m : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) (A.hom ≫ 𝟙 _) (RingHom.id R) g.left)
    (f : Form (B.hom ≫ 𝟙 _)) : tanVal (v ≫ g) f = tanVal v (m.pullForm f) := by
  rw [tanVal_apply, tanVal_apply, SqExt.val_pull (SqExt.dual R) m v.left (pt_w v) (pt_w (v ≫ g)) f]
  rfl

def spOver {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    Over.mk (spMap (algebraMap R D')) ⟶ Over.mk (spMap (algebraMap R D)) :=
  Over.homMk (spMap (φ : D →+* D')) (by
    change spMap _ ≫ spMap _ = spMap _
    rw [← Cris.spMap_comp, φ.comp_algebraMap])

theorem spOver_comp {D D' D'' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'') :
    spOver ψ ≫ spOver φ = spOver (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  simp only [spOver, Over.comp_left, Over.homMk_left]
  rw [← Cris.spMap_comp]
  rfl

theorem tanVal_mul {v w : epsR R ⟶ A} (hv : IsTangent v) (hw : IsTangent w)
    (f : Form (A.hom ≫ 𝟙 _)) : tanVal (v * w) f = tanVal v f + tanVal w f := by
  let E := SqExt.ofModule R R (R × R)
  let p₁ : DualNumber R →ₐ[R] TrivSqZeroExt R (R × R) := TrivSqZeroExt.map (LinearMap.inl R R R)
  let p₂ : DualNumber R →ₐ[R] TrivSqZeroExt R (R × R) := TrivSqZeroExt.map (LinearMap.inr R R R)
  let q₁ : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R := TrivSqZeroExt.map (LinearMap.fst R R R)
  let q₂ : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R := TrivSqZeroExt.map (LinearMap.snd R R R)
  let dg : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R := TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)
  let Z : Over.mk (spMap (algebraMap R (TrivSqZeroExt R (R × R)))) ⟶ A := (spOver p₁ ≫ v) * (spOver p₂ ≫ w)
  have specMap_id₂ : ∀ (D : Type) [CommRing D] [Algebra R D],
      spOver (AlgHom.id R D) = 𝟙 (Over.mk (spMap (algebraMap R D))) :=
    fun D _ _ ↦ Over.OverMorphism.ext (Cris.spMap_id D)
  have kill : ∀ u : epsR R ⟶ A, IsTangent u →
      spOver (TrivSqZeroExt.map (0 : R →ₗ[R] R)) ≫ u = 1 := by
    intro u hu
    have hk : ((TrivSqZeroExt.map (0 : R →ₗ[R] R) : DualNumber R →ₐ[R] DualNumber R) :
        DualNumber R →+* DualNumber R) =
        (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
      RingHom.ext fun x ↦ TrivSqZeroExt.ext (by simp [TrivSqZeroExt.fst_map, TrivSqZeroExt.algebraMap_eq_inl])
        (by simp [TrivSqZeroExt.snd_map, TrivSqZeroExt.algebraMap_eq_inl])
    have hu' : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ u.left = η[A].left := hu
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Hom.one_def, Over.comp_left, Over.toUnit_left]
    show spMap ((TrivSqZeroExt.map (0 : R →ₗ[R] R) : DualNumber R →ₐ[R] DualNumber R) :
        DualNumber R →+* DualNumber R) ≫ u.left = spMap (algebraMap R (DualNumber R)) ≫ η[A].left
    rw [hk, Cris.spMap_comp, Category.assoc, hu']
  have e1 : dg.comp p₁ = AlgHom.id R _ :=
    AlgHom.ext fun x ↦ TrivSqZeroExt.ext (by simp [dg, p₁, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) (by simp [dg, p₁, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map])
  have e2 : dg.comp p₂ = AlgHom.id R _ :=
    AlgHom.ext fun x ↦ TrivSqZeroExt.ext (by simp [dg, p₂, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) (by simp [dg, p₂, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map])
  have e3 : q₁.comp p₁ = AlgHom.id R _ :=
    AlgHom.ext fun x ↦ TrivSqZeroExt.ext (by simp [q₁, p₁, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) (by simp [q₁, p₁, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map])
  have e4 : q₁.comp p₂ = TrivSqZeroExt.map (0 : R →ₗ[R] R) :=
    AlgHom.ext fun x ↦ TrivSqZeroExt.ext (by simp [q₁, p₂, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) (by simp [q₁, p₂, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map])
  have e5 : q₂.comp p₁ = TrivSqZeroExt.map (0 : R →ₗ[R] R) :=
    AlgHom.ext fun x ↦ TrivSqZeroExt.ext (by simp [q₂, p₁, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) (by simp [q₂, p₁, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map])
  have e6 : q₂.comp p₂ = AlgHom.id R _ :=
    AlgHom.ext fun x ↦ TrivSqZeroExt.ext (by simp [q₂, p₂, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) (by simp [q₂, p₂, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map])
  have hZd : spOver dg ≫ Z = v * w := by
    show spOver dg ≫ ((spOver p₁ ≫ v) * (spOver p₂ ≫ w)) = v * w
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp, e1, e2, specMap_id₂,
      Category.id_comp, Category.id_comp]
  have hZ1 : spOver q₁ ≫ Z = v := by
    show spOver q₁ ≫ ((spOver p₁ ≫ v) * (spOver p₂ ≫ w)) = v
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp, e3, e4, specMap_id₂,
      Category.id_comp, kill w hw, _root_.mul_one]
  have hZ2 : spOver q₂ ≫ Z = w := by
    show spOver q₂ ≫ ((spOver p₁ ≫ v) * (spOver p₂ ≫ w)) = w
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp, e5, e6, specMap_id₂,
      Category.id_comp, kill v hv, _root_.one_mul]
  have key : ∀ (φ : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) (u : epsR R ⟶ A),
      (∀ c, (AlgHom.id R R) (E.π c) = (SqExt.dual R).π (φ c)) →
      (∀ b, φ (E.i b) = (SqExt.dual R).i ((AlgHom.id R R) b)) → spOver φ ≫ Z = u →
      tanVal u f = TrivSqZeroExt.snd (R := R) (φ (E.val Z.left (pt_w Z) f.1)) := by
    intro φ u hπ hi hu
    rw [tanVal_apply, SqExt.val_map E (SqExt.dual R) φ (AlgHom.id R R) hπ hi Z.left (pt_w Z) u.left
      (pt_w u) (congrArg Over.Hom.left hu) f]
  rw [key dg (v * w) (fun c ↦ by simp [E, dg, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) (fun b ↦ by simp [E, dg, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) hZd,
    key q₁ v (fun c ↦ by simp [E, q₁, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) (fun b ↦ by simp [E, q₁, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) hZ1,
    key q₂ w (fun c ↦ by simp [E, q₂, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) (fun b ↦ by simp [E, q₂, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]) hZ2]
  obtain ⟨V, hV⟩ : ∃ V : TrivSqZeroExt R (R × R), E.val Z.left (pt_w Z) f.1 = V := ⟨_, rfl⟩
  rw [hV]
  show TrivSqZeroExt.snd (TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R) V) =
    TrivSqZeroExt.snd (TrivSqZeroExt.map (LinearMap.fst R R R) V) +
      TrivSqZeroExt.snd (TrivSqZeroExt.map (LinearMap.snd R R R) V)
  rw [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map]
  exact LinearMap.add_apply _ _ _

def IsLieImage (h : HdR A) (v : epsR R ⟶ A) : Prop :=
  IsTangent v ∧ ∀ (f : Form (A.hom ≫ 𝟙 _)) (hf : Form.cl _ f ∈ primDR A), h ⟨_, hf⟩ = tanVal v f

theorem isLieImage_one_iff {h : HdR A} : IsLieImage h 1 ↔ h ∈ Fil A := by
  have e : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
    RingHom.ext fun _ ↦ rfl
  have ht : IsTangent (1 : epsR R ⟶ A) := by
    show spMap _ ≫ (1 : epsR R ⟶ A).left = η[A].left
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) ≫
      η[A].left = η[A].left
    rw [← Category.assoc, ← Cris.spMap_comp, e, Cris.spMap_id, Category.id_comp]
  rw [mem_Fil]
  unfold IsLieImage
  exact ⟨fun H f hf ↦ (H.2 f hf).trans (tanVal_one f),
    fun H ↦ ⟨ht, fun f hf ↦ (H f hf).trans (tanVal_one f).symm⟩⟩

private theorem mul_left_eq_lift_comp_mu' {X : Scheme.{0}} {G : Over X} [GrpObj G] {T : Over X} (x y : T ⟶ G) :
    (x * y).left = pullback.lift x.left y.left ((Over.w x).trans (Over.w y).symm) ≫ μ[G].left := by
  rw [Hom.mul_def, Over.comp_left, Over.lift_left]

theorem IsLieImage.add {h h' : HdR A} {v v' : epsR R ⟶ A} (e : IsLieImage h v)
    (e' : IsLieImage h' v') : IsLieImage (h + h') (v * v') := by
  have t1 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = η[A].left := e.1
  have t2 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v'.left = η[A].left := e'.1
  have ht : IsTangent (v * v') := by
    show spMap _ ≫ (v * v').left = η[A].left
    have e1 : (η[A] * η[A]).left = η[A].left := by rw [MonObj.one_eq_one, _root_.mul_one]
    rw [mul_left_eq_lift_comp_mu', ← Category.assoc, ← e1, mul_left_eq_lift_comp_mu']
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, t1]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, t2]
  unfold IsLieImage
  refine ⟨ht, fun f hf ↦ ?_⟩
  rw [LinearMap.add_apply, e.2 f hf, e'.2 f hf, tanVal_mul e.1 e'.1 f]

theorem IsLieImage.smul {h : HdR A} {v : epsR R ⟶ A} (e : IsLieImage h v) (r : R) :
    IsLieImage (r • h) (epsScale r ≫ v) := by
  have hl : (epsScale r).left = spMap (TrivSqZeroExt.map (r • (LinearMap.id : R →ₗ[R] R))).toRingHom :=
    rfl
  have t1 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = η[A].left := e.1
  have ee : (TrivSqZeroExt.fstHom R R R).toRingHom.comp
      (TrivSqZeroExt.map (r • (LinearMap.id : R →ₗ[R] R))).toRingHom =
      (TrivSqZeroExt.fstHom R R R).toRingHom := RingHom.ext fun x ↦ by simp
  unfold IsLieImage
  refine ⟨?_, fun f hf ↦ ?_⟩
  · show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (epsScale r ≫ v).left = η[A].left
    rw [Over.comp_left, hl, ← Category.assoc, ← Cris.spMap_comp, ee]
    exact t1
  · rw [LinearMap.smul_apply, e.2 f hf, tanVal_epsScale, smul_eq_mul]

theorem IsLieImage.push {h : HdR A} {v : epsR R ⟶ A} (e : IsLieImage h v) (g : A ⟶ B) [IsMonHom g] :
    IsLieImage (push (dp0 R) (𝟙 _) g h) (v ≫ g) := by
  unfold IsLieImage
  refine ⟨?_, fun f hf ↦ ?_⟩
  · show spMap _ ≫ (v ≫ g).left = η[B].left
    rw [Over.comp_left, ← Category.assoc, e.1, ← Over.comp_left, IsMonHom.one_hom]
  · have m := (homMor (dp0 R) (𝟙 _) g).isMor
    have hf' : Form.cl _ (m.pullForm f) ∈ primDR A := by
      rw [m.cl_pullForm]; exact (homMor (dp0 R) (𝟙 _) g).pullback_mem_primitive hf
    have e' : primPull (dp0 R) (𝟙 _) g ⟨_, hf⟩ = ⟨_, hf'⟩ := Subtype.ext (m.cl_pullForm f).symm
    show h (primPull (dp0 R) (𝟙 _) g ⟨_, hf⟩) = _
    rw [e', e.2 _ hf', tanVal_comp v g m f]

theorem IsLieImage.sub_mem {h h' : HdR A} {v : epsR R ⟶ A} (e : IsLieImage h v)
    (e' : IsLieImage h' v) : h - h' ∈ Fil A := by
  rw [mem_Fil]
  intro f hf
  rw [LinearMap.sub_apply, e.2 f hf, e'.2 f hf, sub_self]

variable (A) in

def LieExact : Prop :=
  (∀ h : HdR A, ∃! v, IsLieImage h v) ∧ ∀ v : epsR R ⟶ A, IsTangent v → ∃ h, IsLieImage h v

variable [IsCommMonObj A] [IsCommMonObj B] {O O' : Type} [CommRing O] [CommRing O']

def LieExact.toLie (H : LieExact A) (a : OAct O A) : HdR A →ₗ[R] Serre.Lie a where
  toFun h := Serre.Lie.mk a (H.1 h).choose (H.1 h).choose_spec.1.1
  map_add' h k := Serre.Lie.ext ((H.1 _).unique (H.1 _).choose_spec.1
    ((H.1 h).choose_spec.1.add (H.1 k).choose_spec.1))
  map_smul' r h := Serre.Lie.ext ((H.1 _).unique (H.1 _).choose_spec.1
    ((H.1 h).choose_spec.1.smul r))

theorem LieExact.toLie_eq_iff (H : LieExact A) (a : OAct O A) {h : HdR A} {v : Serre.Lie a} :
    H.toLie a h = v ↔ IsLieImage h v.hom := by
  constructor
  · rintro rfl
    show IsLieImage h (Serre.Lie.mk a _ _).hom
    rw [Serre.Lie.hom_mk]
    exact (H.1 h).choose_spec.1
  · intro e
    apply Serre.Lie.ext
    show (Serre.Lie.mk a _ _).hom = _
    rw [Serre.Lie.hom_mk]
    exact (H.1 h).unique (H.1 h).choose_spec.1 e

theorem LieExact.ker_toLie (H : LieExact A) (a : OAct O A) : LinearMap.ker (H.toLie a) = Fil A := by
  ext h
  rw [LinearMap.mem_ker, H.toLie_eq_iff, Serre.Lie.hom_zero, isLieImage_one_iff]

theorem LieExact.toLie_surjective (H : LieExact A) (a : OAct O A) :
    Function.Surjective (H.toLie a) := by
  intro v
  obtain ⟨h, e⟩ := H.2 v.hom (Serre.Lie.isTangent v)
  exact ⟨h, (H.toLie_eq_iff a).2 e⟩

def LieExact.quotEquiv (H : LieExact A) (a : OAct O A) : (HdR A ⧸ Fil A) ≃ₗ[R] Serre.Lie a :=
  (Submodule.quotEquivOfEq _ _ (H.ker_toLie a).symm).trans
    ((H.toLie a).quotKerEquivOfSurjective (H.toLie_surjective a))

theorem LieExact.quotEquiv_mk (H : LieExact A) (a : OAct O A) (h : HdR A) :
    H.quotEquiv a (Submodule.Quotient.mk h) = H.toLie a h := rfl

theorem LieExact.toLie_push (H : LieExact A) (H' : LieExact B) (a : OAct O A) (b : OAct O' B)
    (g : A ⟶ B) [IsMonHom g] (h : HdR A) :
    H'.toLie b (push (dp0 R) (𝟙 _) g h) = Serre.Lie.map a b g (H.toLie a h) := by
  rw [H'.toLie_eq_iff, Serre.Lie.hom_map]
  exact ((H.toLie_eq_iff a).1 rfl).push g

theorem LieExact.toLie_act (H : LieExact A) (a : OAct O A) (x : O) (h : HdR A) :
    H.toLie a (act (dp0 R) (𝟙 _) a x h) = x • H.toLie a h := by
  haveI := a.hom x
  rw [act_apply (dp0 R) (𝟙 _) a x, H.toLie_push H a a (a.act x) h, Serre.Lie.map_act]

end Hodge

section Lift

variable (κ : DividedPowers I) {t : S ⟶ Sp R} {A₀ B₀ : Over S} [GrpObj A₀] [GrpObj B₀]
  {A A' A'' B : Over (Sp R)} [GrpObj A] [GrpObj A'] [GrpObj A''] [GrpObj B]
  {i : A₀.left ⟶ A.left} {i' : A₀.left ⟶ A'.left} {i'' : A₀.left ⟶ A''.left} {j : B₀.left ⟶ B.left}

theorem liftMor (h : IsGrpPullback A₀ A t i) : GrpMor (dp0 R) (𝟙 _) A κ t A₀ (RingHom.id R) t i :=
  GrpMor.of_isGrpPullback (Cris.isDPMorphism_of_eq_bot _ rfl _ _) (by rw [Cris.spMap_id]) h

def crysToDR (h : IsGrpPullback A₀ A t i) : Crys κ t A₀ →ₗ[R] HdR A := (liftMor κ h).pull.dualMap

theorem crysToDR_apply (h : IsGrpPullback A₀ A t i) (d : Crys κ t A₀) (c : primDR A) :
    crysToDR κ h d c = d ((liftMor κ h).pull c) := rfl

def liftFil (h : IsGrpPullback A₀ A t i) : Submodule R (Crys κ t A₀) := (Fil A).comap (crysToDR κ h)

theorem crysToDR_push (h : IsGrpPullback A₀ A t i) (k : IsGrpPullback B₀ B t j) (f₀ : A₀ ⟶ B₀)
    (f : A ⟶ B) [IsMonHom f₀] [IsMonHom f] (e : i ≫ f.left = f₀.left ≫ j) (d : Crys κ t A₀) :
    crysToDR κ k (push κ t f₀ d) = push (dp0 R) (𝟙 _) f (crysToDR κ h d) := by
  ext c
  show d (primPull κ t f₀ ((liftMor κ k).pull c)) =
    d ((liftMor κ h).pull (primPull (dp0 R) (𝟙 _) f c))
  have H := (liftMor κ k).isMor.comp (homMor κ t f₀).isMor
  exact congrArg d (Subtype.ext
    ((IsMor.pullback1_comp (liftMor κ k).isMor (homMor κ t f₀).isMor H (fun _ ↦ rfl) rfl c.1).trans
      (IsMor.pullback1_comp (homMor (dp0 R) (𝟙 _) f).isMor (liftMor κ h).isMor H (fun _ ↦ rfl) e c.1).symm))

theorem push_mem_liftFil (h : IsGrpPullback A₀ A t i) (k : IsGrpPullback B₀ B t j) (f₀ : A₀ ⟶ B₀)
    (f : A ⟶ B) [IsMonHom f₀] [IsMonHom f] (e : i ≫ f.left = f₀.left ≫ j) {d : Crys κ t A₀}
    (hd : d ∈ liftFil κ h) : push κ t f₀ d ∈ liftFil κ k := by
  show crysToDR κ k (push κ t f₀ d) ∈ Fil B
  rw [crysToDR_push κ h k f₀ f e d]
  exact push_mem_Fil f hd

theorem crysToDR_corr (h : IsGrpPullback A₀ A t i) {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'}
    {C₀ : Over S'} [GrpObj C₀] {C : Over (Sp R')} [GrpObj C] {l : C₀.left ⟶ C.left}
    (h' : IsGrpPullback C₀ C t' l) {σ : R →+* R'} {b₀ : S' ⟶ S} {b : Sp R' ⟶ Sp R}
    {φ₀ : C₀.left ⟶ A₀.left} {φ : C.left ⟶ A.left} (m : GrpMor κ t A₀ κ' t' C₀ σ b₀ φ₀)
    (n : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) C σ b φ) (e : l ≫ φ = φ₀ ≫ i) {d : Crys κ t A₀}
    {d' : Crys κ' t' C₀} (hd : m.Corr d d') : n.Corr (crysToDR κ h d) (crysToDR κ' h' d') := by
  intro c
  show d' ((liftMor κ' h').pull (n.pull c)) = σ (d ((liftMor κ h).pull c))
  rw [← hd ((liftMor κ h).pull c)]
  have H := n.isMor.comp (liftMor κ' h').isMor
  exact congrArg d' (Subtype.ext
    ((IsMor.pullback1_comp n.isMor (liftMor κ' h').isMor H (fun _ ↦ rfl) rfl c.1).trans
      (IsMor.pullback1_comp (liftMor κ h).isMor m.isMor H (fun _ ↦ rfl) e.symm c.1).symm))

def IsGM (h : IsGrpPullback A₀ A t i) (h' : IsGrpPullback A₀ A' t i') (x : HdR A) (x' : HdR A') : Prop :=
  ∃ d : Crys κ t A₀, crysToDR κ h d = x ∧ crysToDR κ h' d = x'

theorem IsGM.symm {h : IsGrpPullback A₀ A t i} {h' : IsGrpPullback A₀ A' t i'} {x : HdR A}
    {x' : HdR A'} (e : IsGM κ h h' x x') : IsGM κ h' h x' x := by
  obtain ⟨d, h₁, h₂⟩ := e
  exact ⟨d, h₂, h₁⟩

def gmEquiv {h : IsGrpPullback A₀ A t i} {h' : IsGrpPullback A₀ A' t i'}
    (H : Function.Bijective (crysToDR κ h)) (H' : Function.Bijective (crysToDR κ h')) :
    HdR A ≃ₗ[R] HdR A' :=
  (LinearEquiv.ofBijective _ H).symm.trans (LinearEquiv.ofBijective _ H')

end Lift

section KS

variable (R) in

abbrev epsRed : Sp R ⟶ Sp (DualNumber R) := spMap (TrivSqZeroExt.fstHom R R R).toRingHom

variable (R) in

def epsDP : DividedPowers (RingHom.ker (TrivSqZeroExt.fstHom R R R).toRingHom) :=
  divided₂ (SqExt.dual R).sq

variable {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A']
  {i : A.left ⟶ A'.left}

variable (A) in

theorem constMor : GrpMor (dp0 R) (𝟙 _) A (epsDP R) (epsRed R) A (algebraMap R (DualNumber R)) (𝟙 _)
    (Over.Hom.left (𝟙 A)) :=
  { dp := Cris.isDPMorphism_of_eq_bot _ rfl _ _
    base := by
      have e : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) =
          RingHom.id R := RingHom.ext fun _ ↦ rfl
      show 𝟙 _ ≫ 𝟙 _ = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R))
      rw [Category.comp_id, ← Cris.spMap_comp, e, Cris.spMap_id]
    w := by simp
    mul := fun T x y x₀ y₀ hx hy ↦ by
      rw [Over.id_left, Category.comp_id (Over.Hom.left (x * y)), GrpMor.mul_left_eq_lift_comp_mu,
        GrpMor.mul_left_eq_lift_comp_mu]
      congr 1
      apply pullback.hom_ext
      · simp only [pullback.lift_fst]; rw [hx, Over.id_left]; exact Category.comp_id _
      · simp only [pullback.lift_snd]; rw [hy, Over.id_left]; exact Category.comp_id _ }

def IsFilLift (h : IsGrpPullback A A' (epsRed R) i) (f k : HdR A) : Prop :=
  ∃ d ∈ liftFil (epsDP R) h, ∀ c : primDR A,
    d ((constMor A).pull c) = TrivSqZeroExt.inl (f c) + TrivSqZeroExt.inr (k c)

def IsKSValue (h : IsGrpPullback A A' (epsRed R) i) (f : HdR A) (v : epsR R ⟶ A) : Prop :=
  ∃ k, IsFilLift h f k ∧ IsLieImage k v

variable {h : IsGrpPullback A A' (epsRed R) i}

theorem IsKSValue.add {f f' : HdR A} {v v' : epsR R ⟶ A} (e : IsKSValue h f v)
    (e' : IsKSValue h f' v') : IsKSValue h (f + f') (v * v') := by
  obtain ⟨k, ⟨d, hd, hdk⟩, hk⟩ := e
  obtain ⟨k', ⟨d', hd', hdk'⟩, hk'⟩ := e'
  unfold IsKSValue IsFilLift
  refine ⟨k + k', ⟨d + d', add_mem hd hd', fun c ↦ ?_⟩, hk.add hk'⟩
  rw [LinearMap.add_apply, hdk, hdk', LinearMap.add_apply, LinearMap.add_apply,
    TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
  abel

theorem IsKSValue.smul {f : HdR A} {v : epsR R ⟶ A} (e : IsKSValue h f v) (r : R) :
    IsKSValue h (r • f) (epsScale r ≫ v) := by
  obtain ⟨k, ⟨d, hd, hdk⟩, hk⟩ := e
  unfold IsKSValue IsFilLift
  refine ⟨r • k, ⟨TrivSqZeroExt.inl r • d, Submodule.smul_mem _ _ hd, fun c ↦ ?_⟩, hk.smul r⟩
  rw [LinearMap.smul_apply, hdk, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  ext <;> simp

variable (h) in

def KSRegular : Prop := ∀ f ∈ Fil A, ∃! v, IsKSValue h f v

variable [IsCommMonObj A] {O : Type} [CommRing O]

def KSRegular.ks (H : KSRegular h) (a : OAct O A) : Fil A →ₗ[R] Serre.Lie a where
  toFun f := Serre.Lie.mk a (H f.1 f.2).choose (H f.1 f.2).choose_spec.1.choose_spec.2.1
  map_add' f g := Serre.Lie.ext ((H _ (f + g).2).unique (H _ (f + g).2).choose_spec.1
    ((H f.1 f.2).choose_spec.1.add (H g.1 g.2).choose_spec.1))
  map_smul' r f := Serre.Lie.ext ((H _ (r • f).2).unique (H _ (r • f).2).choose_spec.1
    ((H f.1 f.2).choose_spec.1.smul r))

end KS

section Pairing

theorem evalAt_pull {X X' : Scheme.{0}} (φ : X' ⟶ X) {B : Type} [CommRing B] (x : Sp B ⟶ X')
    {U : X.Opens} {V : X'.Opens} (hV : V ≤ φ ⁻¹ᵁ U) (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V)
    (f : Γ(X, U)ˣ) : evalAt (x ≫ φ) U h f.val = evalAt x V h' (res hV (pullU φ U f)).val := by
  have e : (x ≫ φ).appLE U ⊤ h = φ.app U ≫ X'.presheaf.map (homOfLE hV).op ≫ x.appLE V ⊤ h' := by
    rw [Scheme.Hom.comp_appLE, Scheme.Hom.map_appLE]
  unfold Cris.evalAt pullU res
  rw [e]
  rfl

theorem evalAt_pull_g {X X' : Scheme.{0}} (L : LB X) (φ : X' ⟶ X) {B : Type} [CommRing B]
    (x : Sp B ⟶ X') (j j' : PUnit → L.ι)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)))
    (h' : ⊤ ≤ x ⁻¹ᵁ ((L.pull φ).U j ⊓ (L.pull φ).U j')) :
    evalAt (x ≫ φ) _ h (L.g (j PUnit.unit) (j' PUnit.unit)).val =
      evalAt x _ h' ((L.pull φ).g j j').val := by
  unfold LB.pull LB.LinComb
  simp only [Fintype.prod_unique, zpow_one, pow_one]
  exact evalAt_pull φ x _ h h' _

theorem isChern_pull {X X' : Scheme.{0}} {κ : DividedPowers I} {κ' : DividedPowers I'} {s : X ⟶ Sp R}
    {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (m : IsMor κ s κ' s' σ φ) {L : LB X}
    {z : Cris.H2 κ s} (hz : IsChern κ s L z) : IsChern κ' s' (L.pull φ) (m.pull2 z) := by
  obtain ⟨i, hi, u, ℓ, h1, h2, h3⟩ := hz
  have hsm : ∀ T : (Cris.IsSmall κ' s' (L.pull φ).U).FullSubcategory,
      Cris.IsSmall κ s L.U (m.functor.obj T.obj) := by
    rintro ⟨T, j, hj⟩
    refine ⟨j PUnit.unit, fun p hp ↦ ?_⟩
    have hq : T.x p ∈ ⋂ k : PUnit.{1}, ⇑φ ⁻¹' (L.U (j k) : Set X) := hj hp
    exact Set.mem_iInter.1 hq PUnit.unit
  let F := ObjectProperty.lift (Cris.IsSmall κ s L.U)
    ((Cris.IsSmall κ' s' (L.pull φ).U).ι ⋙ m.functor) hsm
  let cm : CatCoh.CoefMap σ ((Cris.IsSmall κ s L.U).ι ⋙ Cris.O κ s)
      ((Cris.IsSmall κ' s' (L.pull φ).U).ι ⋙ Cris.O κ' s') :=
    { G := F
      α := fun T ↦ RingHom.id _
      naturality := fun _ _ ↦ rfl
      smul := fun T r b ↦ (Algebra.smul_def (A := T.obj.B) (σ r) b).symm }
  unfold Cris.IsChern
  refine ⟨fun T _ ↦ i (F.obj T), fun T p hp ↦ show T.obj.x p ∈ ⋂ k : PUnit.{1}, ⇑φ ⁻¹' (L.U (i (F.obj T)) : Set X) from
      Set.mem_iInter.2 fun _ ↦ hi (F.obj T) hp, fun T T' f ↦ u (F.obj T) (F.obj T') (F.map f),
    cm.pullbackTwoCocycle ℓ, fun T T' f ↦ ?_, fun T T' T'' f g ↦ ?_, ?_⟩
  · exact (h1 (F.obj T) (F.obj T') (F.map f)).trans
      (evalAt_pull_g L φ T'.obj.x (fun _ ↦ i (F.obj T')) (fun _ ↦ i (F.obj T)) _ _)
  · have h := h2 (F.obj T) (F.obj T') (F.obj T'') (F.map f) (F.map g)
    rw [← F.map_comp] at h
    exact h
  · have a1 := CatCoh.CoefMap.pullCohomologyTwo_comp m.coef
      (CatCoh.CoefMap.restrict (Cris.O κ' s') (Cris.IsSmall κ' s' (L.pull φ).U).ι) z
    have a2 := CatCoh.CoefMap.pullCohomologyTwo_comp
      (CatCoh.CoefMap.restrict (Cris.O κ s) (Cris.IsSmall κ s L.U).ι) cm z
    have a3 := CatCoh.CoefMap.pullCohomologyTwo_eq_of_natTrans
      (m.coef.comp (CatCoh.CoefMap.restrict (Cris.O κ' s') (Cris.IsSmall κ' s' (L.pull φ).U).ι))
      ((CatCoh.CoefMap.restrict (Cris.O κ s) (Cris.IsSmall κ s L.U).ι).comp cm)
      (𝟙 ((Cris.IsSmall κ' s' (L.pull φ).U).ι ⋙ m.functor)) (fun _ _ ↦ rfl) z
    rw [← CatCoh.CoefMap.pullCohomologyTwo_class, ← h3]
    exact a1.symm.trans (a3.trans a2)

variable (κ : DividedPowers I) (t : S ⟶ Sp R) (A : Over S) [GrpObj A]

def wedgeForm {n : ℕ} (a b : Fin n → prim κ t A) : LinearMap.BilinForm R (Crys κ t A) :=
  ∑ k, ((LinearMap.mul R R).compl₁₂ (Module.Dual.eval R _ (a k)) (Module.Dual.eval R _ (b k)) -
    (LinearMap.mul R R).compl₁₂ (Module.Dual.eval R _ (b k)) (Module.Dual.eval R _ (a k)))

theorem wedgeForm_apply {n : ℕ} (a b : Fin n → prim κ t A) (x y : Crys κ t A) :
    wedgeForm κ t A a b x y = ∑ k, (x (a k) * y (b k) - x (b k) * y (a k)) := by
  simp [wedgeForm, LinearMap.sum_apply]

def IsPolForm (L : LB A.left) (ψ : LinearMap.BilinForm R (Crys κ t A)) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → prim κ t A),
    IsChern κ (A.hom ≫ t) L (∑ k, cup _ (a k).1 (b k).1) ∧ ψ = wedgeForm κ t A a b

variable {κ t A}

theorem IsPolForm.isAlt {L : LB A.left} {ψ : LinearMap.BilinForm R (Crys κ t A)}
    (h : IsPolForm κ t A L ψ) : ψ.IsAlt := by
  obtain ⟨n, a, b, -, rfl⟩ := h
  intro x
  rw [wedgeForm_apply]
  exact Finset.sum_eq_zero fun k _ ↦ by ring

theorem IsPolForm.pull {L : LB A.left} {ψ : LinearMap.BilinForm R (Crys κ t A)}
    (h : IsPolForm κ t A L ψ) {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' : Over S'} [GrpObj A']
    {σ : R →+* R'} {b : S' ⟶ S} {φ : A'.left ⟶ A.left} (m : GrpMor κ t A κ' t' A' σ b φ) :
    ∃ ψ', IsPolForm κ' t' A' (L.pull φ) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨n, a, b, hL, rfl⟩ := h
  refine ⟨wedgeForm κ' t' A' (fun k ↦ m.pull (a k)) (fun k ↦ m.pull (b k)), ?_, ?_⟩
  · unfold IsPolForm
    refine ⟨n, fun k ↦ m.pull (a k), fun k ↦ m.pull (b k), ?_, rfl⟩
    have hc := isChern_pull m.isMor hL
    simp only [map_sum, IsMor.pullCohomologyTwo_cup] at hc
    exact hc
  · intro x x' y y' hx hy
    rw [wedgeForm_apply, wedgeForm_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hx (a k), hy (b k), hx (b k), hy (a k), map_sub, map_mul, map_mul]

theorem isPolForm_zero (L : LB A.left) (h : ∀ i j, L.g i j = 1) : IsPolForm κ t A L 0 := by
  unfold IsPolForm
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_⟩
  · simpa using Cris.isChern_zero κ (A.hom ≫ t) L h
  · ext x y
    simp [wedgeForm_apply]

def eig {O : Type} [CommRing O] (κ : DividedPowers I) (t : S ⟶ Sp R) {A : Over S} [GrpObj A]
    (a : OAct O A) (τ : O →+* R) : Submodule R (Crys κ t A) :=
  ⨅ x : O, LinearMap.ker (act κ t a x - τ x • (1 : Module.End R (Crys κ t A)))

theorem mem_eig {O : Type} [CommRing O] {a : OAct O A} {τ : O →+* R} {h : Crys κ t A} :
    h ∈ eig κ t a τ ↔ ∀ x, act κ t a x h = τ x • h := by
  simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

def IsAdjointFor {O : Type} [CommRing O] (a : OAct O A) (c : O → O)
    (ψ : LinearMap.BilinForm R (Crys κ t A)) : Prop :=
  ∀ (z : O) x y, ψ (act κ t a z x) y = ψ x (act κ t a (c z) y)

def LieExact.filToDual {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O]
    (H : LieExact A) (a : OAct O A) (ψ : LinearMap.BilinForm R (HdR A))
    (hψ : ∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) : Fil A →ₗ[R] Module.Dual R (Serre.Lie a) :=
  (((Fil A).liftQ (ψ ∘ₗ (Fil A).subtype).flip fun g hg ↦ LinearMap.ext fun f ↦ hψ f.1 f.2 g hg) ∘ₗ
    (H.quotEquiv a).symm.toLinearMap).flip

theorem LieExact.filToDual_toLie {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {O : Type}
    [CommRing O] (H : LieExact A) (a : OAct O A) (ψ : LinearMap.BilinForm R (HdR A))
    (hψ : ∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) (f : Fil A) (x : HdR A) :
    H.filToDual a ψ hψ f (H.toLie a x) = ψ f x := by
  rw [← H.quotEquiv_mk a x]
  simp [LieExact.filToDual]
  rfl

end Pairing

section Zero

theorem primDR_unit (c : primDR (𝟙_ (Over (Sp R)))) : c = 0 := by
  haveI : IsIso ((𝟙_ (Over (Sp R))).hom ≫ 𝟙 (Sp R)) := by
    simp only [Over.tensorUnit_hom, Category.comp_id]; exact IsIso.id _
  exact Subtype.ext (Cris.firstDeRham_base_eq_zero _ c.1)

theorem HdR_unit (h : HdR (𝟙_ (Over (Sp R)))) : h = 0 := by
  ext c
  rw [primDR_unit c, map_zero]
  rfl

theorem lieExact_unit : LieExact (𝟙_ (Over (Sp R))) := by
  have key : ∀ (h : HdR (𝟙_ (Over (Sp R)))) (v : epsR R ⟶ 𝟙_ (Over (Sp R))), IsLieImage h v := by
    intro h v
    have hv : v = 1 := toUnit_unique _ _
    subst hv
    rw [HdR_unit h, isLieImage_one_iff]
    exact Submodule.zero_mem _
  unfold LieExact
  exact ⟨fun h ↦ ⟨1, key h 1, fun v _ ↦ toUnit_unique _ _⟩, fun v _ ↦ ⟨0, key 0 v⟩⟩

theorem allPrim_unit : AllPrim (dp0 R) (𝟙 _) (𝟙_ (Over (Sp R))) := by
  haveI : IsIso ((𝟙_ (Over (Sp R))).hom ≫ 𝟙 (Sp R)) := by
    simp only [Over.tensorUnit_hom, Category.comp_id]; exact IsIso.id _
  rw [AllPrim, eq_top_iff]
  intro c _
  rw [Cris.firstDeRham_base_eq_zero _ c]
  exact Submodule.zero_mem _

end Zero

end GlobalTheory.DeRham
