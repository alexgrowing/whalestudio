import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.AbForms

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R]

abbrev Spo {T : Type} [CommRing T] (f : R →+* T) : Over (Sp R) := Over.mk (spMap f)

def spo {T T' : Type} [CommRing T] [CommRing T'] {f : R →+* T} {f' : R →+* T'} (a : T →+* T')
    (h : a.comp f = f') : Spo f' ⟶ Spo f :=
  Over.homMk (spMap a) (by subst h; exact (spMap_comp f a).symm)

theorem spo_comp {T T' T'' : Type} [CommRing T] [CommRing T'] [CommRing T''] {f : R →+* T}
    {f' : R →+* T'} {f'' : R →+* T''} (a : T →+* T') (b : T' →+* T'') (h : a.comp f = f')
    (h' : b.comp f' = f'') (h'' : (b.comp a).comp f = f'') :
    spo b h' ≫ spo a h = spo (b.comp a) h'' :=
  Over.OverMorphism.ext (spMap_comp a b).symm

theorem spo_id {T : Type} [CommRing T] {f : R →+* T} (h : (RingHom.id T).comp f = f) :
    spo (RingHom.id T) h = 𝟙 _ :=
  Over.OverMorphism.ext (spMap_id T)

section Pts

variable (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M]

abbrev sz : R →+* TrivSqZeroExt B M := (TrivSqZeroExt.inlHom B M).comp (algebraMap R B)

abbrev fs : TrivSqZeroExt B M →+* B := (TrivSqZeroExt.fstHom B B M).toRingHom

theorem fs_sz : (fs B M).comp (sz (R := R) B M) = algebraMap R B := RingHom.ext fun _ ↦ rfl

theorem fs_inl : (fs B M).comp (TrivSqZeroExt.inlHom B M) = RingHom.id B := RingHom.ext fun _ ↦ rfl

end Pts

theorem exists_lift {X : Scheme.{0}} {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
    [IsCentralScalar B M] (x : Sp B ⟶ X) [IsOpenImmersion x] (y : Sp (TrivSqZeroExt B M) ⟶ X)
    (h : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ y = x) :
    ∃ σ : B →+* TrivSqZeroExt B M, y = spMap σ ≫ x := by
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) := by
    change Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom B B M).toRingHom)
    rw [← Set.range_eq_univ, range_comap_of_surjective _ _ (fun b ↦ ⟨TrivSqZeroExt.inl b, rfl⟩)]
    refine Set.eq_univ_of_forall fun p a ha ↦ ?_
    have h0 : a.fst = 0 := ha
    have h2 : a ^ 2 = 0 := by
      rw [pow_two]
      ext <;> simp [h0]
    exact p.isPrime.mem_of_pow_mem 2 (h2 ▸ p.asIdeal.zero_mem)
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := hs p
    refine ⟨q, ?_⟩
    rw [← h]; rfl
  refine ⟨(Spec.preimage (IsOpenImmersion.lift x y hr)).hom, ?_⟩
  have e : spMap (Spec.preimage (IsOpenImmersion.lift x y hr)).hom = IsOpenImmersion.lift x y hr :=
    Spec.map_preimage _
  rw [e, IsOpenImmersion.lift_fac]

theorem one_left (A P : Over (Sp R)) [GrpObj A] : (1 : P ⟶ A).left = P.hom ≫ η[A].left := by
  rw [Hom.one_def]
  simp

section Tm

variable {B B' M M' : Type} [CommRing B] [CommRing B'] [AddCommGroup M] [AddCommGroup M'] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M']

def tmap (α : B →+* B') (f : M →+ M') (hf : ∀ b m, f (b • m) = α b • f m) :
    TrivSqZeroExt B M →+* TrivSqZeroExt B' M' where
  toFun c := TrivSqZeroExt.inl (α c.fst) + TrivSqZeroExt.inr (f c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [hf]

variable (α : B →+* B') (f : M →+ M') (hf : ∀ b m, f (b • m) = α b • f m)

@[simp] theorem fst_tmap (c : TrivSqZeroExt B M) : (tmap α f hf c).fst = α c.fst := by simp [tmap]

@[simp] theorem snd_tmap (c : TrivSqZeroExt B M) : (tmap α f hf c).snd = f c.snd := by simp [tmap]

end Tm

section Group

variable {A : Over (Sp R)} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]

def xo (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B)) : Spo (algebraMap R B) ⟶ A :=
  Over.homMk x hx

variable {M : Type} [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
  (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))

def Zp (σ : B →+* TrivSqZeroExt B M) (hσ : σ.comp (algebraMap R B) = sz B M) : Spo (sz (R := R) B M) ⟶ A :=
  spo σ hσ ≫ xo x hx * (spo (TrivSqZeroExt.inlHom B M) rfl ≫ xo x hx)⁻¹

theorem spo_xo (τ : B →+* B) (hτ : τ = RingHom.id B) (h : τ.comp (algebraMap R B) = algebraMap R B) :
    spo τ h ≫ xo x hx = xo x hx := by
  subst hτ
  rw [spo_id, Category.id_comp]

theorem Zp_fst (σ : B →+* TrivSqZeroExt B M) (hσ : σ.comp (algebraMap R B) = sz B M)
    (h1 : (fs B M).comp σ = RingHom.id B) : spo (fs B M) (fs_sz B M) ≫ Zp x hx σ hσ = 1 := by
  rw [Zp, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, spo_comp _ _ _ _ (by rw [RingHom.comp_assoc, hσ, fs_sz]),
    spo_comp _ _ _ _ (by rw [RingHom.comp_assoc]; exact fs_sz B M), spo_xo x hx _ h1, spo_xo x hx _ (fs_inl B M), mul_inv_cancel]

variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M']

theorem spo_spo_xo (x' : Sp B' ⟶ A.left) (hx' : x' ≫ A.hom = spMap (algebraMap R B'))
    (α : B →+* B') (hxx : x' = spMap α ≫ x)
    {T T' : Type} [CommRing T] [CommRing T'] {f : R →+* T} {f' : R →+* T'} (ψ : T →+* T')
    (hψ : ψ.comp f = f') (τ : B →+* T) (hτ : τ.comp (algebraMap R B) = f)
    (τ' : B' →+* T') (hτ' : τ'.comp (algebraMap R B') = f') (e : ψ.comp τ = τ'.comp α) :
    spo ψ hψ ≫ spo τ hτ ≫ xo x hx = spo τ' hτ' ≫ xo x' hx' := by
  refine Over.OverMorphism.ext ?_
  change spMap ψ ≫ spMap τ ≫ x = spMap τ' ≫ x'
  rw [hxx, ← Category.assoc, ← spMap_comp, e, spMap_comp, Category.assoc]

theorem Zp_map (x' : Sp B' ⟶ A.left) (hx' : x' ≫ A.hom = spMap (algebraMap R B'))
    (α : B →+* B') (hxx : x' = spMap α ≫ x) (hα : α.comp (algebraMap R B) = algebraMap R B')
    (f : M →+ M') (hf : ∀ b m, f (b • m) = α b • f m)
    (σ : B →+* TrivSqZeroExt B M) (hσ : σ.comp (algebraMap R B) = sz B M)
    (σ' : B' →+* TrivSqZeroExt B' M') (hσ' : σ'.comp (algebraMap R B') = sz B' M')
    (e : (tmap α f hf).comp σ = σ'.comp α) (h : (tmap α f hf).comp (sz (R := R) B M) = sz B' M') :
    spo (tmap α f hf) h ≫ Zp x hx σ hσ = Zp x' hx' σ' hσ' := by
  rw [Zp, MonObj.comp_mul, GrpObj.comp_inv, spo_spo_xo x hx x' hx' α hxx _ h σ hσ σ' hσ' e,
    spo_spo_xo x hx x' hx' α hxx _ h (TrivSqZeroExt.inlHom B M) rfl (TrivSqZeroExt.inlHom B' M') rfl
      (RingHom.ext fun b ↦ by ext <;> simp)]
  rfl

end Group

section Cot

variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
  [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ A.left} (hy : IsCot A.hom η[A].left W y₀)

def yo : Spo (TrivSqZeroExt.inlHom R W) ⟶ A := Over.homMk y₀ hy.1

variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]

theorem tsz_comp (u : W →ₗ[R] M) : (tsz (B := B) u).comp (TrivSqZeroExt.inlHom R W) = sz B M :=
  RingHom.ext fun r ↦ by ext <;> simp [tsz]

def tzo (u : W →ₗ[R] M) : Spo (sz (R := R) B M) ⟶ A := spo (tsz u) (tsz_comp u) ≫ yo hy

theorem tzo_fst (u : W →ₗ[R] M) : spo (fs B M) (fs_sz B M) ≫ tzo (B := B) hy u = 1 := by
  refine Over.OverMorphism.ext ?_
  rw [one_left]
  change spMap (fs B M) ≫ spMap (tsz u) ≫ y₀ = spMap (algebraMap R B) ≫ η[A].left
  have e : (fs B M).comp (tsz u) = (algebraMap R B).comp (TrivSqZeroExt.fstHom R R W).toRingHom :=
    RingHom.ext fun c ↦ by simp [tsz]
  rw [← Category.assoc, ← spMap_comp, e, spMap_comp, Category.assoc, hy.2.1]

theorem cot_unique (Zt : Spo (sz (R := R) B M) ⟶ A) (hZ : spo (fs B M) (fs_sz B M) ≫ Zt = 1) :
    ∃! u : W →ₗ[R] M, Zt = tzo hy u := by
  have h2 : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ Zt.left =
      spMap (algebraMap R B) ≫ η[A].left :=
    (congrArg (fun t ↦ t.left) hZ).trans (one_left _ _)
  obtain ⟨u, hu, hu'⟩ := hy.2.2 B M Zt.left (Over.w Zt) h2
  exact ⟨u, Over.OverMorphism.ext hu, fun v hv ↦ hu' v (congrArg (fun t ↦ t.left) hv)⟩

variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M']

theorem tzo_map (α : B →+* B') (hα : α.comp (algebraMap R B) = algebraMap R B') (f : M →ₗ[R] M')
    (hf : ∀ b m, (f : M →+ M') (b • m) = α b • (f : M →+ M') m)
    (h : (tmap α (f : M →+ M') hf).comp (sz (R := R) B M) = sz B' M') (u : W →ₗ[R] M) :
    spo (tmap α (f : M →+ M') hf) h ≫ tzo hy u = tzo (B := B') hy (f ∘ₗ u) := by
  have e : (tmap α (f : M →+ M') hf).comp (tsz u) = tsz (B := B') (f ∘ₗ u) := RingHom.ext fun c ↦ by
    ext
    · simp [tsz, ← hα]
    · simp [tsz]
  refine Over.OverMorphism.ext ?_
  change spMap (tmap α (f : M →+ M') hf) ≫ spMap (tsz u) ≫ y₀ = spMap (tsz (B := B') (f ∘ₗ u)) ≫ y₀
  rw [← Category.assoc, ← spMap_comp, e]

theorem diag_w : (diagSec R B : B →+* TrivSqZeroExt B Ω[B⁄R]).comp (algebraMap R B) = sz B Ω[B⁄R] :=
  RingHom.ext fun r ↦ by
    ext
    · exact fst_derSec _ _
    · exact (snd_derSec _ _).trans (by simp)

theorem diag_fst : (fs B Ω[B⁄R]).comp (diagSec R B : B →+* TrivSqZeroExt B Ω[B⁄R]) = RingHom.id B :=
  RingHom.ext fun b ↦ fst_derSec _ b

variable (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))

theorem Zp_diag_fst : spo (fs B Ω[B⁄R]) (fs_sz B Ω[B⁄R]) ≫
    Zp x hx (M := Ω[B⁄R]) (diagSec R B : B →+* _) diag_w = 1 := by
  have h := Zp_fst (R := R) (A := A) (B := B) (M := Ω[B⁄R]) x hx (diagSec R B : B →+* _) diag_w diag_fst
  exact h

theorem exists_uOf : ∃ u : W →ₗ[R] Ω[B⁄R],
    Zp x hx (diagSec R B : B →+* _) diag_w = tzo (B := B) (M := Ω[B⁄R]) hy u := by
  have h := cot_unique (B := B) (M := Ω[B⁄R]) hy _ (Zp_diag_fst x hx)
  exact h.exists

def uOf : W →ₗ[R] Ω[B⁄R] :=
  (exists_uOf hy x hx).choose

theorem uOf_spec : Zp x hx (diagSec R B : B →+* _) diag_w = tzo (B := B) (M := Ω[B⁄R]) hy (uOf hy x hx) :=
  (exists_uOf hy x hx).choose_spec

abbrev tm (f : Ω[B⁄R] →ₗ[B] M) : TrivSqZeroExt B Ω[B⁄R] →+* TrivSqZeroExt B M :=
  tmap (RingHom.id B) (f.restrictScalars R : Ω[B⁄R] →ₗ[R] M) fun b m ↦ f.map_smul b m

abbrev sg (f : Ω[B⁄R] →ₗ[B] M) : B →+* TrivSqZeroExt B M := (tm f).comp (diagSec R B : B →+* _)

theorem tm_w (f : Ω[B⁄R] →ₗ[B] M) : (tm f).comp (sz (R := R) B Ω[B⁄R]) = sz B M :=
  RingHom.ext fun r ↦ by
    ext
    · exact fst_tmap (RingHom.id B) ((f.restrictScalars R : Ω[B⁄R] →ₗ[R] M) : Ω[B⁄R] →+ M)
        (fun b m ↦ f.map_smul b m) _
    · exact (snd_tmap (RingHom.id B) ((f.restrictScalars R : Ω[B⁄R] →ₗ[R] M) : Ω[B⁄R] →+ M)
        (fun b m ↦ f.map_smul b m) _).trans (map_zero _)

theorem sg_w (f : Ω[B⁄R] →ₗ[B] M) : (sg f).comp (algebraMap R B) = sz B M := by
  rw [RingHom.comp_assoc, diag_w, tm_w]

theorem Zp_sg (f : Ω[B⁄R] →ₗ[B] M) :
    Zp x hx (sg f) (sg_w f) = tzo hy ((f.restrictScalars R) ∘ₗ uOf hy x hx) := by
  have h := Zp_map x hx x hx (RingHom.id B) (by rw [spMap_id, Category.id_comp]) rfl
    ((f.restrictScalars R : Ω[B⁄R] →ₗ[R] M) : Ω[B⁄R] →+ M) (fun b m ↦ f.map_smul b m)
    (diagSec R B : B →+* _) diag_w (sg f) (sg_w f) rfl (tm_w f)
  rw [← h, uOf_spec hy x hx]
  exact tzo_map hy (RingHom.id B) rfl (f.restrictScalars R) (fun b m ↦ f.map_smul b m) _ _

theorem spMap_inj {T T' : Type} [CommRing T] [CommRing T'] {f g : T →+* T'} (h : spMap f = spMap g) : f = g :=
  RingHom.ext fun r ↦ congrArg (fun q ↦ q.hom r) (Spec.map_injective h)

theorem sg_fst (f : Ω[B⁄R] →ₗ[B] M) (b : B) : (sg f b).fst = b :=
  (fst_tmap (RingHom.id B) ((f.restrictScalars R : Ω[B⁄R] →ₗ[R] M) : Ω[B⁄R] →+ M)
    (fun b m ↦ f.map_smul b m) _).trans (fst_derSec _ b)

theorem sg_snd (f : Ω[B⁄R] →ₗ[B] M) (b : B) : (sg f b).snd = f (KaehlerDifferential.D R B b) :=
  (snd_tmap (RingHom.id B) ((f.restrictScalars R : Ω[B⁄R] →ₗ[R] M) : Ω[B⁄R] →+ M)
    (fun b m ↦ f.map_smul b m) _).trans (congrArg f (snd_derSec (KaehlerDifferential.D R B) b))

theorem Zp_congr {σ σ' : B →+* TrivSqZeroExt B M} (e : σ = σ') (h : σ.comp (algebraMap R B) = sz B M)
    (h' : σ'.comp (algebraMap R B) = sz B M) : Zp x hx σ h = Zp x hx σ' h' := by
  subst e; rfl

def derOf (σ : B →+* TrivSqZeroExt B M) (h1 : ∀ b, (σ b).fst = b)
    (h2 : ∀ r, σ (algebraMap R B r) = TrivSqZeroExt.inl (algebraMap R B r)) : Derivation R B M :=
  Derivation.mk'
    { toFun b := (σ b).snd
      map_add' a b := by simp
      map_smul' r b := by
        rw [Algebra.smul_def, map_mul, h2]
        simp [h1] }
    fun a b ↦ by
      simp [h1, add_comm]

variable [IsOpenImmersion x]

theorem exists_lin (g : W →ₗ[R] M) :
    ∃ f : Ω[B⁄R] →ₗ[B] M, (f.restrictScalars R) ∘ₗ uOf hy x hx = g := by
  let c : Spo (sz (R := R) B M) ⟶ A := spo (TrivSqZeroExt.inlHom B M) rfl ≫ xo x hx
  have hz := tzo_fst (B := B) (M := M) hy g
  let y : Spo (sz (R := R) B M) ⟶ A := tzo hy g * c
  have hy1 : spo (fs B M) (fs_sz B M) ≫ y = xo x hx := by
    have h3 : spo (fs B M) (fs_sz B M) ≫ c = xo x hx := by
      change _ ≫ spo (TrivSqZeroExt.inlHom B M) rfl ≫ xo x hx = _
      rw [← Category.assoc, spo_comp _ _ _ _ (by rw [RingHom.comp_assoc]; exact fs_sz B M),
        spo_xo x hx _ (fs_inl B M)]
    change _ ≫ (tzo hy g * c) = _
    rw [MonObj.comp_mul, hz, _root_.one_mul, h3]
  have hy2 : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ y.left = x := congrArg (fun t ↦ t.left) hy1
  obtain ⟨σ, hσ⟩ := exists_lift x y.left hy2
  have hw : σ.comp (algebraMap R B) = sz B M := spMap_inj (by
    rw [spMap_comp, ← hx, ← Category.assoc, ← hσ]
    exact Over.w y)
  have h1 : (fs B M).comp σ = RingHom.id B := spMap_inj (by
    refine (cancel_mono x).1 ?_
    rw [spMap_comp, Category.assoc, ← hσ, hy2, spMap_id, Category.id_comp])
  let δ : Derivation R B M := derOf σ (fun b ↦ congrArg (fun t ↦ t b) h1)
    (fun r ↦ congrArg (fun t ↦ t r) hw)
  let f : Ω[B⁄R] →ₗ[B] M := δ.liftKaehlerDifferential
  have e : sg f = σ := RingHom.ext fun b ↦ by
    ext
    · exact (sg_fst f b).trans (congrArg (fun t ↦ t b) h1).symm
    · exact (sg_snd f b).trans (Derivation.liftKaehlerDifferential_comp_D δ b)
  have hZ : Zp x hx σ hw = tzo hy g := by
    have h4 : spo σ hw ≫ xo x hx = y := Over.OverMorphism.ext hσ.symm
    change spo σ hw ≫ xo x hx * c⁻¹ = _
    rw [h4]
    exact mul_inv_cancel_right _ _
  have h5 : tzo (B := B) hy g = tzo hy ((f.restrictScalars R) ∘ₗ uOf hy x hx) := by
    rw [← hZ, ← Zp_sg hy x hx f]
    exact Zp_congr x hx e.symm _ _
  exact ⟨f, ((cot_unique hy (tzo hy g) (tzo_fst hy g)).unique rfl h5).symm⟩

theorem lin_unique (f f' : Ω[B⁄R] →ₗ[B] M)
    (h : (f.restrictScalars R) ∘ₗ uOf hy x hx = (f'.restrictScalars R) ∘ₗ uOf hy x hx) : f = f' := by
  have h1 : Zp x hx (sg f) (sg_w f) = Zp x hx (sg f') (sg_w f') := by
    rw [Zp_sg hy, Zp_sg hy, h]
  have h2 : spo (sg f) (sg_w f) ≫ xo x hx = spo (sg f') (sg_w f') ≫ xo x hx := mul_right_cancel h1
  have h3 : spMap (sg f) ≫ x = spMap (sg f') ≫ x := congrArg (fun t ↦ t.left) h2
  have h4 : sg f = sg f' := spMap_inj ((cancel_mono x).1 h3)
  refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b ↦ ?_)
  have h5 := congrArg (fun t ↦ (t b).snd) h4
  exact (sg_snd f b).symm.trans (h5.trans (sg_snd f' b))

omit [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [AddCommGroup M] [Module B M] in
theorem uOf_isBaseChange : IsBaseChange B (uOf hy x hx) := by
  refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g ↦ ?_
  letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup B
  letI : Module Bᵐᵒᵖ Q := Module.compHom Q ((RingHom.id B).fromOpposite fun _ _ ↦ mul_comm _ _)
  haveI : IsCentralScalar B Q := ⟨fun _ _ ↦ rfl⟩
  obtain ⟨f, hf⟩ := exists_lin hy x hx (M := Q) g
  exact ⟨f, hf, fun f' hf' ↦ lin_unique hy x hx f' f (hf'.trans hf.symm)⟩

omit [IsOpenImmersion x]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [AddCommGroup M] [Module B M] in
theorem uOf_res (α : B →ₐ[R] B') (x' : Sp B' ⟶ A.left) (hx' : x' ≫ A.hom = spMap (algebraMap R B'))
    (hxx : x' = spMap (α : B →+* B') ≫ x) :
    uOf hy x' hx' = ((SemiHom.of_algHom α).m1 : Ω[B⁄R] →ₗ[R] Ω[B'⁄R]) ∘ₗ uOf hy x hx := by
  let f : Ω[B⁄R] →ₗ[R] Ω[B'⁄R] := (SemiHom.of_algHom α).m1
  have hf : ∀ b m, (f : Ω[B⁄R] →+ Ω[B'⁄R]) (b • m) = (α : B →+* B') b • (f : Ω[B⁄R] →+ Ω[B'⁄R]) m :=
    fun b m ↦ (SemiHom.of_algHom α).oneFormMap_smul_semilinear b m
  have hα : (α : B →+* B').comp (algebraMap R B) = algebraMap R B' := α.comp_algebraMap
  have h0 : (tmap (α : B →+* B') (f : Ω[B⁄R] →+ Ω[B'⁄R]) hf).comp (sz (R := R) B Ω[B⁄R]) = sz B' Ω[B'⁄R] :=
    RingHom.ext fun r ↦ by
      ext
      · exact (fst_tmap _ _ hf _).trans (congrArg (fun t ↦ t r) hα)
      · exact (snd_tmap _ _ hf _).trans (map_zero _)
  have e : (tmap (α : B →+* B') (f : Ω[B⁄R] →+ Ω[B'⁄R]) hf).comp (diagSec R B : B →+* _) =
      (diagSec R B' : B' →+* _).comp (α : B →+* B') := RingHom.ext fun b ↦ by
    ext
    · exact (fst_tmap _ _ hf _).trans ((congrArg α (fst_derSec _ b)).trans (fst_derSec _ _).symm)
    · exact (snd_tmap _ _ hf _).trans ((congrArg f (snd_derSec _ b)).trans
        (((SemiHom.of_algHom α).m1_D b).trans (snd_derSec _ _).symm))
  have h := Zp_map x hx x' hx' (α : B →+* B') hxx hα (f : Ω[B⁄R] →+ Ω[B'⁄R]) hf (diagSec R B : B →+* _) diag_w
    (diagSec R B' : B' →+* _) diag_w e h0
  have h2 := tzo_map hy (α : B →+* B') hα f hf h0 (uOf hy x hx)
  rw [uOf_spec hy x hx, h2] at h
  exact (cot_unique (B := B') (M := Ω[B'⁄R]) hy _ (Zp_diag_fst x' hx')).unique (uOf_spec hy x' hx') h.symm

end Cot

section Family

variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem par_of_family (hS : Stein F) {W : Type} [AddCommGroup W] [Module R W] (g : ℕ) (hW : VB R W g)
    (u : ∀ T, W →ₗ[R] Ω[F.obj T⁄R]) (hu : ∀ T, IsBaseChange (F.obj T) (u T))
    (hc : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (w : W), u T' w = p1 F φ (u T w)) :
    Par F ∧ VB R (Glob1 F) g := by
  obtain ⟨hfin, hproj, hrank⟩ := hW
  obtain ⟨n, a, b, -, -, hab⟩ := Module.Finite.exists_comp_eq_id_of_projective R W
  let lam : Fin n → W →ₗ[R] R := fun k ↦ LinearMap.proj k ∘ₗ b
  let v : Fin n → W := fun k ↦ a (Pi.single k 1)
  have hdec : ∀ w, ∑ k, lam k w • v k = w := fun w ↦ by
    have e1 : a (b w) = w := LinearMap.congr_fun hab w
    conv_rhs => rw [← e1, pi_eq_sum_univ' (b w)]
    simp [lam, v, map_sum]
  let abelian₂ : ∀ k T, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T := fun k T ↦
    (hu T).lift (Algebra.linearMap R (F.obj T) ∘ₗ lam k)
  have hLam : ∀ k T w, abelian₂ k T (u T w) = algebraMap R (F.obj T) (lam k w) := fun k T w ↦
    (hu T).lift_eq _ w
  have hexp : ∀ T (ξ : Ω[F.obj T⁄R]), ∑ k, abelian₂ k T ξ • u T (v k) = ξ := fun T ξ ↦ by
    have e : (∑ k, (LinearMap.toSpanSingleton (F.obj T) _ (u T (v k))) ∘ₗ abelian₂ k T) = LinearMap.id :=
      (hu T).algHom_ext _ _ fun w ↦ by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, hLam,
          LinearMap.id_apply, algebraMap_smul]
        have := congrArg (u T) (hdec w)
        rw [map_sum] at this
        simpa using this
    simpa using LinearMap.congr_fun e ξ
  have hcomp : ∀ k ⦃T T' : C⦄ (φ : T ⟶ T') (ξ : Ω[F.obj T⁄R]),
      mp F φ (abelian₂ k T ξ) = abelian₂ k T' (p1 F φ ξ) := fun k T T' φ ξ ↦ by
    refine (hu T).inductionOn ξ _ (by simp) (fun w ↦ ?_) (fun s n hn ↦ ?_) (fun a b ha hb ↦ ?_)
    · rw [← hc φ w, hLam, hLam]
      exact (mp F φ).commutes _
    · rw [(abelian₂ k T).map_smul, oneFormsMapOfFunctorMorphism_smul, (abelian₂ k T').map_smul, smul_eq_mul, smul_eq_mul, map_mul, hn]
    · simp only [map_add, ha, hb]
  let jm : W →ₗ[R] Glob1 F := LinearMap.codRestrict (Glob1 F) (LinearMap.pi u) fun w T T' φ ↦ hc φ w
  have hj : ∀ w T, (jm w).1 T = u T w := fun _ _ ↦ rfl
  have hinj : Function.Injective jm := (injective_iff_map_eq_zero jm).2 fun w h ↦ by
    have h0 : ∀ k, lam k w = 0 := fun k ↦ hS.2 (by
      rw [map_zero]
      funext T
      refine ((hLam k T w).symm.trans ?_)
      rw [← hj, h]
      exact map_zero _)
    rw [← hdec w]
    simp [h0]
  have hsurj : Function.Surjective jm := fun ω ↦ by
    have hd : ∀ k, ∃ r : R, Algebra.linearMap R (C0 F) r = fun T ↦ abelian₂ k T (ω.1 T) := fun k ↦
      (hS.1 _).1 (by
        funext T T' φ
        rw [amitsur_d0_apply, hcomp, ← ω.2 φ, sub_self]
        rfl)
    choose r hr using hd
    refine ⟨∑ k, r k • v k, Subtype.ext (funext fun T ↦ ?_)⟩
    rw [hj, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun k _ ↦ ?_) (hexp T (ω.1 T))
    rw [map_smul, ← congrFun (hr k) T, ← algebraMap_smul (F.obj T) (r k) (u T (v k))]
    rfl
  let e : W ≃ₗ[R] Glob1 F := LinearEquiv.ofBijective jm ⟨hinj, hsurj⟩
  have he : ∀ T w, evForm F T (e w) = u T w := fun _ _ ↦ rfl
  refine ⟨fun T ↦ IsBaseChange.of_lift_unique _ fun Q _ _ _ _ q ↦ ?_,
    Module.Finite.equiv e, Module.Projective.of_equiv e, fun p ↦ ?_⟩
  · refine ⟨(hu T).lift (q ∘ₗ e.toLinearMap), ?_, fun q' hq' ↦ ?_⟩
    · refine LinearMap.ext fun ω ↦ ?_
      obtain ⟨w, rfl⟩ := e.surjective ω
      change (hu T).lift (q ∘ₗ e.toLinearMap) (evForm F T (e w)) = q (e w)
      rw [he]
      exact (hu T).lift_eq _ w
    · refine (hu T).algHom_ext _ _ fun w ↦ ?_
      rw [(hu T).lift_eq, ← he]
      exact LinearMap.congr_fun hq' (e w)
  · rw [← Module.rankAtStalk_eq_of_equiv e]
    exact hrank p

end Family

theorem parSt : CotSt → SteinSt → ParSt := by
  intro hc hs R _ A _ g hab hg
  obtain ⟨W, _, _, _, _, y₀, hV, hy⟩ := hc R A.left A.hom η[A].left g (Over.w η[A]) hg
  haveI : ∀ U : A.left.affineOpens, IsOpenImmersion (affPt A.hom U) := fun U ↦
    IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact par_of_family (OAff A.hom) (hs R A g hab hg) g hV
    (fun T ↦ uOf hy (affPt A.hom T.unop) (affPt_w A.hom T.unop))
    (fun T ↦ uOf_isBaseChange hy (affPt A.hom T.unop) (affPt_w A.hom T.unop))
    (fun T T' φ w ↦ congrArg (fun t ↦ t w) (uOf_res hy (affPt A.hom T.unop) (affPt_w A.hom T.unop)
      (Sec.res A.hom (leOfHom φ.unop)) (affPt A.hom T'.unop) (affPt_w A.hom T'.unop)
      (affPt_res A.hom (leOfHom φ.unop)).symm))

end GlobalTheory.CompanionTheory.AbForms
