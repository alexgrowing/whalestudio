import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineFiniteProjectiveRankAtStalk

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FinTrace

open GlobalTheory.FiniteAmple GlobalTheory.LB

section Algebra

variable {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

def tr (φ : A →+* B) : B →+ A := letI := φ.toAlgebra; (Algebra.trace A B).toAddMonoidHom

theorem tr_mul (φ : A →+* B) (a : A) (b : B) : tr φ (φ a * b) = a * tr φ b := by
  letI := φ.toAlgebra
  change Algebra.trace A B (algebraMap A B a * b) = a * Algebra.trace A B b
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem tr_of_isPushout {φ : A →+* B} {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'}
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β)
      (CommRingCat.ofHom φ'))
    (h : FinFree φ) (b : B) : tr φ' (β b) = α (tr φ b) := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  haveI : Module.Finite A B := h.1
  haveI : Module.Free A B := h.2
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  change LinearMap.trace A' B' (Algebra.lmul A' B' (β b)) =
    algebraMap A A' (LinearMap.trace A B (Algebra.lmul A B b))
  rw [← LinearMap.trace_baseChange, ← LinearMap.trace_conj' _ hb.equiv]
  congr 1
  ext y
  obtain ⟨t, rfl⟩ := hb.equiv.surjective y
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [IsBaseChange.equiv_tmul]; rfl
  | add s t hs ht => simp only [map_add, hs, ht]

theorem tr_map (φ : A →+* B) (h : FinFree φ) (r : ℕ)
    (hr : Nontrivial A → (letI := φ.toAlgebra; Module.finrank A B) = r) (a : A) :
    tr φ (φ a) = r * a := by
  letI := φ.toAlgebra
  haveI : Module.Finite A B := h.1
  haveI : Module.Free A B := h.2
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  · change Algebra.trace A B (algebraMap A B a) = _
    rw [Algebra.trace_algebraMap, hr hA, nsmul_eq_mul]

theorem exists_finFree_away_of_finitePresentation {φ : A →+* B} (hf : φ.Finite) (hfl : φ.Flat)
    (hfp : φ.FinitePresentation) (p : PrimeSpectrum A) :
    ∃ r ∉ p.asIdeal, ∀ {A' B' : Type} [CommRing A'] [CommRing B'] {α : A →+* A'} {β : B →+* B'}
      {φ' : A' →+* B'},
      IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β)
        (CommRingCat.ofHom φ') → IsUnit (α r) → FinFree φ' := by
  algebraize [φ]
  have : Module.FinitePresentation A B := Module.FinitePresentation.of_finite_of_finitePresentation A B
  have : Module.Free (Localization p.asIdeal.primeCompl) (LocalizedModule p.asIdeal.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl B)
    (Localization p.asIdeal.primeCompl)
  refine ⟨r, hr, ?_⟩
  intro A' B' _ _ α β φ' H hu
  algebraize [α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  refine ⟨Module.Finite.equiv hb.equiv, ?_⟩
  letI : Algebra (Localization.Away r) A' := (IsLocalization.Away.lift r (g := α) hu).toAlgebra
  have : IsScalarTower A (Localization.Away r) A' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hu x).symm
  have h₁ : Module.Free (Localization.Away r) (TensorProduct A (Localization.Away r) B) :=
    Module.Free.of_equiv (IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (.powers r) B)).equiv.symm
  exact Module.Free.of_equiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away r) A' A' B).trans hb.equiv)

end Algebra

section Geometry

open GlobalTheory.FlatNorm (FreeOpen)

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

theorem resG_app_eq {V W : Y.Opens} (h : W ≤ V) (a : Γ(Y, V)) :
    resG X (f.preimage_mono h) ((f.app V).hom a) = (f.app W).hom (resG Y h a) := by
  exact congr($(f.naturality (homOfLE h).op).hom a).symm

theorem resG_tr [IsFinite f] {V W : Y.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    (hF : FinFree (f.app V).hom) (b : Γ(X, f ⁻¹ᵁ V)) :
    resG Y h (tr (f.app V).hom b) = tr (f.app W).hom (resG X (f.preimage_mono h) b) :=
  (tr_of_isPushout (isPushout_app f hV hW h) hF b).symm

variable [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

omit [Flat f] [LocallyOfFinitePresentation f] in

theorem isAffineOpen_preimage {V : Y.Opens} (hV : IsAffineOpen V) : IsAffineOpen (f ⁻¹ᵁ V) :=
  hV.preimage f

theorem exists_finFree_app_of_finitePresentation {y : Y} {U : Y.Opens} (hy : y ∈ U) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧ V ≤ U ∧ FinFree (f.app V).hom := by
  obtain ⟨V, hV, hyV, hle⟩ := exists_isAffineOpen_mem_and_subset hy
  have hfl : (f.app V).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact f.flat_appLE hV (hV.preimage f) _
  have hfp : (f.app V).hom.FinitePresentation := by
    rw [Scheme.Hom.app_eq_appLE]
    exact f.finitePresentation_appLE hV (hV.preimage f) _
  obtain ⟨r, hr, H⟩ := exists_finFree_away_of_finitePresentation
    (f.finite_app V hV) hfl hfp (hV.primeIdealOf ⟨y, hyV⟩)
  refine ⟨Y.basicOpen r, hV.basicOpen r, ?_, (Y.basicOpen_le r).trans hle,
    H (isPushout_app f hV (hV.basicOpen r) (Y.basicOpen_le r)) (Y.toRingedSpace.isUnit_res_basicOpen r)⟩
  have e := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
  have h₁ : hV.primeIdealOf ⟨y, hyV⟩ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen r := by
    rw [hV.fromSpec_preimage_basicOpen]
    exact hr
  exact (congrArg (· ∈ Y.basicOpen r) e).mp h₁

theorem le_iSup_freeOpen (V : Y.Opens) : V ≤ ⨆ W : FreeOpen f V, W.1 := fun _ hx => by
  obtain ⟨W, h₁, h₂, h₃, h₄⟩ := exists_finFree_app_of_finitePresentation f hx
  exact Opens.mem_iSup.2 ⟨⟨W, h₁, h₃, h₄⟩, h₂⟩

theorem ext_freeOpen {V : Y.Opens} {a b : Γ(Y, V)}
    (h : ∀ W : FreeOpen f V, resG Y W.2.2.1 a = resG Y W.2.2.1 b) : a = b :=
  fun_ext_of_cover _ (fun W : FreeOpen f V => W.2.2.1) (le_iSup_freeOpen f V) h

theorem finrank_app_of_finrank (r : ℕ) (hr : ∀ y, f.finrank y = r) (V : Y.Opens) (hV : IsAffineOpen V)
    (hF : FinFree (f.app V).hom) (hN : Nontrivial Γ(Y, V)) :
    (letI := (f.app V).hom.toAlgebra; Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) = r := by
  letI := (f.app V).hom.toAlgebra
  haveI : Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hF.2
  haveI : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hF.1
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum Γ(Y, V)) := inferInstance
  have e := (GlobalTheory.AbelianMulFin.affine_finite_projective_rankAtStalk f r hr V hV).2.2.2 p
  rw [Module.rankAtStalk_eq_finrank_of_free] at e
  exact e

theorem exists_trFun (V : Y.Opens) (b : Γ(X, f ⁻¹ᵁ V)) : ∃ a : Γ(Y, V), ∀ W : FreeOpen f V,
    resG Y W.2.2.1 a = tr (f.app W.1).hom (resG X (f.preimage_mono W.2.2.1) b) :=
  exists_fun_of_cover _ (fun W : FreeOpen f V => W.2.2.1) (le_iSup_freeOpen f V) _ fun W W' =>
    ext_freeOpen f fun O => by
      rw [resG_resG, resG_resG, resG_tr f W.2.1 O.2.1 _ W.2.2.2, resG_tr f W'.2.1 O.2.1 _ W'.2.2.2,
        resG_resG, resG_resG]

def trFun (V : Y.Opens) : Γ(X, f ⁻¹ᵁ V) →+ Γ(Y, V) where
  toFun b := (exists_trFun f V b).choose
  map_zero' := ext_freeOpen f fun W => by
    rw [(exists_trFun f V 0).choose_spec W, map_zero, map_zero, map_zero]
  map_add' a b := ext_freeOpen f fun W => by
    rw [(exists_trFun f V _).choose_spec W, map_add, map_add, map_add,
      (exists_trFun f V a).choose_spec W, (exists_trFun f V b).choose_spec W]

theorem resG_trFun_free {V : Y.Opens} (b : Γ(X, f ⁻¹ᵁ V)) (W : FreeOpen f V) :
    resG Y W.2.2.1 (trFun f V b) = tr (f.app W.1).hom (resG X (f.preimage_mono W.2.2.1) b) :=
  (exists_trFun f V b).choose_spec W

theorem resG_trFun {V W : Y.Opens} (h : W ≤ V) (b : Γ(X, f ⁻¹ᵁ V)) :
    resG Y h (trFun f V b) = trFun f W (resG X (f.preimage_mono h) b) :=
  ext_freeOpen f fun O => by
    rw [resG_trFun_free, resG_resG, resG_resG]
    exact resG_trFun_free f b ⟨O.1, O.2.1, O.2.2.1.trans h, O.2.2.2⟩

theorem trFun_mul {V : Y.Opens} (a : Γ(Y, V)) (b : Γ(X, f ⁻¹ᵁ V)) :
    trFun f V ((f.app V).hom a * b) = a * trFun f V b :=
  ext_freeOpen f fun W => by
    rw [resG_trFun_free, map_mul (resG X _), map_mul (resG Y _), resG_app_eq, tr_mul, resG_trFun_free]

theorem trFun_app (r : ℕ) (hr : ∀ V : Y.Opens, IsAffineOpen V → FinFree (f.app V).hom →
      Nontrivial Γ(Y, V) → (letI := (f.app V).hom.toAlgebra; Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) = r)
    {V : Y.Opens} (a : Γ(Y, V)) : trFun f V ((f.app V).hom a) = r * a :=
  ext_freeOpen f fun W => by
    rw [resG_trFun_free, resG_app_eq, tr_map _ W.2.2.2 r (hr W.1 W.2.1 W.2.2.2), map_mul, map_natCast]

end Geometry

end GlobalTheory.FinTrace

namespace GlobalTheory.FinTrace

open GlobalTheory.FiniteAmple GlobalTheory.LB GlobalTheory.AbLaw

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

section Sections

variable {L : LB Y}

abbrev pj (L : LB Y) (i : L.ι) : (L.pull f).ι := fun _ => i

theorem preimage_inf_le (V : Y.Opens) (i : L.ι) :
    f ⁻¹ᵁ (V ⊓ L.U i) ≤ f ⁻¹ᵁ V ⊓ (L.pull f).U (pj f L i) :=
  fun _ hx => ⟨hx.1, (pull_U f (pj f L i)).ge hx.2⟩

def trCoord (V : Y.Opens) (s : SecOn (L.pull f) (f ⁻¹ᵁ V)) (i : L.ι) : Γ(Y, V ⊓ L.U i) :=
  trFun f (V ⊓ L.U i) (resG X (preimage_inf_le f V i) (coord s (pj f L i)))

theorem trCoord_mem (V : Y.Opens) (s : SecOn (L.pull f) (f ⁻¹ᵁ V)) : trCoord f V s ∈ secOn L V := by
  intro i j
  have e := coord_rel s (pj f L i) (pj f L j) (W := f ⁻¹ᵁ (V ⊓ L.U i ⊓ L.U j))
    (fun _ hx => ⟨hx.1.1, (pull_U f (pj f L i)).ge hx.1.2⟩)
    (fun _ hx => ⟨hx.1.1, (pull_U f (pj f L j)).ge hx.2⟩)
    (fun _ hx => ⟨(pull_U f (pj f L i)).ge hx.1.2, (pull_U f (pj f L j)).ge hx.2⟩)
  erw [resG_pull_g] at e
  simp only [trCoord, resG_trFun, resG_resG]
  rw [← trFun_mul, ← resG_app_eq, resG_app]
  exact congrArg (trFun f _) e

def trSec (V : Y.Opens) : SecOn (L.pull f) (f ⁻¹ᵁ V) →+ SecOn L V where
  toFun s := mkSec (trCoord f V s) (trCoord_mem f V s)
  map_zero' := sec_ext fun i => by simp [trCoord]
  map_add' s t := sec_ext fun i => by simp [trCoord]

@[simp] theorem coord_trSec (V : Y.Opens) (s : SecOn (L.pull f) (f ⁻¹ᵁ V)) (i : L.ι) :
    coord (trSec f V s) i = trFun f (V ⊓ L.U i) (resG X (preimage_inf_le f V i) (coord s (pj f L i))) :=
  rfl

theorem trSec_smul (V : Y.Opens) (a : Γ(Y, V)) (s : SecOn (L.pull f) (f ⁻¹ᵁ V)) :
    trSec f V ((f.app V).hom a • s) = a • trSec f V s :=
  sec_ext fun i => by
    rw [coord_trSec, coord_smul, coord_smul, coord_trSec, map_mul, resG_resG, ← trFun_mul,
      resG_app_eq]

theorem trSec_restrict {V W : Y.Opens} (h : W ≤ V) (s : SecOn (L.pull f) (f ⁻¹ᵁ V)) :
    trSec f W (SecOn.restrict (L.pull f) (f.preimage_mono h) s) = SecOn.restrict L h (trSec f V s) :=
  sec_ext fun i => by
    rw [coord_trSec, SecOn.coord_restrict, SecOn.coord_restrict, coord_trSec]
    erw [resG_trFun, resG_resG, resG_resG]

theorem trSec_pull (r : ℕ) (hr : ∀ V : Y.Opens, IsAffineOpen V → FinFree (f.app V).hom →
      Nontrivial Γ(Y, V) → (letI := (f.app V).hom.toAlgebra; Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) = r)
    (V : Y.Opens) (s : SecOn L V) :
    trSec f V (SecOn.pull L f V s) = (r : Γ(Y, V)) • s :=
  sec_ext fun i => by
    rw [coord_trSec, coord_smul]
    erw [coord_pullSec, resG_appLE]
    rw [map_natCast, ← trFun_app f r hr (coord s i), Scheme.Hom.app_eq_appLE]

end Sections

end GlobalTheory.FinTrace

namespace GlobalTheory.FinTrace

open GlobalTheory.FiniteAmple GlobalTheory.LB GlobalTheory.AbLaw

section Cech

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {R : Type} [CommRing R] (q : Y ⟶ Spec (CommRingCat.of R))

theorem comp_eq_comp_id : f ≫ q = (f ≫ q) ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]

theorem resG_cst_comp {V : Y.Opens} {V' : X.Opens} (e : f ⁻¹ᵁ V ≤ V') (r : R) :
    resG X e (cst (f ≫ q) V' r) = (f.app V).hom (cst q V r) := by
  rw [Scheme.Hom.app_eq_appLE, appLE_cst (comp_eq_comp_id f q) (le_refl (f ⁻¹ᵁ V)) r]
  exact rs_cst (f ≫ q) e r

theorem natCast_eq_cst (V : Y.Opens) (r : ℕ) : cst q V (r : R) = (r : Γ(Y, V)) := map_natCast _ r

variable [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] {L : LB Y}

variable (L) in

def trR (V : Y.Opens) (V' : X.Opens) (e : f ⁻¹ᵁ V ≤ V') :
    SecOnR (f ≫ q) (L.pull f) V' →ₗ[R] SecOnR q L V where
  toFun x := SecOnR.of q L V (trSec f V (SecOn.restrict (L.pull f) e ((SecOnR.of (f ≫ q) _ V').symm x)))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    rw [SecOnR.smul_def, LinearEquiv.map_smul, (SecOn.restrict (L.pull f) e).map_smulₛₗ]
    erw [resG_cst_comp f q e r, trSec_smul]
    rfl

variable (L) in

def trCube {κ : Type} (D : κ → Y.Opens) :
    secCube (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i) ⟶ secCube q L D :=
  GlobalTheory.Cube.homMk (fun s => trR f q L (⨅ i ∈ s, D i) (⨅ i ∈ s, f ⁻¹ᵁ D i) (preimage_biInf D f s).le)
    fun {s t} h x => by
      show trSec f _ (SecOn.restrict (L.pull f) (preimage_biInf D f t).le
          (SecOn.restrict (L.pull f) (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) x)) =
        SecOn.restrict L (iInf_le_iInf_of_subset D h)
          (trSec f _ (SecOn.restrict (L.pull f) (preimage_biInf D f s).le x))
      rw [← trSec_restrict]
      congr 1
      exact (SecOn.restrict_restrict (M := L.pull f) _ _ (x : SecOn (L.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i))).trans
        (SecOn.restrict_restrict _ _ _).symm

variable (L) in

def pullCube {κ : Type} (D : κ → Y.Opens) :
    secCube q L D ⟶ secCube (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i) :=
  GlobalTheory.Cube.homMk (fun s => secCubePull L D (comp_eq_comp_id f q) s)
    fun h x => secCubePull_res D (comp_eq_comp_id f q) h x

end Cech

end GlobalTheory.FinTrace

namespace GlobalTheory.FinTrace

open GlobalTheory.FiniteAmple GlobalTheory.LB GlobalTheory.AbLaw

theorem exactAt_of_isIso_comp {R : Type} [CommRing R] {C D : CochainComplex (ModuleCat.{0} R) ℕ}
    (i : C ⟶ D) (p : D ⟶ C) [IsIso (i ≫ p)] {n : ℕ} (hD : D.ExactAt n) : C.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hD ⊢
  rw [IsZero.iff_id_eq_zero]
  have e : 𝟙 (C.homology n) = HomologicalComplex.homologyMap i n ≫
      HomologicalComplex.homologyMap p n ≫ inv (HomologicalComplex.homologyMap (i ≫ p) n) := by
    rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, IsIso.hom_inv_id]
  rw [e, hD.eq_of_tgt (HomologicalComplex.homologyMap i n) 0, zero_comp]

def smulCube {R : Type} [CommRing R] {κ : Type} (A : GlobalTheory.Cube.{0} κ R) (u : Rˣ) : A ≅ A :=
  GlobalTheory.Cube.isoMk (fun _ => LinearEquiv.smulOfUnit u) fun h x => ((GlobalTheory.Cube.res A h).map_smul (u : R) x).symm

section Cech

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {R : Type} [CommRing R] (q : Y ⟶ Spec (CommRingCat.of R))
  [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

theorem pullCube_trCube (r : ℕ) (hr : ∀ V : Y.Opens, IsAffineOpen V → FinFree (f.app V).hom →
      Nontrivial Γ(Y, V) → (letI := (f.app V).hom.toAlgebra; Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) = r)
    (hu : IsUnit (r : R)) (L : LB Y) {κ : Type} (D : κ → Y.Opens) :
    pullCube f q L D ≫ trCube f q L D = (smulCube (secCube q L D) hu.unit).hom := by
  ext s x
  obtain ⟨y, rfl⟩ : ∃ y : SecOn L (⨅ i ∈ s, D i), y = x := ⟨x, rfl⟩
  change trSec f _ (SecOn.restrict (L.pull f) (preimage_biInf D f s).le
    (SecOn.pullLE L f _ _ (preimage_biInf D f s).ge y)) = ((hu.unit : R)) • (show SecOnR q L _ from y)
  rw [SecOn.restrict_pullLE]
  erw [SecOn.pullLE_self, trSec_pull f r hr]
  rw [IsUnit.unit_spec, SecOnR.smul_def, natCast_eq_cst]
  rfl

theorem cechLB_exactAt_of_pull (r : ℕ) (hr : ∀ V : Y.Opens, IsAffineOpen V → FinFree (f.app V).hom →
      Nontrivial Γ(Y, V) → (letI := (f.app V).hom.toAlgebra; Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) = r)
    (hu : IsUnit (r : R)) (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) (n : ℕ)
    (h : (cechLB (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i)).ExactAt n) : (cechLB q L D).ExactAt n := by
  haveI : IsIso ((cechFunctor κ R).map (pullCube f q L D) ≫ (cechFunctor κ R).map (trCube f q L D)) := by
    rw [← Functor.map_comp, pullCube_trCube f q r hr hu]
    infer_instance
  exact exactAt_of_isIso_comp ((cechFunctor κ R).map (pullCube f q L D))
    ((cechFunctor κ R).map (trCube f q L D)) h

omit [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] in

def funCube (a : Γ(Y, ⊤)) (L : LB Y) {κ : Type} (D : κ → Y.Opens) : secCube q L D ⟶ secCube q L D :=
  secCubeMap q D (fun V => LinearMap.lsmul Γ(Y, V) (SecOn L V) (rs Y (le_top : V ≤ ⊤) a))
    fun h s => by
      rw [LinearMap.lsmul_apply, LinearMap.lsmul_apply, map_smulₛₗ, rs_rs]

def cechPull (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) :
    cechLB q L D ⟶ cechLB (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i) :=
  (cechFunctor κ R).map (pullCube f q L D)

def cechTr (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) :
    cechLB (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i) ⟶ cechLB q L D :=
  (cechFunctor κ R).map (trCube f q L D)

def cechSMul (a : Γ(Y, ⊤)) (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) :
    cechLB q L D ⟶ cechLB q L D :=
  (cechFunctor κ R).map (funCube q a L D)

theorem pullCube_trCube_inv (r : ℕ) (hr : ∀ y, f.finrank y = r) (hu : IsUnit (r : Γ(Y, ⊤)))
    (L : LB Y) {κ : Type} (D : κ → Y.Opens) :
    pullCube f q L D ≫ trCube f q L D ≫ funCube q (hu.unit⁻¹).val L D = 𝟙 _ := by
  ext s x
  obtain ⟨y, rfl⟩ : ∃ y : SecOn L (⨅ i ∈ s, D i), y = x := ⟨x, rfl⟩
  change rs Y (le_top : (⨅ i ∈ s, D i) ≤ ⊤) (hu.unit⁻¹).val •
    trSec f _ (SecOn.restrict (L.pull f) (preimage_biInf D f s).le
      (SecOn.pullLE L f _ _ (preimage_biInf D f s).ge y)) = y
  rw [SecOn.restrict_pullLE]
  erw [SecOn.pullLE_self, trSec_pull f r (finrank_app_of_finrank f r hr)]
  rw [smul_smul, ← map_natCast (rs Y (le_top : (⨅ i ∈ s, D i) ≤ ⊤)) r, ← map_mul, IsUnit.val_inv_mul,
    map_one, one_smul]

theorem cechLB_retract (r : ℕ) (hr : ∀ y, f.finrank y = r) (hu : IsUnit (r : Γ(Y, ⊤)))
    (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) :
    cechPull f q L D ≫ (cechTr f q L D ≫ cechSMul q (hu.unit⁻¹).val L D) = 𝟙 (cechLB q L D) := by
  have e := congrArg (cechFunctor κ R).map (pullCube_trCube_inv f q r hr hu L D)
  rw [Functor.map_comp, Functor.map_comp, CategoryTheory.Functor.map_id] at e
  exact e

theorem cechLB_retract_and_exactAt (r : ℕ) (hr : ∀ y, f.finrank y = r) (hu : IsUnit (r : Γ(Y, ⊤)))
    (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) :
    cechPull f q L D ≫ (cechTr f q L D ≫ cechSMul q (hu.unit⁻¹).val L D) = 𝟙 (cechLB q L D) ∧
      ∀ n : ℕ, (cechLB (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i)).ExactAt n → (cechLB q L D).ExactAt n := by
  refine ⟨cechLB_retract f q r hr hu L D, fun n h => ?_⟩
  haveI : IsIso (cechPull f q L D ≫ (cechTr f q L D ≫ cechSMul q (hu.unit⁻¹).val L D)) := by
    rw [cechLB_retract f q r hr hu]
    infer_instance
  exact exactAt_of_isIso_comp (cechPull f q L D) (cechTr f q L D ≫ cechSMul q (hu.unit⁻¹).val L D) h

theorem cechLB_exactAt_of_pull_of_finrank (r : ℕ) (hr : ∀ y, f.finrank y = r)
    (hu : IsUnit (r : Γ(Y, ⊤))) (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) (n : ℕ)
    (h : (cechLB (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i)).ExactAt n) : (cechLB q L D).ExactAt n :=
  (cechLB_retract_and_exactAt f q r hr hu L D).2 n h

end Cech

end GlobalTheory.FinTrace
