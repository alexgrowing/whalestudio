import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeConj

abbrev cc : Sp ℂ ⟶ Sp ℂ := spMap (starRingEnd ℂ)

theorem cc_cc : cc ≫ cc = 𝟙 (Sp ℂ) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by simp))

@[reassoc] theorem cc_cc_assoc' {Y : Scheme.{0}} (f : Sp ℂ ⟶ Y) : cc ≫ cc ≫ f = f := by
  rw [← Category.assoc, cc_cc, Category.id_comp]

abbrev tw (T : Over (Sp ℂ)) : Over (Sp ℂ) := Over.mk (T.hom ≫ cc)

def twEquiv (A T : Over (Sp ℂ)) : (T ⟶ tw A) ≃ (tw T ⟶ A) where
  toFun f := Over.homMk f.left (by
    have := Over.w f
    simp only [Over.mk_hom] at this ⊢
    rw [← this, Category.assoc, Category.assoc, cc_cc, Category.comp_id])
  invFun f := Over.homMk f.left (by
    have := Over.w f
    simp only [Over.mk_hom] at this ⊢
    rw [← Category.assoc, this, Category.assoc, cc_cc, Category.comp_id])
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

@[simp] theorem twEquiv_left {A T : Over (Sp ℂ)} (x : T ⟶ tw A) : (twEquiv A T x).left = x.left := rfl

abbrev twF (A : Over (Sp ℂ)) [GrpObj A] : (Over (Sp ℂ))ᵒᵖ ⥤ GrpCat.{0} :=
  (Over.map cc).op ⋙ yonedaGrpObj A

def twRep (A : Over (Sp ℂ)) [GrpObj A] : (twF A ⋙ forget _).RepresentableBy (tw A) where
  homEquiv {T} := twEquiv A T
  homEquiv_comp f g := Over.OverMorphism.ext rfl

scoped instance twGrp (A : Over (Sp ℂ)) [GrpObj A] : GrpObj (tw A) := GrpObj.ofRepresentableBy _ _ (twRep A)

theorem twEquiv_mul {A T : Over (Sp ℂ)} [GrpObj A] (x y : T ⟶ tw A) :
    twEquiv A T (x * y) = twEquiv A T x * twEquiv A T y :=
  ((yonedaGrpObjIsoOfRepresentableBy _ _ (twRep A)).hom.app (Opposite.op T)).hom.map_mul x y

theorem twEquiv_one {A T : Over (Sp ℂ)} [GrpObj A] : twEquiv A T 1 = 1 :=
  ((yonedaGrpObjIsoOfRepresentableBy _ _ (twRep A)).hom.app (Opposite.op T)).hom.map_one

def pc {A : Over (Sp ℂ)} (s : 𝟙_ (Over (Sp ℂ)) ⟶ A) : 𝟙_ (Over (Sp ℂ)) ⟶ tw A :=
  (twEquiv A _).symm (toUnit _ ≫ s)

theorem toUnit_left : (toUnit (tw (𝟙_ (Over (Sp ℂ))))).left = cc := by
  simpa using Over.w (toUnit (tw (𝟙_ (Over (Sp ℂ)))))

theorem pc_left {A : Over (Sp ℂ)} (s : 𝟙_ (Over (Sp ℂ)) ⟶ A) : (pc s).left = cc ≫ s.left := by
  show (toUnit _ ≫ s).left = _
  rw [Over.comp_left, toUnit_left]

theorem twEquiv_pc {A : Over (Sp ℂ)} (s : 𝟙_ (Over (Sp ℂ)) ⟶ A) : twEquiv A _ (pc s) = toUnit _ ≫ s :=
  (twEquiv A _).apply_symm_apply _

theorem pc_mul {A : Over (Sp ℂ)} [GrpObj A] (s t : 𝟙_ (Over (Sp ℂ)) ⟶ A) : pc (s * t) = pc s * pc t :=
  (twEquiv A _).injective (by rw [twEquiv_mul, twEquiv_pc, twEquiv_pc, twEquiv_pc, comp_mul])

theorem pc_one {A : Over (Sp ℂ)} [GrpObj A] : pc (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = 1 :=
  (twEquiv A _).injective (by rw [twEquiv_one, twEquiv_pc, comp_one])

theorem pc_injective {A : Over (Sp ℂ)} : Function.Injective (pc (A := A)) := fun s t h => by
  have h1 := congrArg (fun r => cc ≫ r.left) h
  simp only [pc_left, cc_cc_assoc'] at h1
  exact Over.OverMorphism.ext h1

theorem pc_surjective {A : Over (Sp ℂ)} : Function.Surjective (pc (A := A)) := fun r => by
  have hr : r.left ≫ A.hom = cc := by
    have := Over.w r
    simp only [Over.mk_hom] at this
    have h2 := congrArg (· ≫ cc) this
    simpa [cc_cc] using h2
  refine ⟨Over.homMk (cc ≫ r.left) (by simp [hr, cc_cc]), Over.OverMorphism.ext ?_⟩
  rw [pc_left]
  simp [cc_cc_assoc']

def ccIso : Sp ℂ ≅ Sp ℂ := ⟨cc, cc, cc_cc, cc_cc⟩

theorem isGrpPullback_tw {X : Scheme.{0}} {G : Over X} [GrpObj G] {A : Over (Sp ℂ)} [GrpObj A]
    {z : Sp ℂ ⟶ X} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ) :
    IsGrpPullback (tw A) G (cc ≫ z) φ := by
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · exact h.1.of_iso (Iso.refl _) (Iso.refl _) ccIso (Iso.refl _) (by simp) (by simp [ccIso]) (by simp)
      (by simp [ccIso, cc_cc_assoc'])
  · let e : Over.mk ((tw T).hom ≫ z) ⟶ Over.mk (T.hom ≫ cc ≫ z) := Over.homMk (𝟙 _) (by simp)
    have h1 := h.2 (tw T) (twEquiv A T x) (twEquiv A T y) (e ≫ x₀) (e ≫ y₀)
      (by simpa [e] using hx) (by simpa [e] using hy)
    rw [← comp_mul, ← twEquiv_mul] at h1
    simpa [e] using h1

theorem spMap_inv {R : Type} [CommRing R] (ψ : R →+* R) (hψ : ∀ a, ψ (ψ a) = a) :
    spMap ψ ≫ spMap ψ = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext hψ))

theorem top_le_comp {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') {Y : Scheme.{0}} {x : Sp R ⟶ Y}
    {U : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U := fun p _ => by
  have h1 : (spMap ψ) p ∈ x ⁻¹ᵁ U := h trivial
  simpa using h1

theorem top_le_inv {R : Type} [CommRing R] (ψ : R →+* R) (hψ : ∀ a, ψ (ψ a) = a) {Y : Scheme.{0}} {x : Sp R ⟶ Y}
    {U : Y.Opens} : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  refine ⟨fun h => ?_, top_le_comp ψ⟩
  have h1 := top_le_comp ψ h
  rwa [← Category.assoc, spMap_inv ψ hψ, Category.id_comp] at h1

theorem val_spMap {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') {Y : Scheme.{0}} (x : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U) (f : Γ(Y, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (((spMap ψ ≫ x).appLE U ⊤ h').hom f) =
      ψ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((x.appLE U ⊤ h).hom f)) := by
  have e := Scheme.Hom.appLE_comp_appLE (spMap ψ) x U ⊤ ⊤ h le_top
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have e2 : (spMap ψ).appLE ⊤ ⊤ le_top = (spMap ψ).appTop := by
    simp only [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [← e, e2]
  exact congrArg (fun k => k.hom ((Scheme.Hom.appLE x U ⊤ h).hom f)) n

theorem valAt'_cc {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (cc ≫ x) U f = starRingEnd ℂ (valAt' x U f) := by
  have hi := top_le_inv (starRingEnd ℂ) (fun a => by simp) (x := x) (U := U)
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [dif_pos h, dif_pos (hi.2 h)]
    exact val_spMap _ x U h _ f
  · rw [dif_neg h, dif_neg (fun h' => h (hi.1 h')), map_zero]

section Analysis

variable {g : ℕ}

def cjL (L : (Fin g → ℂ) →L[ℂ] ℂ) : (Fin g → ℂ) →L[ℂ] ℂ :=
  ⟨{ toFun := fun w => starRingEnd ℂ (L (star w))
     map_add' := fun a b => by simp
     map_smul' := fun c a => by simp },
    Complex.continuous_conj.comp (L.continuous.comp continuous_star)⟩

theorem hasFDerivWithinAt_conj {F : (Fin g → ℂ) → ℂ} {L : (Fin g → ℂ) →L[ℂ] ℂ} {s : Set (Fin g → ℂ)}
    {x : Fin g → ℂ} (h : HasFDerivWithinAt F L s (star x)) :
    HasFDerivWithinAt (fun z => starRingEnd ℂ (F (star z))) (cjL L) (star ⁻¹' s) x := by
  have h1 := h.restrictScalars ℝ
  have h2 : HasFDerivWithinAt (star : (Fin g → ℂ) → (Fin g → ℂ))
      (((starL' ℝ : (Fin g → ℂ) ≃L[ℝ] (Fin g → ℂ))) : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ)) (star ⁻¹' s) x :=
    (starL' ℝ : (Fin g → ℂ) ≃L[ℝ] (Fin g → ℂ)).hasFDerivAt.hasFDerivWithinAt
  have h3 := h1.comp x h2 (fun _ h => h)
  have h4 := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
    (x := F (star x))).comp_hasFDerivWithinAt x h3
  exact HasFDerivWithinAt.of_restrictScalars ℝ h4 (by ext w; rfl)

theorem differentiableOn_conj {F : (Fin g → ℂ) → ℂ} {s : Set (Fin g → ℂ)} (h : DifferentiableOn ℂ F s) :
    DifferentiableOn ℂ (fun z => starRingEnd ℂ (F (star z))) (star ⁻¹' s) := fun _ hx =>
  (hasFDerivWithinAt_conj (h _ hx).hasFDerivWithinAt).differentiableWithinAt

theorem fderiv_conj (F : (Fin g → ℂ) → ℂ) (x w : Fin g → ℂ) :
    fderiv ℂ (fun z => starRingEnd ℂ (F (star z))) x w = starRingEnd ℂ (fderiv ℂ F (star x) (star w)) := by
  by_cases h : DifferentiableAt ℂ F (star x)
  · have h1 := hasFDerivWithinAt_conj (s := Set.univ) h.hasFDerivAt.hasFDerivWithinAt
    rw [Set.preimage_univ, hasFDerivWithinAt_univ] at h1
    rw [h1.fderiv]
    rfl
  · have h' : ¬ DifferentiableAt ℂ (fun z => starRingEnd ℂ (F (star z))) x := fun hd => h (by
      have h1 := hasFDerivWithinAt_conj (F := fun z => starRingEnd ℂ (F (star z))) (x := star x)
        (s := Set.univ) (by rw [star_star]; exact hd.hasFDerivAt.hasFDerivWithinAt)
      rw [Set.preimage_univ, hasFDerivWithinAt_univ] at h1
      simpa using h1.differentiableAt)
    rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h']
    simp

theorem form_conj (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) :
    a ⬝ᵥ (Hm.map (starRingEnd ℂ)).mulVec (star b) =
      starRingEnd ℂ (star a ⬝ᵥ Hm.mulVec (star (star b))) := by
  simp [dotProduct, Matrix.mulVec, map_sum, map_mul]

end Analysis

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem top_le_pc {s : 𝟙_ (Over (Sp ℂ)) ⟶ A} {U : A.left.Opens} :
    ⊤ ≤ (pc s).left ⁻¹ᵁ U ↔ ⊤ ≤ s.left ⁻¹ᵁ U := by
  rw [pc_left]
  exact top_le_inv _ (fun a => by simp)

theorem valAt'_pc (s : 𝟙_ (Over (Sp ℂ)) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U)) :
    valAt' (pc s).left U f = starRingEnd ℂ (valAt' s.left U f) := by
  rw [pc_left]
  exact valAt'_cc _ U f

def starZ (g : ℕ) : (Fin g → ℂ) →ₗ[ℤ] (Fin g → ℂ) :=
  (starAddEquiv : (Fin g → ℂ) ≃+ (Fin g → ℂ)).toAddMonoidHom.toIntLinearMap

theorem starZ_apply (z : Fin g → ℂ) : starZ g z = star z := rfl

theorem dom_eq (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (U : A.left.Opens) :
    {z | ⊤ ≤ (pc (ex (star z))).left ⁻¹ᵁ U} = star ⁻¹' {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U} :=
  Set.ext fun _ => top_le_pc

theorem conjugate_uniformisation_holomorphic (u : HolUnif A L g) (U : A.left.Opens) (f : Γ(A.left, U)) :
    IsOpen {z | ⊤ ≤ (pc (u.ex (star z))).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (pc (u.ex (star z))).left U f)
        {z | ⊤ ≤ (pc (u.ex (star z))).left ⁻¹ᵁ U} := by
  rw [dom_eq]
  exact ⟨(u.hol U f).1.preimage continuous_star,
    (differentiableOn_conj (u.hol U f).2).congr fun z _ => valAt'_pc _ U f⟩

theorem conjugate_frame_holomorphic (u : HolUnif A L g) (i : L.ι) :
    DifferentiableOn ℂ (fun z => starRingEnd ℂ (u.fr i (star z)))
      {z | ⊤ ≤ (pc (u.ex (star z))).left ⁻¹ᵁ L.U i} := by
  rw [dom_eq]
  exact differentiableOn_conj (u.fr_hol i)

def cjU (u : HolUnif A L g) : HolUnif (tw A) L g where
  ex z := pc (u.ex (star z))
  ex_add z w := by rw [star_add, u.ex_add, pc_mul]
  ex_onto r := by
    obtain ⟨s, rfl⟩ := pc_surjective r
    obtain ⟨w, rfl⟩ := u.ex_onto s
    exact ⟨star w, by
      show pc (u.ex (star (star w))) = _
      rw [star_star]⟩
  Λ := u.Λ.comap (starZ g)
  ker z := by
    rw [Submodule.mem_comap, starZ_apply, ← u.ker]
    exact ⟨fun h => pc_injective (h.trans pc_one.symm), fun h => by rw [h, pc_one]⟩
  discrete := by
    haveI := u.discrete
    exact DiscreteTopology.of_continuous_injective
      (f := fun l : u.Λ.comap (starZ g) => (⟨star l.1, l.2⟩ : u.Λ))
      (Continuous.subtype_mk (continuous_star.comp continuous_subtype_val) _)
      (fun a b h => Subtype.ext (star_injective (congrArg Subtype.val h)))
  full := by
    rw [eq_top_iff]
    intro w _
    have hw : star w ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) := by rw [u.full]; trivial
    have key : ∀ y ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)),
        star y ∈ Submodule.span ℝ ((u.Λ.comap (starZ g) : Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        refine Submodule.subset_span ?_
        show starZ g (star x) ∈ u.Λ
        rw [starZ_apply, star_star]
        exact hx
      | zero => simp
      | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx
    simpa using key _ hw
  hol := conjugate_uniformisation_holomorphic u
  fr i z := starRingEnd ℂ (u.fr i (star z))
  fr_hol := conjugate_frame_holomorphic u
  fr_ne i z h := (map_ne_zero _).2 (u.fr_ne i (star z) (top_le_pc.1 h))
  fr_compat i j z h := by
    have e := valAt'_pc (u.ex (star z)) (L.U i ⊓ L.U j) (L.g i j).val
    refine Eq.trans ?_ (congrArg (· * starRingEnd ℂ (u.fr j (star z))) e.symm)
    rw [← map_mul, ← u.fr_compat i j _ (top_le_pc.1 h)]

theorem isAH_cjU (u : HolUnif A L g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) :
    (cjU u).IsAH (Hm.map (starRingEnd ℂ)) (fun l => starRingEnd ℂ (χ ⟨star l.1, l.2⟩)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun z hz => ?_, fun l => ?_, fun l i z hz => ?_⟩
  · simp only [Matrix.map_apply, RCLike.star_def]
    rw [← h1.apply i j]
    simp
  · rw [form_conj, Complex.conj_re]
    exact h2 _ (by simpa using hz)
  · rw [RCLike.norm_conj]
    exact h3 _
  · have e := h4 ⟨star l.1, l.2⟩ i (star z) (top_le_pc.1 hz)
    show starRingEnd ℂ (u.fr i (star z)) = starRingEnd ℂ (χ ⟨star l.1, l.2⟩) * _ *
      starRingEnd ℂ (u.fr i (star (z + l.1)))
    rw [e, star_add, map_mul, map_mul, ← Complex.exp_conj, form_conj, form_conj]
    simp only [map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal, map_div₀, Complex.conj_ofNat,
      star_star]

def cjV (v : epsR ℂ ⟶ A) : epsR ℂ ⟶ tw A :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ v.left) (by
    have hv := Over.w v
    simp only [Over.mk_hom] at hv ⊢
    rw [Category.assoc, ← Category.assoc v.left, hv, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])))

theorem snd_val_cj (v : epsR ℂ ⟶ A) (U : A.left.Opens) (h0 : ⊤ ≤ v.left ⁻¹ᵁ U)
    (hU : ⊤ ≤ (spMap (dualMap (starRingEnd ℂ)) ≫ v.left) ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom
        (((spMap (dualMap (starRingEnd ℂ)) ≫ v.left).appLE U ⊤ hU).hom f)) =
      starRingEnd ℂ (TrivSqZeroExt.snd (show DualNumber ℂ from
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.left.appLE U ⊤ h0).hom f))) := by
  have e := val_spMap (dualMap (starRingEnd ℂ)) v.left U h0 hU f
  exact (congrArg TrivSqZeroExt.snd e).trans (by simp [dualMap])

theorem fderiv_cj (u : HolUnif A L g) (U : A.left.Opens) (f : Γ(A.left, U)) (a : Fin g → ℂ) :
    fderiv ℂ (fun z => valAt' (pc (u.ex (star z))).left U f) 0 (star a) =
      starRingEnd ℂ (fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 a) := by
  have hF : (fun z => valAt' (pc (u.ex (star z))).left U f) =
      fun z => starRingEnd ℂ (valAt' (u.ex (star z)).left U f) := funext fun z => valAt'_pc _ U f
  have e := fderiv_conj (fun z => valAt' (u.ex z).left U f) 0 (star a)
  rw [star_zero, star_star] at e
  rw [hF]
  exact e

theorem isDiff_cj (u : HolUnif A L g) {a : Fin g → ℂ} {v : epsR ℂ ⟶ A} (h : u.IsDiff a v) :
    (cjU u).IsDiff (star a) (cjV v) := by
  intro U hU f
  have hi : ∀ b : DualNumber ℂ, dualMap (starRingEnd ℂ) (dualMap (starRingEnd ℂ) b) = b := fun b => by
    ext <;> simp [dualMap]
  have h0 : ⊤ ≤ v.left ⁻¹ᵁ U := (top_le_inv _ hi).1 hU
  exact (snd_val_cj v U h0 hU f).trans ((congrArg _ (h U h0 f)).trans (fderiv_cj u U f a).symm)

end Unif

theorem isTan_conj {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X} {v : epsAt z ⟶ G}
    {v' : epsAt (cc ≫ z) ⟶ G} (e : v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left) (h : IsTanAt G z v) :
    IsTanAt G (cc ≫ z) v' := by
  unfold IsTanAt at *
  have e1 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫
      spMap (dualMap (starRingEnd ℂ)) =
      cc ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by simp [dualMap]))
  let k : Over.mk (cc ≫ z) ⟶ Over.mk z := Over.homMk cc rfl
  have e2 : (1 : Over.mk (cc ≫ z) ⟶ G).left = cc ≫ (1 : Over.mk z ⟶ G).left := by
    rw [← comp_one k]
    rfl
  rw [e, ← Category.assoc, e1, Category.assoc, h, e2]

theorem hodgeInnerProduct_conj {X : Scheme.{0}} {G : Over X} [GrpObj G] {L : LB G.left} {z : Sp ℂ ⟶ X}
    {v w : epsAt z ⟶ G} {v' w' : epsAt (cc ≫ z) ⟶ G} {c : ℂ}
    (hv : v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left)
    (hw : w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (h : HodgeIP G L z v w c) :
    HodgeIP G L (cc ≫ z) v' w' (starRingEnd ℂ c) := by
  obtain ⟨hL, tv, tw', A, _, φ, g, u, Hm, χ, a', b', a, b, h1, h2, h3, h4, h5, h6, rfl⟩ := h
  refine ⟨hL, isTan_conj hv tv, isTan_conj hw tw', tw A, inferInstance, φ, g, cjU u, Hm.map (starRingEnd ℂ), _,
    cjV a', cjV b', star a, star b, isGrpPullback_tw h1, isAH_cjU u h2, ?_, ?_, isDiff_cj u h5, isDiff_cj u h6, ?_⟩
  · rw [hv, ← h3]
    show (spMap (dualMap (starRingEnd ℂ)) ≫ a'.left) ≫ φ = _
    rw [Category.assoc]
  · rw [hw, ← h4]
    show (spMap (dualMap (starRingEnd ℂ)) ≫ b'.left) ≫ φ = _
    rw [Category.assoc]
  · rw [form_conj]
    simp

theorem hodgeInnerProduct_conj_abelianScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ t.G) (v' w' : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ t.G) (c : ℂ), v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left → w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left → HodgeIP t.G t.PP.L z v w c → HodgeIP t.G t.PP.L (spMap (starRingEnd ℂ) ≫ z) v' w' (starRingEnd ℂ c) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hv hw h => hodgeInnerProduct_conj hv hw h

end GlobalTheory.CompanionTheory.Ar.HodgeConj
