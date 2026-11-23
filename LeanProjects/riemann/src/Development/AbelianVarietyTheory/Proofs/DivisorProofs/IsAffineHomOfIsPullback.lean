import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Obs.BaseChg

section Nat
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F F' : C ⥤ CommAlgCat.{0} R}

def ofNat (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (sm : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) : CoefMap (RingHom.id R) F F' where
  G := 𝟭 C
  α := α
  naturality := nat
  smul := sm

theorem ofNat_pull2_bijective (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (sm : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) (hb : ∀ T, Function.Bijective (α T)) :
    Function.Bijective (ofNat α nat sm).pull2 := by
  let e : ∀ T, F.obj T ≃+* F'.obj T := fun T ↦ RingEquiv.ofBijective (α T) (hb T)
  let β : ∀ T, F'.obj T →+* F.obj T := fun T ↦ (e T).symm.toRingHom
  have hβα : ∀ T b, β T (α T b) = b := fun T b ↦ (e T).symm_apply_apply b
  have hαβ : ∀ T b, α T (β T b) = b := fun T b ↦ (e T).apply_symm_apply b
  have natβ : ∀ {T T' : C} (a : T ⟶ T') (b : F'.obj T), β T' (mp F' a b) = mp F a (β T b) := fun a b ↦ by
    apply (hb _).1; rw [hαβ, nat, hαβ]
  have smβ : ∀ T (r : R) (b : F'.obj T), β T (r • b) = r • β T b := fun T r b ↦ by
    apply (hb T).1; rw [hαβ, sm, hαβ]
  have h1 : ∀ c, (ofNat β natβ smβ).pull2 ((ofNat α nat sm).pull2 c) = c := fun c ↦ by
    rw [← CoefMap.pullCohomologyTwo_comp]
    conv_rhs => rw [← CoefMap.pullCohomologyTwo_id c]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun T ↦ 𝟙 T, naturality := fun _ _ f ↦ by dsimp [ofNat, CoefMap.comp, CoefMap.id]; simp } (fun T b ↦ by
      exact (mp_id F T b).trans (hβα T b).symm) c
  have h2 : ∀ c, (ofNat α nat sm).pull2 ((ofNat β natβ smβ).pull2 c) = c := fun c ↦ by
    rw [← CoefMap.pullCohomologyTwo_comp]
    conv_rhs => rw [← CoefMap.pullCohomologyTwo_id c]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun T ↦ 𝟙 T, naturality := fun _ _ f ↦ by dsimp [ofNat, CoefMap.comp, CoefMap.id]; simp } (fun T b ↦ by
      exact (mp_id F' T b).trans (hαβ T b).symm) c
  exact ⟨fun x y hxy ↦ by rw [← h1 x, hxy, h1], fun y ↦ ⟨_, h2 y⟩⟩

end Nat

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}

theorem isAffineHom_of_isPullback (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : IsAffineHom pr :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance

abbrev pre (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) : X₁.affineOpens :=
  haveI := isAffineHom_of_isPullback hp
  ⟨pr ⁻¹ᵁ U.1, U.2.preimage pr⟩

def preF (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : AffOp X₀ ⥤ AffOp X₁ :=
  (Monotone.functor (f := pre hp) fun _ _ h ↦ (show pr ⁻¹ᵁ _ ≤ pr ⁻¹ᵁ _ from
    fun _ hx ↦ (Subtype.coe_le_coe.2 h) hx)).op

abbrev pairOf (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) : Pair pr :=
  ⟨(pre hp U, U), le_rfl⟩

def secP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) :
    Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  GlobalTheory.CechDR.secPull s₀ s₁ (pairOf hp U)

theorem pullbackSection_smul₂ (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₀)
    (b : Sec s₀ U.1) : secP hp U (r • b) = algebraMap R₀ R₁ r • secP hp U b :=
  semiHom_secPull hp.w (pairOf hp U) r b

def beta (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) :
    R₁ ⊗[R₀] Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  letI : Algebra R₀ (Sec s₁ (pr ⁻¹ᵁ U.1)) := ((algebraMap R₁ _).comp (algebraMap R₀ R₁)).toAlgebra
  haveI : IsScalarTower R₀ R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId R₁ _)
    { toRingHom := secP hp U
      commutes' := fun r ↦ by
        have := pullbackSection_smul₂ hp U r 1
        rw [map_one] at this
        change secP hp U (algebraMap R₀ _ r) = _
        rw [Algebra.algebraMap_eq_smul_one r, this, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
          Algebra.algebraMap_eq_smul_one r]
        exact (Algebra.algebraMap_eq_smul_one _).symm }
    (fun _ _ ↦ Commute.all _ _)).toRingHom

theorem beta_tmul (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₁)
    (b : Sec s₀ U.1) : beta hp U (r ⊗ₜ b) = algebraMap R₁ _ r * secP hp U b := by
  simp [beta]

theorem beta_smul (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₁)
    (x : R₁ ⊗[R₀] Sec s₀ U.1) : beta hp U (r • x) = r • beta hp U x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, beta_tmul, beta_tmul, map_mul, _root_.mul_assoc, Algebra.smul_def]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem beta_nat (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) {U V : AffOp X₀} (a : U ⟶ V)
    (x : (ext R₁ (OAff s₀)).obj U) :
    beta hp V.unop (mp (ext R₁ (OAff s₀)) a x) = mp (preF hp ⋙ OAff s₁) a (beta hp U.unop x) := by
  revert x
  change ∀ x : R₁ ⊗[R₀] Sec s₀ U.unop.1, _
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact (map_zero _).symm
  | tmul r b =>
    have hn := (pairPull hp.w).naturality
      (homOfLE (show pairOf hp V.unop ≤ pairOf hp U.unop from
        Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨fun _ hx ↦ (Subtype.coe_le_coe.2 (leOfHom a.unop) : V.unop.1 ≤ U.unop.1) hx,
          leOfHom a.unop⟩))).op b
    change beta hp V.unop (r ⊗ₜ mp (OAff s₀) a b) = mp (preF hp ⋙ OAff s₁) a (beta hp U.unop (r ⊗ₜ b))
    rw [beta_tmul, beta_tmul]
    erw [map_mul]
    congr 1
    all_goals first | exact ((Sec.res s₁ _).commutes r).symm | exact hn
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (map_add _ _ _).symm

def fwd (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) :
    CoefMap (RingHom.id R₁) (ext R₁ (OAff s₀)) (preF hp ⋙ OAff s₁) :=
  ofNat (fun U ↦ beta hp U.unop) (fun a x ↦ beta_nat hp a x) (fun U r x ↦ beta_smul hp U.unop r x)

section PairMaps
variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}

theorem comp_base_eq (hf : f₁ ≫ pr = pr' ≫ f₀) (y : Y₁) : pr.base (f₁.base y) = f₀.base (pr'.base y) := by
  have := congrArg (fun g : Y₁ ⟶ X₀ ↦ g.base y) hf
  simpa using this

abbrev preP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) (p : Pair f₀) : Pair f₁ :=
  ⟨(pre hp' p.1.1, pre hp p.1.2), fun y hy ↦ by
    show pr.base (f₁.base y) ∈ p.1.2.1
    rw [comp_base_eq hf]; exact p.2 hy⟩

def preFP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    (Pair f₀)ᵒᵖ ⥤ (Pair f₁)ᵒᵖ :=
  (Monotone.functor (f := preP hp hp' hf) fun _ _ h ↦ Subtype.coe_le_coe.1 (Prod.le_def.2
    ⟨show pr' ⁻¹ᵁ _ ≤ pr' ⁻¹ᵁ _ from fun _ hx ↦ (Subtype.coe_le_coe.2 (Pair.le_fst h)) hx,
     show pr ⁻¹ᵁ _ ≤ pr ⁻¹ᵁ _ from fun _ hx ↦ (Subtype.coe_le_coe.2 (Pair.le_snd h)) hx⟩)).op

def zMap (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) :
    CoefMap (RingHom.id R₁) (preF hp ⋙ OAff s₁) (preFP hp hp' hf ⋙ OPair f₁ t₁) where
  G := pairSnd f₀
  α p := (pairPull h₁).α ((preFP hp hp' hf).obj p)
  naturality a b := (pairPull h₁).naturality ((preFP hp hp' hf).map a) b
  smul p r b := (pairPull h₁).smul ((preFP hp hp' hf).obj p) r b

def zRes (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    CoefMap (RingHom.id R₁) (preF hp' ⋙ OAff t₁) (preFP hp hp' hf ⋙ OPair f₁ t₁) where
  G := pairFst f₀
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def kMap (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    CoefMap (RingHom.id R₁) (ext R₁ (OPair f₀ t₀)) (preFP hp hp' hf ⋙ OPair f₁ t₁) :=
  ofNat (fun p ↦ beta hp' p.unop.1.1) (fun a x ↦ beta_nat hp' ((pairFst f₀).map a) x)
    (fun p r x ↦ beta_smul hp' _ r x)

end PairMaps

section Pointwise
variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}

theorem preF_cover (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hW : ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W) (x : X₁) (U : X₁.Opens) (hx : x ∈ U) :
    ∃ t : AffOp X₀, x ∈ ((preF hp).obj t).unop.1 ∧ ((preF hp).obj t).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := pr.base x) (U := W₀) hx
  exact ⟨Opposite.op ⟨V, hV⟩, hxV, fun y hy ↦ hVW hy⟩

theorem preF_dir (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hW : ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W) (t₁ t₂ : AffOp X₀) (x : X₁) (U : X₁.Opens)
    (hx : x ∈ U) (h₁ : x ∈ ((preF hp).obj t₁).unop.1) (h₂ : x ∈ ((preF hp).obj t₂).unop.1) :
    ∃ t₃ : AffOp X₀, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((preF hp).obj t₃).unop.1 ∧
      ((preF hp).obj t₃).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := pr.base x)
    (U := W₀ ⊓ t₁.unop.1 ⊓ t₂.unop.1) ⟨⟨hx, h₁⟩, h₂⟩
  exact ⟨Opposite.op ⟨V, hV⟩,
    ⟨(homOfLE (show (⟨V, hV⟩ : X₀.affineOpens) ≤ t₁.unop from fun y hy ↦ (hVW hy).1.2)).op⟩,
    ⟨(homOfLE (show (⟨V, hV⟩ : X₀.affineOpens) ≤ t₂.unop from fun y hy ↦ (hVW hy).2)).op⟩,
    hxV, fun y hy ↦ (hVW hy).1.1⟩

theorem preFP_cover (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (hW : ∀ W : Y₁.Opens, ∃ W₀ : Y₀.Opens, pr' ⁻¹ᵁ W₀ = W) (x : Y₁) (U : Y₁.Opens) (hx : x ∈ U) :
    ∃ t : (Pair f₀)ᵒᵖ, x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj t).unop.1 ∧
      ((preFP hp hp' hf ⋙ pairFst f₁).obj t).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f₀.base (pr'.base x))
    (U := (⊤ : X₀.Opens)) trivial
  obtain ⟨V', hV', hxV', hV'W⟩ := exists_isAffineOpen_mem_and_subset (x := pr'.base x)
    (U := W₀ ⊓ f₀ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨V', hV'⟩, ⟨V, hV⟩), fun z hz ↦ (hV'W hz).2⟩, hxV', fun z hz ↦ (hV'W hz).1⟩

theorem preFP_directed (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (hW : ∀ W : Y₁.Opens, ∃ W₀ : Y₀.Opens, pr' ⁻¹ᵁ W₀ = W) (a₁ a₂ : (Pair f₀)ᵒᵖ) (x : Y₁) (U : Y₁.Opens)
    (hx : x ∈ U) (h₁ : x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₁).unop.1)
    (h₂ : x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₂).unop.1) :
    ∃ a₃ : (Pair f₀)ᵒᵖ, Nonempty (a₁ ⟶ a₃) ∧ Nonempty (a₂ ⟶ a₃) ∧
      x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₃).unop.1 ∧ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₃).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  have g₁ : f₀.base (pr'.base x) ∈ a₁.unop.1.2.1 := a₁.unop.2 h₁
  have g₂ : f₀.base (pr'.base x) ∈ a₂.unop.1.2.1 := a₂.unop.2 h₂
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := f₀.base (pr'.base x))
    (U := a₁.unop.1.2.1 ⊓ a₂.unop.1.2.1) ⟨g₁, g₂⟩
  obtain ⟨V', hV', hxV', hV'W⟩ := exists_isAffineOpen_mem_and_subset (x := pr'.base x)
    (U := W₀ ⊓ a₁.unop.1.1.1 ⊓ a₂.unop.1.1.1 ⊓ f₀ ⁻¹ᵁ V) ⟨⟨⟨hx, h₁⟩, h₂⟩, hxV⟩
  let a₃ : Pair f₀ := ⟨(⟨V', hV'⟩, ⟨V, hV⟩), fun z hz ↦ (hV'W hz).2⟩
  refine ⟨Opposite.op a₃, ⟨(homOfLE (show a₃ ≤ a₁.unop from Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨fun z hz ↦ (hV'W hz).1.1.2, fun z hz ↦ (hVW hz).1⟩))).op⟩,
    ⟨(homOfLE (show a₃ ≤ a₂.unop from Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨fun z hz ↦ (hV'W hz).1.2, fun z hz ↦ (hVW hz).2⟩))).op⟩, hxV', fun z hz ↦ (hV'W hz).1.1.1⟩

end Pointwise

end GlobalTheory.Obs.BaseChg
