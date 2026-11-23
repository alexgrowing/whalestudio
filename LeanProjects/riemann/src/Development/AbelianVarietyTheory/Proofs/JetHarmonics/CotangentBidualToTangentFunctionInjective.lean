import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.HodgeTateCharacterSystems
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueIsAl
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv

namespace GlobalTheory.HodgeTateCompare

open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage

noncomputable section

section Tangent

variable {O : Type} [CommRing O] [IsLocalRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G]

def locIncl : specO O (LocRing G) ⟶ G :=
  Over.homMk (fromLoc G) (spec_strMap G).symm

variable {G}

theorem ptMap_locIncl_injective {R : Type} [CommRing R] [Algebra O R]
    {φ ψ : LocRing G →ₐ[O] R} (h : ptMap φ ≫ locIncl G = ptMap ψ ≫ locIncl G) : φ = ψ := by
  have h1 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ G.left.fromSpecStalk (origin G) =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ G.left.fromSpecStalk (origin G) :=
    congrArg Over.Hom.left h
  have h2 := Spec.map_injective ((cancel_mono (G.left.fromSpecStalk (origin G))).1 h1)
  exact AlgHom.ext fun a => congrArg (fun q => q.hom a) h2

theorem ptMap_aug_locIncl : ptMap (aug G) ≫ locIncl G = 1 := by
  ext1
  change Spec.map (augMap G) ≫ fromLoc G = (toUnit (specO O O)).left ≫ unitSec G
  rw [spec_augMap]
  have h : (toUnit (specO O O)).left = 𝟙 (Spec (CommRingCat.of O)) := by
    have h1 := Over.w (toUnit (specO O O))
    exact ((Category.comp_id _).symm.trans h1).trans (Spec.map_id _)
  rw [h]
  exact (Category.id_comp _).symm

theorem tangentPt_eq {R : Type} [CommRing R] [Algebra O R] (v : Cotangent G →ₗ[O] R) :
    (tangentPt v : specO O (DualNumber R) ⟶ G) = ptMap (tangentAlg v) ≫ locIncl G := rfl

theorem tangentAlg_fst {R : Type} [CommRing R] [Algebra O R] (v : Cotangent G →ₗ[O] R)
    (a : LocRing G) : (tangentAlg v a).fst = algebraMap O R (aug G a) := by
  simp [tangentAlg]

theorem tangentAlg_snd {R : Type} [CommRing R] [Algebra O R] (v : Cotangent G →ₗ[O] R)
    (a : LocRing G) : (tangentAlg v a).snd = v (dAt G a) := by
  simp [tangentAlg]

theorem fst_tangentPt {R : Type} [CommRing R] [Algebra O R] (v : Cotangent G →ₗ[O] R) :
    ptMap (TrivSqZeroExt.fstHom O R R) ≫ (tangentPt v : specO O (DualNumber R) ⟶ G) = 1 := by
  have h : (TrivSqZeroExt.fstHom O R R).comp (tangentAlg v) = (Algebra.ofId O R).comp (aug G) :=
    AlgHom.ext fun a => tangentAlg_fst v a
  rw [tangentPt_eq, ← Category.assoc, ptMap_comp_ptMap, h, ← ptMap_comp_ptMap, Category.assoc,
    ptMap_aug_locIncl, comp_one]

def toLieG (v : Lie G) : LieG G := ⟨tangentPt v, fst_tangentPt v⟩

theorem toLieG_injective : Function.Injective (toLieG (G := G)) := by
  intro v w h
  have h1 : tangentAlg v = tangentAlg w := ptMap_locIncl_injective (congrArg Subtype.val h)
  refine AugCot.hom_ext (ε := aug G) fun a => ?_
  exact (tangentAlg_snd v a).symm.trans
    ((congrArg (fun φ => (φ a).snd) h1).trans (tangentAlg_snd w a))

theorem isLocalRing_dualNumber : IsLocalRing (DualNumber O) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _

theorem exists_factor {T : Type} [CommRing T] [IsLocalRing T] [Algebra O T] (w : specO O T ⟶ G)
    (hw : w.left (closedPoint T) = origin G) :
    ∃ φ : LocRing G →ₐ[O] T, ptMap φ ≫ locIncl G = w := by
  have h0 : ∃ φ : G.left.presheaf.stalk (origin G) ⟶ .of T,
      Spec.map φ ≫ G.left.fromSpecStalk (origin G) = w.left := by
    rw [← hw]
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of T) w.left⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : CommRingCat.of (LocRing G) ⟶ .of T,
      Spec.map φ ≫ fromLoc G = w.left := h0
  have h : strMap G ≫ φ = CommRingCat.ofHom (algebraMap O T) := by
    apply Spec.map_injective
    have h2 := Over.w w
    rw [← hφ] at h2
    rw [Spec.map_comp]
    exact (congrArg (Spec.map φ ≫ ·) (spec_strMap G)).trans ((Category.assoc _ _ _).symm.trans h2)
  refine ⟨{ φ.hom with commutes' := fun a => congrArg (fun q => q.hom a) h }, ?_⟩
  ext1
  exact hφ

theorem toLieG_surjective : Function.Surjective (toLieG (G := G)) := by
  intro x
  haveI := isLocalRing_dualNumber (O := O)
  have hx : ptMap (TrivSqZeroExt.fstHom O O O) ≫ x.1 = ptMap (aug G) ≫ locIncl G :=
    x.2.trans ptMap_aug_locIncl.symm
  have hloc : IsLocalHom (TrivSqZeroExt.fstHom O O O).toRingHom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  have hpt : x.1.left (closedPoint (DualNumber O)) = origin G := by
    have h1 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O O).toRingHom) ≫ x.1.left =
        unitSec G := (congrArg Over.Hom.left hx).trans (spec_augMap G)
    have h2 := congrArg (fun q : Spec (CommRingCat.of O) ⟶ G.left => q (closedPoint O)) h1
    refine Eq.trans ?_ ((Scheme.Hom.comp_apply _ _ _).symm.trans h2)
    congr 1
    exact (comap_closedPoint (TrivSqZeroExt.fstHom O O O).toRingHom).symm
  obtain ⟨φ, hφ⟩ := exists_factor x.1 hpt
  have h2 : (TrivSqZeroExt.fstHom O O O).comp φ = aug G := by
    apply ptMap_locIncl_injective
    rw [← ptMap_comp_ptMap, Category.assoc, hφ, hx]
  have h3 : ∀ a, (φ a).fst = aug G a := fun a => AlgHom.congr_fun h2 a
  obtain ⟨v, hv⟩ : ∃ v : Lie G, ∀ a, v (dAt G a) = (φ a).snd :=
    ⟨AugCot.ofSqZero (aug G) φ h3, AugCot.ofSqZero_d (aug G) φ h3⟩
  refine ⟨v, Subtype.ext ?_⟩
  change tangentPt v = x.1
  rw [← hφ, tangentPt_eq]
  congr 2
  refine AlgHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · rw [tangentAlg_fst, h3]; rfl
  · rw [tangentAlg_snd, hv]

variable (G) in

def lieEquiv : Lie G ≃ LieG G :=
  Equiv.ofBijective toLieG ⟨toLieG_injective, toLieG_surjective⟩

theorem lieEquiv_val (v : Lie G) : (lieEquiv G v).1 = tangentPt v := rfl

theorem scale_tangentPt {R : Type} [CommRing R] [Algebra O R] (v : Cotangent G →ₗ[O] R) (a : R) :
    scale O a ≫ (tangentPt v : specO O (DualNumber R) ⟶ G) = tangentPt (a • v) := by
  rw [tangentPt_eq, tangentPt_eq, ← Category.assoc, scale, ptMap_comp_ptMap]
  congr 2
  refine AlgHom.ext fun b => TrivSqZeroExt.ext ?_ ?_
  · simp [tangentAlg_fst]
  · simp [tangentAlg_snd]

theorem lieEquiv_smul (a : O) (v : Lie G) :
    (lieEquiv G (a • v)).1 = ptMap (dualScale a) ≫ (lieEquiv G v).1 :=
  (scale_tangentPt v a).symm

theorem lieEquiv_add (v w : Lie G) :
    (lieEquiv G (v + w)).1 = (lieEquiv G v).1 * (lieEquiv G w).1 := by
  let i₁ := LinearMap.inl O O O
  let i₂ := LinearMap.inr O O O
  let x : specO O (DualNumber O) ⟶ G := tangentPt v
  let y : specO O (DualNumber O) ⟶ G := tangentPt w
  have hx : ptMap (TrivSqZeroExt.fstHom O O O) ≫ x = 1 := fst_tangentPt v
  have hy : ptMap (TrivSqZeroExt.fstHom O O O) ≫ y = 1 := fst_tangentPt w
  let u : Cotangent G →ₗ[O] O × O := LinearMap.prod v w
  obtain ⟨α, hα₁, hα₂⟩ : ∃ α : LocRing G →ₐ[O] TrivSqZeroExt O (O × O),
      (∀ a, (α a).fst = aug G a) ∧ ∀ a, (α a).snd = u (dAt G a) :=
    ⟨AugCot.toSqZero (aug G) u, AugCot.fst_toSqZero (aug G) u, AugCot.snd_toSqZero (aug G) u⟩
  let z : specO O (TrivSqZeroExt O (O × O)) ⟶ G := ptMap α ≫ locIncl G
  have hz : ∀ l : O × O →ₗ[O] O, ofTwo O l ≫ z = tangentPt (G := G) (l ∘ₗ u) := by
    intro l
    rw [tangentPt_eq, ← Category.assoc, ofTwo, ptMap_comp_ptMap]
    congr 2
    refine AlgHom.ext fun b => TrivSqZeroExt.ext ?_ ?_
    · simp [tangentAlg_fst, hα₁]
    · simp [tangentAlg_snd, hα₂]
  have key : z = (toTwo O i₁ ≫ x) * (toTwo O i₂ ≫ y) := by
    ext1
    refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst O O O)).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd O O O)).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst O O O)).toRingHom
        (fun x => ⟨1, one_pos, TrivSqZeroExt.map i₁ x, by ext <;> simp [i₁]⟩)
        fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : ofTwo O (LinearMap.fst O O O) ≫ _ = ofTwo O (LinearMap.fst O O O) ≫ _)
      rw [comp_mul, hz]
      simp only [← Category.assoc, ofTwo_toTwo]
      have e₂ : LinearMap.fst O O O (i₁ 1) = 1 := rfl
      have e₃ : LinearMap.fst O O O (i₂ 1) = 0 := rfl
      rw [e₂, e₃, scale_zero_comp hy, _root_.mul_one, scale_one, Category.id_comp]
      rfl
    · refine congrArg Over.Hom.left
        (?_ : ofTwo O (LinearMap.snd O O O) ≫ _ = ofTwo O (LinearMap.snd O O O) ≫ _)
      rw [comp_mul, hz]
      simp only [← Category.assoc, ofTwo_toTwo]
      have e₂ : LinearMap.snd O O O (i₁ 1) = 0 := rfl
      have e₃ : LinearMap.snd O O O (i₂ 1) = 1 := rfl
      rw [e₂, e₃, scale_zero_comp hx, _root_.one_mul, scale_one, Category.id_comp]
      rfl
  let l := LinearMap.fst O O O + LinearMap.snd O O O
  have := congrArg (ofTwo O l ≫ ·) key
  simp only [comp_mul, ← Category.assoc, ofTwo_toTwo, hz] at this
  have e₂ : l (i₁ 1) = 1 := by simp [l, i₁]
  have e₃ : l (i₂ 1) = 1 := by simp [l, i₂]
  rw [e₂, e₃, scale_one, Category.id_comp, Category.id_comp] at this
  exact this

end Tangent

section Cotangent

variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]

theorem mem_omega_iff (g : LieG G → O) :
    g ∈ omega G ↔ ∃ F : Module.Dual O (Lie G), ∀ v, g (lieEquiv G v) = F v := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨⟨fun v => g (lieEquiv G v), fun v w => ?_⟩, fun a v => ?_⟩, fun _ => rfl⟩
    · have h := (lieEquiv G (v + w)).2
      rw [lieEquiv_add] at h
      rw [← h₁ _ _ h]
      exact congrArg g (Subtype.ext (lieEquiv_add v w))
    · have h := (lieEquiv G (a • v)).2
      rw [lieEquiv_smul] at h
      exact (congrArg g (Subtype.ext (lieEquiv_smul a v))).trans (h₂ a _ h)
  · rintro ⟨F, hF⟩
    refine ⟨fun x y h => ?_, fun a x h => ?_⟩
    · obtain ⟨v, rfl⟩ := (lieEquiv G).surjective x
      obtain ⟨w, rfl⟩ := (lieEquiv G).surjective y
      rw [hF, hF, ← map_add, ← hF]
      exact congrArg g (Subtype.ext (lieEquiv_add v w).symm)
    · obtain ⟨v, rfl⟩ := (lieEquiv G).surjective x
      rw [hF, ← smul_eq_mul, ← map_smul, ← hF]
      exact congrArg g (Subtype.ext (lieEquiv_smul a v).symm)

variable (G) in

def cotangentBidualToTangentFunction : Module.Dual O (Lie G) →ₗ[O] (LieG G → O) where
  toFun F x := F ((lieEquiv G).symm x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cotangentBidualToTangentFunction_apply (F : Module.Dual O (Lie G)) (v : Lie G) :
    cotangentBidualToTangentFunction G F (lieEquiv G v) = F v :=
  congrArg F ((lieEquiv G).symm_apply_apply v)

theorem cotangentBidualToTangentFunction_injective : Function.Injective (cotangentBidualToTangentFunction G) := fun F F' h =>
  LinearMap.ext fun v => by rw [← cotangentBidualToTangentFunction_apply, h, cotangentBidualToTangentFunction_apply]

theorem range_cotangentBidualToTangentFunction : LinearMap.range (cotangentBidualToTangentFunction G) = omega G := by
  ext g
  rw [mem_omega_iff]
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F, cotangentBidualToTangentFunction_apply F⟩
  · rintro ⟨F, hF⟩
    refine ⟨F, funext fun x => ?_⟩
    obtain ⟨v, rfl⟩ := (lieEquiv G).surjective x
    rw [cotangentBidualToTangentFunction_apply, hF]

variable (G) in

def bidualEquivOmega : Module.Dual O (Lie G) ≃ₗ[O] omega G :=
  (LinearEquiv.ofInjective _ cotangentBidualToTangentFunction_injective).trans (LinearEquiv.ofEq _ _ range_cotangentBidualToTangentFunction)

variable (G) in

def ev : Cotangent G →ₗ[O] (LieG G → O) := cotangentBidualToTangentFunction G ∘ₗ Module.Dual.eval O (Cotangent G)

theorem ev_apply (f : Cotangent G) (v : Lie G) : ev G f (lieEquiv G v) = v f :=
  cotangentBidualToTangentFunction_apply (Module.Dual.eval O (Cotangent G) f) v

theorem ev_mem (f : Cotangent G) : ev G f ∈ omega G :=
  range_cotangentBidualToTangentFunction.le ⟨Module.Dual.eval O (Cotangent G) f, rfl⟩

theorem ev_injective [Module.IsReflexive O (Cotangent G)] : Function.Injective (ev G) :=
  cotangentBidualToTangentFunction_injective.comp (Module.bijective_dual_eval O (Cotangent G)).1

theorem range_ev [Module.IsReflexive O (Cotangent G)] : LinearMap.range (ev G) = omega G := by
  rw [ev, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.2 (Module.bijective_dual_eval O (Cotangent G)).2), range_cotangentBidualToTangentFunction]

variable (G) in

def omegaEquiv [Module.IsReflexive O (Cotangent G)] : Cotangent G ≃ₗ[O] omega G :=
  (LinearEquiv.ofInjective _ ev_injective).trans (LinearEquiv.ofEq _ _ range_ev)

theorem strMap_eq : strMap G =
    StructureSheaf.toStalk O (G.hom (origin G)) ≫ G.hom.stalkMap (origin G) := by
  apply Spec.map_injective
  have e : (Spec (CommRingCat.of O)).fromSpecStalk (G.hom (origin G)) =
      Spec.map (StructureSheaf.toStalk O (G.hom (origin G))) := Spec.fromSpecStalk_eq' _ _
  refine (spec_strMap G).trans ?_
  refine (Scheme.SpecMap_stalkMap_fromSpecStalk G.hom (x := origin G)).symm.trans ?_
  rw [e]
  exact (Spec.map_comp _ _).symm

theorem finite_projective_of_smooth [Smooth G.hom] :
    Module.Finite O (Cotangent G) ∧ Module.Projective O (Cotangent G) := by
  let q : PrimeSpectrum O := G.hom (origin G)
  letI : Algebra O ((Spec (CommRingCat.of O)).presheaf.stalk q) := StructureSheaf.stalkAlgebra O q
  have := q.isPrime
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of O)).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk O q
  have h₁ : (strMap G).hom.FormallySmooth := by
    have hs : (G.hom.stalkMap (origin G)).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp (G.hom.smoothLocus_eq_top.ge (Set.mem_univ _))
    have h₀ : Algebra.FormallySmooth O ((Spec (CommRingCat.of O)).presheaf.stalk q) :=
      Algebra.FormallySmooth.of_isLocalization q.asIdeal.primeCompl
    rw [strMap_eq]
    exact RingHom.FormallySmooth.comp (RingHom.formallySmooth_algebraMap.2 h₀) hs
  have h₂ : (strMap G).hom.EssFiniteType := by
    have hs : (G.hom.stalkMap (origin G)).hom.EssFiniteType :=
      LocallyOfFiniteType.stalkMap G.hom _
    have h₀ : Algebra.EssFiniteType O ((Spec (CommRingCat.of O)).presheaf.stalk q) :=
      Algebra.EssFiniteType.of_isLocalization _ q.asIdeal.primeCompl
    rw [strMap_eq]
    exact RingHom.EssFiniteType.comp (RingHom.essFiniteType_algebraMap.2 h₀) hs
  haveI : Algebra.FormallySmooth O (LocRing G) := h₁
  haveI : Algebra.EssFiniteType O (LocRing G) := h₂
  exact ⟨AugCot.finite (aug G), AugCot.projective (aug G)⟩

end Cotangent

section Characters

variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]

theorem torsion_ext {N : ℕ} {T : Over (Spec (CommRingCat.of O))} {x y : T ⟶ torsion G N}
    (h : x ≫ torsion.ι G N = y ≫ torsion.ι G N) : x = y :=
  pullback.hom_ext h (toUnit_unique _ _)

theorem comp_ι_pow {N : ℕ} {T : Over (Spec (CommRingCat.of O))} (x : T ⟶ torsion G N) :
    (x ≫ torsion.ι G N) ^ N = 1 := by
  rw [← comp_pow, torsion_ι_pow, comp_one]

theorem torsionLift_comp_ι {N : ℕ} {T : Over (Spec (CommRingCat.of O))} (x : T ⟶ torsion G N)
    (h : (x ≫ torsion.ι G N) ^ N = 1) : torsionLift (x ≫ torsion.ι G N) h = x :=
  torsion_ext (torsionLift_ι _ _)

variable [IsCommMonObj G]

theorem isCharTors_iff {N : ℕ} (f : torsion G N ⟶ Gm (Spec (CommRingCat.of O))) :
    IsCharTors G N f ↔ ∃ χ : TorsionChar G N, χ.hom = f := by
  constructor
  · intro h
    exact ⟨⟨f, fun T x y hx hy => h T _ _ _ (by simp only [torsionLift_ι])⟩, rfl⟩
  · rintro ⟨χ, rfl⟩ T x y z hz
    have h := χ.map_mul T _ _ (comp_ι_pow x) (comp_ι_pow y)
    rw [torsionLift_comp_ι, torsionLift_comp_ι] at h
    rw [← h]
    congr 1
    exact torsion_ext (hz.trans (torsionLift_ι _ _).symm)

variable (G) in

def tvEquiv (p : ℕ) : Tv G p ≃ CharSystem G p where
  toFun χ :=
    { char := fun n => ⟨χ.χ n, fun T x y hx hy => χ.isChar n T _ _ _ (by simp only [torsionLift_ι])⟩
      compat := fun n => ((Category.id_comp _).symm.trans (χ.compat n _ (𝟙 _) (torsionIncl G p n)
        (by rw [Category.id_comp, torsionIncl, torsionLift_ι]))).symm }
  invFun t :=
    { χ := fun n => (t.char n).hom
      isChar := fun n => (isCharTors_iff _).2 ⟨_, rfl⟩
      compat := fun n T x y h => by
        have e : x ≫ torsionIncl G p n = y :=
          torsion_ext (by rw [Category.assoc, torsionIncl, torsionLift_ι, h])
        rw [← t.compat n, ← Category.assoc, e] }
  left_inv _ := rfl
  right_inv _ := rfl

end Characters

section HodgeTate

variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]

theorem dualBC_tangentPt {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (v : Cotangent G →ₗ[O] R) :
    ptMap (dualBC φ) ≫ (tangentPt v : specO O (DualNumber R) ⟶ G) =
      tangentPt (φ.toLinearMap ∘ₗ v) := by
  rw [tangentPt_eq, tangentPt_eq, ← Category.assoc, ptMap_comp_ptMap]
  congr 2
  refine AlgHom.ext fun b => TrivSqZeroExt.ext ?_ ?_
  · simp [dualBC_fst, tangentAlg_fst]
  · simp [dualBC_snd, tangentAlg_snd]

variable [IsCommMonObj G] {p : ℕ}

end HodgeTate

section Valued

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

end Valued

end

end GlobalTheory.HodgeTateCompare
