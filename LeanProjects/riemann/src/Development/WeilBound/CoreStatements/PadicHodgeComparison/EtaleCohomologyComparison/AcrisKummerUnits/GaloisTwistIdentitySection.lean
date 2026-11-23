import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def galOC (σ : Gal(PadicAlgCl l/K)) : OC l →+* OC l := integerMap (galCp σ : ℂ_[l] →+* ℂ_[l]) (AInf.norm_galCp_toRingHom σ)

def galOb (σ : Gal(PadicAlgCl l/K)) : Ob l →+* Ob l := preTiltMap l (galCp σ : ℂ_[l] →+* ℂ_[l]) (AInf.norm_galCp_toRingHom σ)

theorem isUnit_kummerEta (σ : Gal(PadicAlgCl l/K)) : IsUnit (kummerEta σ) :=
  (IsPerfectoidField.isUnit_iff_norm_untilt l).2 (by rw [untilt_kummerEta]; simp)

theorem theta0_gal (σ : Gal(PadicAlgCl l/K)) (x : Ainf l) :
    theta0 l (WittVector.map (galOb σ) x) = galOC σ (theta0 l x) := fontaineTheta_map_preTiltMap _ _ x

namespace PAlg

def tw (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : PAlg l where
  A := A.A
  s := A.s.comp (galOb σ)
  perf := A.perf
  compl := by
    have e : Ideal.span {A.s.comp (galOb σ) (pFlat l)} = Ideal.span {A.s (pFlat l)} := by
      rw [RingHom.comp_apply, galOb, pFlat_mul_kummerEta, map_mul]
      exact Ideal.span_singleton_mul_right_unit ((isUnit_kummerEta σ).map A.s) _
    rw [e]; exact A.compl
  tf := by
    rw [RingHom.comp_apply, galOb, pFlat_mul_kummerEta, map_mul]
    exact mul_mem A.tf ((isUnit_kummerEta σ).map A.s).mem_nonZeroDivisors

theorem tw_pi (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : (tw σ A).pi = A.pi * A.s (kummerEta σ) := by
  change A.s (galOb σ (pFlat l)) = _
  rw [galOb, pFlat_mul_kummerEta, map_mul]; rfl

theorem IsTest.tw (σ : Gal(PadicAlgCl l/K)) {A : PAlg l} (h : A.IsTest) : (tw σ A).IsTest :=
  ⟨h.1, fun f g ⟨N, hN⟩ => h.2 f g ⟨N, by
    rw [tw_pi, mul_pow] at hN
    exact (Ideal.mul_unit_mem_iff_mem _ (((isUnit_kummerEta σ).map A.s).pow N)).1 hN⟩⟩

def twId (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : (tw σ A).A →+* A.A := RingHom.id A.A

theorem galois_twist_identity_section (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : (twId σ A).comp (tw σ A).s = A.s.comp (galOb σ) := rfl

theorem pdOk_twId (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : PdOk (twId σ A) :=
  pdOk_of_over (galois_twist_identity_section σ A) fun k => ACris.dpow_mem (ACris.gal_smul_mem_ker σ xi0_mem) k

def twAcr (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) : (tw σ A).Acr n →+* A.Acr n := (pdOk_twId σ A).acr n

theorem twAcr_cris (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (a : Acris l) :
    twAcr σ A n ((tw σ A).cris n a) = A.cris n (ACris.galCris σ a) :=
  (pdOk_twId σ A).acr_cris (galois_twist_identity_section σ A) (ACris.galZero σ) (fun y => RingHom.congr_fun (f := ACris.galAway σ)
    (awayW_ext fun x => by rw [ACris.galAway_algebraMap, awayW_algebraMap]; rfl) y.1) n a

def twU (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : (tw σ A).U →+* A.U :=
  Ideal.Quotient.lift _ (A.th.comp (WittVector.map (twId σ A))) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have e : WittVector.map (twId σ A) (tw σ A).xi = A.sW (WittVector.map (galOb σ) (xi0 l)) := by
      rw [xi, sW, sW, ← wmap_comp, galois_twist_identity_section, wmap_comp]
    rw [map_mul, RingHom.comp_apply _ _ (tw σ A).xi, e, ← oC_theta0, theta0_gal, RingHom.mem_ker.1 xi0_mem, map_zero,
      map_zero, mul_zero]

theorem twU_th (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (x : (tw σ A).W) :
    twU σ A ((tw σ A).th x) = A.th (WittVector.map (twId σ A) x) := rfl

theorem twU_oC (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (x : OC l) : twU σ A ((tw σ A).oC x) = A.oC (galOC σ x) := by
  obtain ⟨y, rfl⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l x
  rw [oC_theta0, twU_th, ← theta0_gal, oC_theta0, sW, sW, ← wmap_comp, galois_twist_identity_section, wmap_comp]

theorem twU_bijective (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : Function.Bijective (twU σ A) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
    have hy : WittVector.map (twId σ A) y = y := wmap_id (R := A.A) y
    have e : (A.xi : WittVector l A.A) = (tw σ A).sW (σ⁻¹ • xi0 l) := by
      have : WittVector.map (galOb σ) (σ⁻¹ • xi0 l) = xi0 l := smul_inv_smul σ (xi0 l)
      exact (congrArg (WittVector.map A.s) this.symm).trans (wmap_comp _ _ _).symm
    have h0 : (tw σ A).th ((tw σ A).sW (σ⁻¹ • xi0 l)) = 0 := by
      rw [← oC_theta0, RingHom.mem_ker.1 (ACris.gal_smul_mem_ker σ⁻¹ xi0_mem), map_zero]
    rw [hy, e] at hc
    change (tw σ A).th y = 0
    rw [← hc]
    exact (map_mul (tw σ A).th c _).trans ((congrArg (_ * ·) h0).trans (mul_zero _))
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨(tw σ A).th x, congrArg A.th (wmap_id (R := A.A) x)⟩

def twUEquiv (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : (tw σ A).U ≃+* A.U := RingEquiv.ofBijective _ (twU_bijective σ A)

def twMap (σ : Gal(PadicAlgCl l/K)) {A B : PAlg l} (f : A ⟶ B) : tw σ A ⟶ tw σ B :=
  ⟨(Hom.f f : A.A →+* B.A), by change (Hom.f f).comp (A.s.comp _) = B.s.comp _; rw [← RingHom.comp_assoc, Hom.comm f]⟩

theorem twU_mapU (σ : Gal(PadicAlgCl l/K)) {A B : PAlg l} (f : A ⟶ B) (x : (tw σ A).U) :
    twU σ B (mapU (twMap σ f) x) = mapU f (twU σ A x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change B.th (WittVector.map _ (WittVector.map _ y)) = B.th (WittVector.map _ (WittVector.map _ y))
  rw [← wmap_comp, ← wmap_comp]; rfl

theorem twAcr_mapAcr (σ : Gal(PadicAlgCl l/K)) {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (x : (tw σ A).Acr n) :
    twAcr σ B n (mapAcr (twMap σ f) n x) = mapAcr f n (twAcr σ A n x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine congrArg (B.mkAcr n) (Subtype.ext ?_)
  change awayW (twId σ B) (awayW (Hom.f (twMap σ f)) y.1) = awayW (Hom.f f) (awayW (twId σ A) y.1)
  rw [← RingHom.comp_apply, ← awayW_comp, ← RingHom.comp_apply, ← awayW_comp]; rfl

end PAlg

open PAlg

def twF (σ : Gal(PadicAlgCl l/K)) : PAlg l ⥤ PAlg l where
  obj := tw σ
  map := twMap σ
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev El (P : PAlg l ⥤ Type) : Type 1 := (testι l ⋙ P).Elements

abbrev elπ (P : PAlg l ⥤ Type) : El P ⥤ PAlg l := CategoryOfElements.π _ ⋙ testι l

abbrev AcrEl (P : PAlg l ⥤ Type) (n : ℕ) : El P ⥤ CommAlgCat.{0} (Acris l) := elπ P ⋙ AcrA l n

abbrev MH (P : PAlg l ⥤ Type) (n j : ℕ) : Type 1 := CH.H (CH.modF (AcrEl P n)) j

def FilEl (P : PAlg l ⥤ Type) (n r : ℕ) : CH.SubF (CH.modF (AcrEl P n)) where
  S T := (((elπ P).obj T).Fil n r).restrictScalars (Acris l)
  map_mem φ _ hx := mapAcr_fil ((elπ P).map φ) n r hx

def MFil (P : PAlg l ⥤ Type) (n r j : ℕ) : Submodule (Acris l) (MH P n j) := (FilEl P n r).img j

def phiMor (P : PAlg l ⥤ Type) (n : ℕ) : CH.Mor (CH.modF (AcrEl P n)) (CH.modF (AcrEl P n)) (ACris.phi ℂ_[l] l) where
  G := 𝟭 _
  τ T := { toFun := ((elπ P).obj T).phi n
           map_add' := map_add _
           map_smul' := fun a (x : ((elπ P).obj T).Acr n) => (map_mul (((elπ P).obj T).phi n) (((elπ P).obj T).cris n a) x).trans
             (congrArg (· * ((elπ P).obj T).phi n x) (((elπ P).obj T).phi_cris n a)) }
  nat φ x := (mapAcr_phi ((elπ P).map φ) n x).symm

def redEl (P : PAlg l ⥤ Type) {m n : ℕ} (h : n ≤ m) : CH.modF (AcrEl P m) ⟶ CH.modF (AcrEl P n) :=
  Functor.whiskerLeft (elπ P) (redF l h)

def MSys (P : PAlg l ⥤ Type) (j : ℕ) : Sys.{1} (Acris l) :=
  CH.towerH (fun n => CH.modF (AcrEl P n)) (fun n => redEl P n.le_succ) j

def elMap {P P' : PAlg l ⥤ Type} (u : P ⟶ P') : El P ⥤ El P' := CategoryOfElements.map (Functor.whiskerLeft (testι l) u)

def pullMor {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (n : ℕ) :
    CH.Mor (CH.modF (AcrEl P' n)) (CH.modF (AcrEl P n)) (RingHom.id _) where
  G := elMap u
  τ _ := LinearMap.id
  nat _ _ := rfl

def elTw (σ : Gal(PadicAlgCl l/K)) {P : PAlg l ⥤ Type} (a : P ⟶ twF σ ⋙ P) : El P ⥤ El P where
  obj T := ⟨⟨tw σ T.1.obj, T.1.property.tw σ⟩, a.app T.1.obj T.2⟩
  map {T T'} φ := ⟨ObjectProperty.homMk (twMap σ φ.1.hom), by
    have h := ConcreteCategory.congr_hom (a.naturality φ.1.hom) T.2
    have e : P.map φ.1.hom T.2 = T'.2 := φ.2
    exact h.symm.trans (congrArg (a.app T'.1.obj) e)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def galMor (σ : Gal(PadicAlgCl l/K)) {P : PAlg l ⥤ Type} (a : P ⟶ twF σ ⋙ P) (n : ℕ) :
    CH.Mor (CH.modF (AcrEl P n)) (CH.modF (AcrEl P n)) (ACris.galCris σ) where
  G := elTw σ a
  τ T := { toFun := twAcr σ T.1.obj n
           map_add' := map_add _
           map_smul' := fun c (x : (tw σ T.1.obj).Acr n) => (map_mul (twAcr σ T.1.obj n) ((tw σ T.1.obj).cris n c) x).trans
             (congrArg (· * twAcr σ T.1.obj n x) (twAcr_cris σ T.1.obj n c)) }
  nat φ x := twAcr_mapAcr σ φ.1.hom n x

section Points
variable {O : Type} [CommRing O] {X Y : Scheme.{0}}

def PX (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l) : PAlg l ⥤ Type where
  obj A := {y : Spec (CommRingCat.of A.U) ⟶ X // y ≫ q = Spec.map (CommRingCat.ofHom (A.oC.comp κ))}
  map {A B} f := TypeCat.ofHom fun y => ⟨Spec.map (CommRingCat.ofHom (mapU f)) ≫ y.1, by
    rw [Category.assoc, y.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => mapU_oC f _⟩
  map_id A := by
    ext y
    change Spec.map (CommRingCat.ofHom (mapU (𝟙 A))) ≫ y.1 = y.1
    rw [mapU_id, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  map_comp f g := by
    ext y
    change Spec.map (CommRingCat.ofHom (mapU (f ≫ g))) ≫ y.1 =
      Spec.map (CommRingCat.ofHom (mapU g)) ≫ Spec.map (CommRingCat.ofHom (mapU f)) ≫ y.1
    rw [mapU_comp, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

def pxMap {p : X ⟶ Spec (CommRingCat.of O)} {q : Y ⟶ Spec (CommRingCat.of O)} (κ : O →+* OC l) (u : X ⟶ Y) (hu : u ≫ q = p) :
    PX p κ ⟶ PX q κ where
  app A := TypeCat.ofHom fun y => ⟨y.1 ≫ u, by rw [Category.assoc, hu]; exact y.2⟩
  naturality A B f := by
    ext y
    exact Subtype.ext (Category.assoc _ _ _)

def pxTw (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l) (σ : Gal(PadicAlgCl l/K)) (h : ∀ x, galOC σ (κ x) = κ x) :
    PX q κ ⟶ twF σ ⋙ PX q κ where
  app A := TypeCat.ofHom fun y => ⟨Spec.map (CommRingCat.ofHom (twUEquiv σ A).symm.toRingHom) ≫ y.1, by
    rw [Category.assoc, y.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => (twUEquiv σ A).symm_apply_eq.2 ?_
    exact ((twU_oC σ A (κ x)).trans (congrArg A.oC (h x))).symm⟩
  naturality A B f := by
    ext y
    refine Subtype.ext ?_
    change Spec.map (CommRingCat.ofHom (twUEquiv σ B).symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom (mapU f)) ≫ y.1 =
      Spec.map (CommRingCat.ofHom (mapU (twMap σ f))) ≫ Spec.map (CommRingCat.ofHom (twUEquiv σ A).symm.toRingHom) ≫ y.1
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    refine RingHom.ext fun x => (twUEquiv σ B).symm_apply_eq.2 ?_
    exact ((twU_mapU σ f _).trans (congrArg (mapU f) ((twUEquiv σ A).apply_symm_apply x))).symm

end Points

end CrystallineSemistableComparison
