import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models.Inhab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def trivTriple (H : Host E) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (a : OAct (𝓞 E) G) : SAB H S where
  G := G
  semi := hG
  act := a
  PP := UU.trivRig G
  cub := UU.trivCub G
  sym := PrimNorm.isSymmetric_of_hasGen _ ⟨UU.unitGen _ _, UU.unitGen_isGen _ _⟩
  adj := fun _ => ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (Out.Inh.linComb_triv_g _ _))⟩
  prim := ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (fun _ _ => rfl))⟩

def zeroTriple (H : Host E) (S : Scheme.{0}) : SAB H S :=
  trivTriple H (𝟙_ (Over S)) (isSemiAbelian_of_isAbelianScheme _ (UU.isAbelianScheme_unit S))
    ⟨fun _ => 𝟙 _, fun _ => inferInstance, rfl, fun _ _ => toUnit_unique _ _, fun _ _ => toUnit_unique _ _⟩

theorem isProper_zeroTriple (S : Scheme.{0}) : IsProper (zeroTriple H S).G.hom :=
  (UU.isAbelianScheme_unit S).proper

theorem abLocus_eq_univ {S : Scheme.{0}} (G : Over S) (h : IsProper G.hom) : abLocus G = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ _ _ _ => inferInstance

theorem abOpen_and_splitFib {S : Scheme.{0}} (t : SAB H S) (h : IsProper t.G.hom) : AbOpen t.G ∧ SplitFib t.G := by
  refine ⟨⟨⊤, (abLocus_eq_univ _ h).symm, inferInstance⟩, fun x => ?_⟩
  exact ⟨S.residueField x, inferInstance, Algebra.id _, inferInstance, inferInstance, _,
    ZJ.isGt_splitExtOfAbelian _ (isAbelianScheme_pullback_obj _ t.G ⟨t.semi.comm, t.semi.smooth, h, t.semi.geomConnected⟩)⟩

theorem good_zeroTriple (S : Scheme.{0}) : Good (zeroTriple H S) := by
  obtain ⟨h₁, h₂⟩ := abOpen_and_splitFib (zeroTriple H S) (isProper_zeroTriple S)
  refine ⟨h₁, h₂, fun x => ⟨⊤, trivial, fun _ => 1, fun i j => ?_, fun y _ => ⟨y, PUnit.unit, rfl, ?_⟩⟩⟩
  · exact (map_one _).trans ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).symm
  · rw [Scheme.basicOpen_one]
    exact ⟨trivial, trivial⟩

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

section General

variable {O F : Type} [CommRing O] [Field F] (β : O →+* F) {X : Scheme.{0}} (s : X ⟶ Sp O) (t : SAB H X)

def ofTriple (hn : Geo.Tor.IsNormalScheme X) (hp : IsProjOver s) (hf : Flat s) (W : (pullback s (spMap β)).Opens)
    (hW : pullback.fst s (spMap β) ⁻¹' abLocus t.G = W) (hd : Dense (W : Set (pullback s (spMap β) : Scheme)))
    (t₀ : SAB H W.toScheme) (m : SABMap t₀ t (W.ι ≫ pullback.fst _ _)) : Cpt (W.ι ≫ pullback.snd _ _) t₀ β :=
  ⟨X, s, hn, hp, hf, W.ι, rfl, inferInstance, by rwa [Scheme.Opens.range_ι], t, m, by rwa [Scheme.Opens.range_ι]⟩

def ofAbelian (hn : Geo.Tor.IsNormalScheme X) (hp : IsProjOver s) (hf : Flat s) (ha : IsProper t.G.hom)
    (t₀ : SAB H (pullback s (spMap β))) (m : SABMap t₀ t (𝟙 _ ≫ pullback.fst _ _)) :
    Cpt (pullback.snd s (spMap β)) t₀ β :=
  ⟨X, s, hn, hp, hf, 𝟙 _, Category.id_comp _, inferInstance, by simp, t, m, by simp [abLocus_eq_univ _ ha]⟩

end General

section Above

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U} {β : O →+* F}

theorem above_refl (C : Cpt c t₀ β) : ∃ ν : SABMap t₀ t₀ (𝟙 U), ν.φ = 𝟙 _ ∧
    Nonempty (C.Above C (RingHom.id O) (𝟙 U) ν) ∧ C.ExtendsAut (Iso.refl U) ν := by
  obtain ⟨ν, hν⟩ := ObjMaps.exists_sab_id t₀
  obtain ⟨mu, hmu⟩ := ObjMaps.exists_sab_id C.t
  have e : spMap (RingHom.id O) = 𝟙 _ := Spec.map_id _
  have w : 𝟙 C.X ≫ C.s = C.s ≫ spMap (RingHom.id O) := by simp [e]
  have hφ : C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ := by rw [hν, hmu]; simp
  refine ⟨ν, hν, ⟨⟨𝟙 _, w, ?_, mu, by simp, hφ⟩⟩, Iso.refl _, mu, by simp, by simp, hφ⟩
  have : IsIso (spMap (RingHom.id O)) := e ▸ inferInstance
  have h : pullback.lift (𝟙 C.X) C.s w ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have : IsIso (pullback.lift (𝟙 C.X) C.s w) := IsIso.of_isIso_fac_right h
  infer_instance

theorem abLocus_open_part (C : Cpt c t₀ β) : abLocus t₀.G = Set.univ := by
  refine Set.eq_univ_of_forall fun x => (abLocus_pullback abLocusOne C.t.semi C.m.cart.1 x).1 ?_
  have h : C.jQ x ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G := C.ab_gen ▸ Set.mem_range_self x
  simpa using h

end Above

theorem exists_above_of_finite {O F : Type} [CommRing O] [Field F] (β : O →+* F) {X X' : Scheme.{0}} (s : X ⟶ Sp O)
    (g : X' ⟶ X) [IsFinite g] (t : SAB H X) (hn : Geo.Tor.IsNormalScheme X) (hn' : Geo.Tor.IsNormalScheme X') (hp : IsProjOver s)
    (hf : Flat s) (hf' : Flat (g ≫ s)) (ha : IsProper t.G.hom) :
    ∃ (t₀ : SAB H (pullback s (spMap β))) (t₀' : SAB H (pullback (g ≫ s) (spMap β)))
      (C : Cpt (pullback.snd s (spMap β)) t₀ β) (C' : Cpt (pullback.snd (g ≫ s) (spMap β)) t₀' β)
      (r : pullback (g ≫ s) (spMap β) ⟶ pullback s (spMap β)) (ν : SABMap t₀' t₀ r)
      (a : C'.Above C (RingHom.id O) r ν), C.X = X ∧ C'.X = X' ∧ HEq a.π g ∧ HEq C.t t := by
  obtain ⟨t', ⟨mu⟩⟩ := exists_pull g t
  have ha' : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) mu.cart.1 ha
  obtain ⟨t₀, ⟨m⟩⟩ := exists_pull (𝟙 _ ≫ pullback.fst s (spMap β)) t
  obtain ⟨t₀', ⟨m'⟩⟩ := exists_pull (𝟙 _ ≫ pullback.fst (g ≫ s) (spMap β)) t'
  let r : pullback (g ≫ s) (spMap β) ⟶ pullback s (spMap β) :=
    pullback.lift (pullback.fst _ _ ≫ g) (pullback.snd _ _) (by simpa using pullback.condition)
  have hr : (𝟙 _ ≫ pullback.fst (g ≫ s) (spMap β)) ≫ g = r ≫ (𝟙 _ ≫ pullback.fst s (spMap β)) := by
    rw [Category.id_comp, Category.id_comp]; exact (pullback.lift_fst _ _ _).symm
  obtain ⟨n, hn₁⟩ := ObjMaps.exists_sab_comp mu m'
  have key : ∀ (f : pullback (g ≫ s) (spMap β) ⟶ X) (n : SABMap t₀' t f),
      f = r ≫ (𝟙 _ ≫ pullback.fst s (spMap β)) → ∃ ν : SABMap t₀' t₀ r, n.φ = ν.φ ≫ m.φ := by
    rintro _ n rfl
    exact ObjMaps.exists_sab_cancel m n
  obtain ⟨ν, hν⟩ := key _ n hr
  have e : spMap (RingHom.id O) = 𝟙 _ := Spec.map_id _
  have w : g ≫ s = (g ≫ s) ≫ spMap (RingHom.id O) := by simp [e]
  have hfin : IsFinite (pullback.lift g (g ≫ s) w) := by
    have : IsIso (spMap (RingHom.id O)) := e ▸ inferInstance
    have h : pullback.lift g (g ≫ s) w = g ≫ inv (pullback.fst s (spMap (RingHom.id O))) := by
      rw [IsIso.eq_comp_inv]; exact pullback.lift_fst _ _ _
    rw [h]; infer_instance
  exact ⟨t₀, t₀', ofAbelian β s t hn hp hf ha t₀ m,
    ofAbelian β (g ≫ s) t' hn' (isProjOver_comp_of_isFinite g hp) hf' ha' t₀' m', r, ν,
    ⟨g, w, hfin, mu, hr, hn₁.symm.trans hν⟩, rfl, rfl, HEq.rfl, HEq.rfl⟩

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  have := ProjSpace.Model.isIso_str_zero (R := R)
  exact ⟨0, inv (PSpace.str R 0), inferInstance, IsIso.inv_hom_id _⟩

theorem exists_gaussian : IsDedFrac (algebraMap ℤ ℚ) ∧
    ∃ (U U' : Scheme.{0}) (c : U ⟶ Sp ℚ) (c' : U' ⟶ Sp ℚ) (t₀ : SAB HostModel.host U) (t₀' : SAB HostModel.host U')
      (C : Cpt c t₀ (algebraMap ℤ ℚ)) (C' : Cpt c' t₀' (algebraMap ℤ ℚ)) (r : U' ⟶ U) (ν : SABMap t₀' t₀ r)
      (a : C'.Above C (RingHom.id ℤ) r ν), C.X = Sp ℤ ∧ C'.X = Sp GaussianInt ∧
        HEq a.π (spMap (algebraMap ℤ GaussianInt)) ∧ Good C.t := by
  refine ⟨⟨⟨inferInstance, inferInstance⟩, inferInstance, inferInstanceAs (IsFractionRing ℤ ℚ)⟩, ?_⟩
  have hM : Module.Finite ℤ GaussianInt := by
    refine Module.Finite.of_surjective ((LinearMap.toSpanSingleton ℤ _ 1).coprod
      (LinearMap.toSpanSingleton ℤ _ (⟨0, 1⟩ : GaussianInt))) fun z => ⟨(z.re, z.im), ?_⟩
    ext <;> simp
  have : IsFinite (spMap (algebraMap ℤ GaussianInt)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hM
  have hfl : Flat (spMap (algebraMap ℤ GaussianInt) ≫ 𝟙 _) := by
    rw [Category.comp_id, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  obtain ⟨t₀, t₀', C, C', r, ν, a, h₁, h₂, h₃, h₄⟩ := exists_above_of_finite (algebraMap ℤ ℚ) (𝟙 (Sp ℤ))
    (spMap (algebraMap ℤ GaussianInt)) (zeroTriple HostModel.host _) (ZJ.isNormalScheme_sp ℤ)
    (ZJ.isNormalScheme_sp GaussianInt) (isProjOver_id ℤ) inferInstance hfl (isProper_zeroTriple _)
  refine ⟨_, _, _, _, t₀, t₀', C, C', r, ν, a, h₁, h₂, h₃, ?_⟩
  have key : ∀ (Y : Scheme.{0}) (t : SAB HostModel.host Y), Y = Sp ℤ → HEq t (zeroTriple HostModel.host (Sp ℤ)) →
      Good t := by
    rintro _ _ rfl h
    obtain rfl := eq_of_heq h
    exact good_zeroTriple _
  exact key _ _ h₁ h₄

theorem system_primes_distinct_levels_ge_three {D : Datum H} {Xo : ∀ l : Level H, Moduli D l} (S : System Xo) :
    S.n true ≠ S.n false ∧ ∀ i, 3 ≤ S.n i ^ S.J i := by
  refine ⟨fun h => ?_, fun i => ?_⟩
  · have := S.ch_ne (S.n true)
    cases hc : S.ch (S.n true) <;> simp_all
  · obtain ⟨hp, ho, -⟩ := S.aux i
    have h2 := hp.two_le
    have h3 : 3 ≤ S.n i := by
      obtain ⟨k, hk⟩ := ho
      omega
    exact h3.trans (Nat.le_self_pow (by have := S.J_pos i; omega) _)

theorem isPrimeToPart_unique {l₀ l₀' l : Level H} {p : ℕ} (h : IsPrimeToPart l₀ l p) (h' : IsPrimeToPart l₀' l p) :
    l₀ = l₀' := by
  obtain ⟨a, b, c⟩ := h
  obtain ⟨a', b', c'⟩ := h'
  cases l₀; cases l₀'
  simp only at a b c a' b' c'
  subst a b c a' b' c'
  rfl

theorem exists_isInc (l : Level H) (n : ℕ) : ∃ β : RZ H n l.A →+* KA l,
    IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β := by
  have h : RZ H n l.A ≤ (KA l).toSubfield.toSubring := by
    refine Subring.closure_le.2 ?_
    have h₁ : H.rt0 ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
    have h₂ : zeta l.A ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
    rintro x (rfl | rfl | rfl)
    · exact (KA l).div_mem (add_mem (one_mem _) h₁) (by exact_mod_cast natCast_mem (KA l) 2)
    · exact (KA l).inv_mem (natCast_mem (KA l) n)
    · exact h₂
  exact ⟨Subring.inclusion h, fun _ => rfl⟩

end GlobalTheory.Models.Inhab

end
