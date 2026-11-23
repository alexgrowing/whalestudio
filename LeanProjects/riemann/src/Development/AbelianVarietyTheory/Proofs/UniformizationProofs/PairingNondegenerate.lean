import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntermediateFieldOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAffineWeightUnits
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionGeometricPointOfField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusQuotientCardTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfCubWeilOrthogonal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAbelianPartDimAddTorusRank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfPowEqOneOfLocalHom
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU.SpecialPairing

theorem card_map {A₀ A A' : Type} [CommGroup A₀] [CommGroup A] [CommGroup A'] (r : A →* A₀) (j : A →* A') (N : ℕ)
    (ri : ∀ y y', y ^ N = 1 → y' ^ N = 1 → r y = r y' → y = y') (rs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ r y = x)
    (hj : Function.Injective j) (K : Subgroup A₀) :
    Nat.card (((powMonoidHom N).ker ⊓ K.comap r).map j) = Nat.card {x : A₀ // x ^ N = 1 ∧ x ∈ K} := by
  rw [Subgroup.card_map_of_injective hj]
  refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨r y.1, by rw [← map_pow, show y.1 ^ N = 1 from y.2.1, map_one],
    y.2.2⟩) ⟨fun y y' h => Subtype.ext (ri _ _ y.2.1 y'.2.1 (congrArg Subtype.val h)), fun x => ?_⟩)
  obtain ⟨y, hy, e⟩ := rs x.1 x.2.1
  exact ⟨⟨y, hy, show r y ∈ K from e ▸ x.2.2⟩, Subtype.ext e⟩

theorem core {A₀ A A' B : Type} [CommGroup A₀] [CommGroup A] [CommGroup A'] [CommGroup B] (r : A →* A₀)
    (j : A →* A') (q : A₀ →* B) (N M : ℕ) (P' : A' → A' → Prop) (P : B → B → Prop)
    (ri : ∀ y y', y ^ N = 1 → y' ^ N = 1 → r y = r y' → y = y') (rs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ r y = x)
    (hj : Function.Injective j) (qs : ∀ b, b ^ N = 1 → ∃ x, x ^ N = 1 ∧ q x = b)
    (hP : ∀ y y', y ^ N = 1 → y' ^ N = 1 → P (q (r y)) (q (r y')) → P' (j y) (j y'))
    (h1 : ∀ b, b ^ N = 1 → P 1 b)
    (hc : Nat.card {x : A₀ // x ^ N = 1 ∧ q x = 1} * Nat.card {x : A₀ // x ^ N = 1} = M)
    (rad : ∀ T H : Subgroup A', (∀ x ∈ T, x ^ N = 1) → (∀ x ∈ H, x ^ N = 1) → Nat.card T * Nat.card H = M →
      (∀ x ∈ T, ∀ y ∈ H, P' x y) → ∀ x, x ^ N = 1 → (∀ y ∈ H, P' x y) → x ∈ T)
    (b : B) (hb : b ^ N = 1) (h : ∀ b', b' ^ N = 1 → P b b') : b = 1 := by
  have tq : ∀ y : A, y ^ N = 1 → q (r y) ^ N = 1 := fun y hy => by rw [← map_pow, ← map_pow, hy, map_one, map_one]
  have tj : ∀ y : A, y ^ N = 1 → j y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]
  obtain ⟨x, hx, rfl⟩ := qs b hb
  obtain ⟨y, hy, rfl⟩ := rs x hx
  obtain ⟨y', hy', e⟩ := rad (((powMonoidHom N).ker ⊓ q.ker.comap r).map j)
    (((powMonoidHom N).ker ⊓ (⊤ : Subgroup A₀).comap r).map j)
    (by rintro _ ⟨z, hz, rfl⟩; exact tj z hz.1) (by rintro _ ⟨z, hz, rfl⟩; exact tj z hz.1)
    (by
      rw [card_map r j N ri rs hj, card_map r j N ri rs hj, ← hc]
      simp only [Subgroup.mem_top, and_true, MonoidHom.mem_ker])
    (by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
      refine hP z z' hz.1 hz'.1 ?_
      rw [show q (r z) = 1 from hz.2]
      exact h1 _ (tq _ hz'.1))
    (j y) (tj y hy) (by
      rintro _ ⟨z', hz', rfl⟩
      exact hP y z' hy hz'.1 (h _ (tq _ hz'.1)))
  obtain rfl := hj e
  exact hy'.2

theorem exists_embedding (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] [Algebra V W]
    [Module.Finite V W] (h : Function.Injective (algebraMap V W)) :
    ∃ φ : W →+* AlgebraicClosure (FractionRing V), Function.Injective φ ∧ φ.comp (algebraMap V W) =
      (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V)) := by
  have i : Function.Injective (algebraMap V (AlgebraicClosure (FractionRing V))) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V)]
    exact (algebraMap (FractionRing V) _).injective.comp (IsFractionRing.injective V (FractionRing V))
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 h
  have : FaithfulSMul V (AlgebraicClosure (FractionRing V)) := (faithfulSMul_iff_algebraMap_injective _ _).2 i
  let φ : W →ₐ[V] AlgebraicClosure (FractionRing V) := IsAlgClosed.lift
  refine ⟨φ.toRingHom, ?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    rw [RingHom.comap_ker, show φ.toRingHom.comp (algebraMap V W) = algebraMap V _ from φ.comp_algebraMap]
    exact (RingHom.injective_iff_ker_eq_bot _).1 i
  · rw [← IsScalarTower.algebraMap_eq]; exact φ.comp_algebraMap

theorem torsion_ext (W : Type) [CommRing W] [IsLocalRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (p : Spec (CommRingCat.of W) ⟶ S) (N : ℕ)
    (hN : IsUnit (N : W)) {Ω : Type} [Field Ω] (f : W →+* Ω) [IsLocalHom f] (y y' : Over.mk p ⟶ G) (hy : y ^ N = 1)
    (hy' : y' ^ N = 1) (e : Spec.map (CommRingCat.ofHom f) ≫ y.left = Spec.map (CommRingCat.ofHom f) ≫ y'.left) :
    y = y' := by
  have := GlobalTheory.TorsionSeparable.epi_specMap (IsLocalRing.ResidueField.lift f)
  rw [← IsLocalRing.ResidueField.lift_comp_residue f, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Category.assoc, cancel_epi] at e
  let ρ : Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ p) ⟶ Over.mk p :=
    Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W))) rfl
  exact (GlobalTheory.existsUnique_torsion_lift W S G p N hN (ρ ≫ y)
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])).unique ⟨hy, rfl⟩ ⟨hy', e.symm⟩

theorem toBase_bijective {S S' : Scheme.{0}} (G : Over S) (f : S' ⟶ S) (T : Over S') :
    Function.Bijective (toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f)
      pullback.condition (T := T)) :=
  ⟨fun x y h => Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun z => z.left) h)
    ((Over.w x).trans (Over.w y).symm)), fun x =>
    ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩⟩

set_option maxHeartbeats 800000 in

theorem pairing_nondegenerate : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun {V} _ _ _ {_} {_} _ _ s => ∀ (t : Tower s) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))) (N : ℕ), IsUnit (N : V) → ∀ x : Over.mk p ⟶ (t.l 0).Q.B, x ^ N = 1 → (∀ y : Over.mk p ⟶ (t.l 0).Q.B, y ^ N = 1 → CubWeil (t.l 0).D.M.c N x y 1) → x = 1 := by
  intro hAb hL V _ _ _ A G _ _ s t Ω _ _ p N hN
  obtain ⟨dvr, cpl, -⟩ := s.cdvr
  have := s.semi.smooth
  have := s.semi.separated
  have := (t.l 0).Q.q_hom
  obtain ⟨φ₀, rfl⟩ : ∃ φ₀ : (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) →+* Ω, p = Spec.map (CommRingCat.ofHom φ₀) :=
    ⟨(Spec.preimage p).hom, (Spec.map_preimage p).symm⟩
  let f : V →+* Ω := φ₀.comp (Ideal.Quotient.mk _)
  have hf : IsLocalHom f := ⟨fun a ha => by
    by_contra h
    have : Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact h)
    exact ha.ne_zero (by rw [RingHom.comp_apply, this, map_zero])⟩
  have hNΩ : (N : Ω) ≠ 0 := by simpa using (hN.map f).ne_zero
  have hN0 : N ≠ 0 := by rintro rfl; simp at hNΩ
  obtain ⟨g', hg'⟩ : ∃ g', SmoothOfRelativeDimension g' (t.l 0).Q.B.hom := by
    have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := φ₀.domain_nontrivial
    have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    exact GlobalTheory.AbelianDim.exists_relDim _ _ (t.l 0).Q.isAb
  have hd := (GlobalTheory.UU.Tower.dim_eq_add_finrank V A G s t g').1 hg'
  obtain ⟨c₁, c₂⟩ := torusQuotient_card_torsion _ _ _ (t.l 0).Q Ω (Spec.map (CommRingCat.ofHom φ₀)) N hNΩ
  rw [GlobalTheory.card_torsion_geometricPoint_of_field hAb _ _ (t.l 0).Q.isAb g' hg' Ω _ N hNΩ] at c₂
  let T₀ : Over (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))) :=
    Over.mk (Spec.map (CommRingCat.ofHom φ₀))
  have hpf : Spec.map (CommRingCat.ofHom f) = T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0 := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  let β : (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) ≃*
      (Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) ⟶ G) :=
    MulEquiv.ofBijective (toBaseHom (toBase_mul_pullback G _) T₀) (toBase_bijective G _ T₀)
  have hβ : ∀ x, (β x).left = x.left ≫ (fstG _ 0 G).left := fun _ => rfl
  let ι₀ : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hpf.symm)
  have fin : Finite {x : T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G // x ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  have fin' := (show Set.Finite {x : T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G | x ^ N = 1} from fin).image
    (fun x => ι₀ ≫ β x)
  obtain ⟨W, _, _, _, _, _, f', _, inj, _, _, hf', lifts⟩ := GlobalTheory.exists_finite_extension_torsion_lift hL.unramExt V G N
    hN Ω f hf fin'.toFinset (by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := fin'.mem_toFinset.1 hx
      show (ι₀ ≫ β u) ^ N = 1
      rw [← MonObj.comp_pow, ← map_pow, show u ^ N = 1 from hu, map_one, MonObj.comp_one])
  obtain ⟨φ, φi, hφ⟩ := exists_embedding V W inj
  let TW : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let ρ : Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) ⟶ TW :=
    Over.homMk (Spec.map (CommRingCat.ofHom f')) (by
      refine Eq.trans ?_ hpf
      rw [← hf', CommRingCat.ofHom_comp, Spec.map_comp]; rfl)
  let σ : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ TW :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
      have e := congrArg (fun z => Spec.map (CommRingCat.ofHom z)) hφ
      simp only [CommRingCat.ofHom_comp, Spec.map_comp] at e
      exact e)
  let r : (TW ⟶ G) →* (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) := β.symm.toMonoidHom.comp (preHom ρ)
  have hr : ∀ y, (r y).left ≫ (fstG _ 0 G).left = Spec.map (CommRingCat.ofHom f') ≫ y.left := fun y =>
    (hβ _).symm.trans (congrArg (fun z => z.left) (β.apply_symm_apply (ρ ≫ y)))
  let q : (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) →* (T₀ ⟶ (t.l 0).Q.B) :=
    MonoidHom.mk' (· ≫ (t.l 0).Q.q) fun x y => MonObj.mul_comp x y _
  refine core r (preHom σ) q N (N ^ (2 * A.g)) (fun x y => CubWeil s.P.c N x y 1)
    (fun x y => CubWeil (t.l 0).D.M.c N x y 1) (fun y y' hy hy' e => ?_) (fun x hx => ?_) (fun y y' e => ?_)
    ?_ (fun y y' hy hy' h => ?_) (fun b hb => cubWeil_one_left _ hb) ?_
    (mem_of_cubWeil_orthogonal hL V A G s _ N (Nat.one_le_iff_ne_zero.2 hN0))
  · refine torsion_ext W G _ N (by simpa using hN.map (algebraMap V W)) f' y y' hy hy' ?_
    rw [← hr, ← hr, e]
  · obtain ⟨y, hy, e⟩ := lifts (ι₀ ≫ β x) (fin'.mem_toFinset.2 ⟨x, hx, rfl⟩)
    refine ⟨y, hy, β.injective (Over.OverMorphism.ext ?_)⟩
    have e' : (ι₀ ≫ β x).left = (β x).left := Category.id_comp _
    rw [hβ, hr y, e, e']
  · exact GlobalTheory.over_points_ext_of_injective _ G W _ φ φi _ y y' (congrArg (fun z => z.left) e)
  · refine (torusQuotient_points_lift _ _ _ (t.l 0).Q Ω _).2 N fun a => ?_
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a.val (Nat.pos_of_ne_zero hN0)
    have hz0 : z ≠ 0 := by rintro rfl; exact a.ne_zero (by rw [← hz, zero_pow hN0])
    exact ⟨Units.mk0 z hz0, Units.ext hz⟩
  · have := ((cubWeil_one_iff_closedFibre V A G s t W Ω f' inferInstance _ N hN y y' (r y) (r y') hy hy' (hr y) (hr y')).2 h).comp σ
    rwa [map_one] at this
  · have e : N ^ (2 * A.g) = N ^ Module.finrank ℤ s.X * (N ^ Module.finrank ℤ s.X * N ^ (2 * g')) := by
      rw [hd]; ring
    rw [e]
    exact congrArg₂ (· * ·) ((Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)).trans c₁) c₂

end GlobalTheory.UU.SpecialPairing
end
