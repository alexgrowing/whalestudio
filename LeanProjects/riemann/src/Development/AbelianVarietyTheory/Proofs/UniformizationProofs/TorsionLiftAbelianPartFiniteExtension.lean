import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionGeometricPointOfField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFinsetPointExtendsValuationSubalgebra
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageEqOneIffTorusPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageOneMulInv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLiftExtending
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFormalTorusPointsSemiAbelianModel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.TorsionLift

theorem exists_char_root {X M : Type} [AddCommGroup X] [CommGroup M] {I : Type} (β : Module.Basis I ℤ X)
    (N : ℕ) (c : Multiplicative X →* M) (h : ∀ i, ∃ u : M, u ^ N = c (Multiplicative.ofAdd (β i))) :
    ∃ d : Multiplicative X →* M, d ^ N = c := by
  choose u hu using h
  let l : X →ₗ[ℤ] Additive M := β.constr ℤ (fun i => Additive.ofMul (u i))
  refine ⟨AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, ?_⟩
  have : N • l = (MonoidHom.toAdditiveRight c).toIntLinearMap := by
    refine β.ext fun i => ?_
    simp only [l, LinearMap.smul_apply, Module.Basis.constr_basis, ← ofMul_pow, hu]
    rfl
  refine MonoidHom.ext fun x => ?_
  have h2 := congrArg Additive.toMul (LinearMap.congr_fun this x.toAdd)
  rw [LinearMap.smul_apply, toMul_nsmul] at h2
  exact h2

theorem exists_big (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] (F : Type) [Field F] [IsAlgClosed F] [Algebra V F]
    [FaithfulSMul V F] [Algebra.IsAlgebraic V F] (W₁ : Subalgebra V F) [Module.Finite V W₁] (N : ℕ) (hN : 1 ≤ N)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {J : Type} [Finite J]
    (c : J → (Multiplicative X →* (W₁)ˣ)) :
    ∃ (W : Subalgebra V F) (_ : IsLocalRing W) (h : W₁ ≤ W),
      IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧ IsLocalHom (algebraMap V W) ∧
      (∀ z : F, z ^ N = 1 → z ∈ W) ∧
      ∀ j, ∃ d : Multiplicative X →* (W)ˣ,
        d ^ N = (Units.map (Subalgebra.inclusion h).toRingHom.toMonoidHom).comp (c j) := by
  classical
  let β := Module.Free.chooseBasis ℤ X
  have hz : ∀ j i, ∃ z : F, z ^ N = ((c j (Multiplicative.ofAdd (β i))).val : F) :=
    fun j i => IsAlgClosed.exists_pow_nat_eq _ hN
  choose z hz using hz
  obtain ⟨g, hg⟩ := (Module.Finite.fg_top (R := V) (M := W₁))
  have := Fintype.ofFinite J
  let s : Finset F := (g.image Subtype.val ∪ Polynomial.nthRootsFinset N 1) ∪
    (Finset.univ.image fun p : J × Module.Free.ChooseBasisIndex ℤ X => z p.1 p.2)
  obtain ⟨W, hW, -, hc, -, -, hl, -, hint⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra V F s
  have hI : ∀ w : W₁, IsIntegral V (w : F) := fun w =>
    (Algebra.IsIntegral.isIntegral (R := V) w).map W₁.val
  have hle : W₁ ≤ W := by
    intro w hw
    have : (⟨w, hw⟩ : W₁) ∈ Submodule.span V (g : Set W₁) := hg ▸ Submodule.mem_top
    have h2 : Submodule.span V (g : Set W₁) ≤ (Subalgebra.toSubmodule W).comap W₁.val.toLinearMap := by
      rw [Submodule.span_le]
      intro a ha
      exact hint a (by simp only [s, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨a, ha, rfl⟩)) (hI a)
    exact h2 this
  refine ⟨W, inferInstance, hle, hc, hl, ?_, fun j => exists_char_root β N _ fun i => ?_⟩
  · intro x hx
    refine hint x ?_ (IsIntegral.of_pow hN (by rw [hx]; exact isIntegral_one))
    simp only [s, Finset.mem_union]
    exact Or.inl (Or.inr ((Polynomial.mem_nthRootsFinset hN 1).2 hx))
  · have hm : z j i ∈ W := by
      refine hint _ ?_ (IsIntegral.of_pow hN (by rw [hz]; exact hI _))
      simp only [s, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨(j, i), Finset.mem_univ _, rfl⟩
    have he : (⟨z j i, hm⟩ : W) ^ N =
        (((Units.map (Subalgebra.inclusion hle).toRingHom.toMonoidHom).comp (c j)) (Multiplicative.ofAdd (β i))).val :=
      Subtype.ext (hz j i)
    have hu : IsUnit (⟨z j i, hm⟩ : W) := by
      rw [← isUnit_pow_iff (n := N) (by omega), he]; exact Units.isUnit _
    refine ⟨hu.unit, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, hu.unit_spec, he]

section
variable {V : Type} [CommRing V]

abbrev PT (V W : Type) [CommRing V] [CommRing W] [Algebra V W] : Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))

def ptMap {W W' : Type} [CommRing W] [CommRing W'] [Algebra V W] [Algebra V W'] (ψ : W →ₐ[V] W') :
    PT V W' ⟶ PT V W :=
  Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap)

theorem scal_comp_specMap {W W' : Type} [CommRing W] [CommRing W'] (ψ : W →+* W') {Z : Scheme.{0}}
    (r : Z ⟶ Spec (CommRingCat.of W')) (w : W) :
    scal (r ≫ Spec.map (CommRingCat.ofHom ψ)) w = scal r (ψ w) := by
  unfold scal
  rw [Scheme.Hom.comp_appTop]
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  have h2 := congrArg (fun f => f.hom w) this
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 ⊢
  rw [h2]
end

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] {s : HidaSetting V A G}

def Im (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [Algebra V W] (x : PT V W ⟶ G) (b : PT V W ⟶ a.B) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left

def Tp (t : Tower s) (W : Type) [CommRing W] [Algebra V W] (x : PT V W ⟶ G) (c : Multiplicative s.X →* Wˣ) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ (Spec.map (CommRingCat.ofHom (algebraMap V W))) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (c (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ (x).left

theorem Im.pull {t : Tower s} {a : t.Alg} {W W' : Type} [CommRing W] [Algebra V W] [CommRing W'] [Algebra V W']
    (ψ : W →ₐ[V] W') {x : PT V W ⟶ G} {b : PT V W ⟶ a.B} (h : Im t a W x b) :
    Im t a W' (ptMap ψ ≫ x) (ptMap ψ ≫ b) := by
  intro e Z r xe hxe
  have := h e Z (r ≫ (ptMap ψ).left) xe (by rw [hxe, Category.assoc]; rfl)
  rw [this, Category.assoc]; rfl

theorem Tp.pull {t : Tower s} {W W' : Type} [CommRing W] [Algebra V W] [CommRing W'] [Algebra V W']
    (ψ : W →ₐ[V] W') {x : PT V W ⟶ G} {c : Multiplicative s.X →* Wˣ} (h : Tp t W x c) :
    Tp t W' (ptMap ψ ≫ x) ((Units.map ψ.toRingHom.toMonoidHom).comp c) := by
  intro e Z r τ h1 h2
  have := h e Z (r ≫ (ptMap ψ).left) τ (by
      rw [h1, Category.assoc]; exact congrArg (r ≫ ·) (Over.w (ptMap ψ)).symm)
    (fun χ => (h2 χ).trans (scal_comp_specMap ψ.toRingHom r _).symm)
  rw [this, Category.assoc]; rfl

theorem Im.pow {t : Tower s} {a : t.Alg} {W : Type} [CommRing W] [Algebra V W]
    {x : PT V W ⟶ G} {b : PT V W ⟶ a.B} (h : Im t a W x b) (n : ℕ) : Im t a W (x ^ n) (b ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (GlobalTheory.UU.image_one_mul_inv V A G s t a W x x b b).1
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ((GlobalTheory.UU.image_one_mul_inv V A G s t a W _ x _ b).2 ih h).1

theorem correct {t : Tower s} {a : t.Alg} {W : Type} [CommRing W] [IsLocalRing W] [Algebra V W]
    (hc : IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W) (hl : IsLocalHom (algebraMap V W))
    {x : PT V W ⟶ G} {b : PT V W ⟶ a.B} (h : Im t a W x b) (N : ℕ) (d : Multiplicative s.X →* Wˣ)
    (hd : Tp t W (x ^ N) (d ^ N)) : ∃ y : PT V W ⟶ G, y ^ N = 1 ∧ Im t a W y b := by
  obtain ⟨κ, -, hk⟩ := GlobalTheory.UU.exists_formalTorus_points V A G s t W hc hl
  have h1 : x ^ N = κ (d ^ N) := (hk _ _).2 hd
  have h2 : Im t a W (κ d) 1 :=
    (GlobalTheory.UU.image_eq_one_iff_torus_point V A G s t a W hc hl (κ d)).2 ⟨d, (hk _ _).1 rfl⟩
  have h3 : Im t a W (κ d)⁻¹ 1⁻¹ := ((GlobalTheory.UU.image_one_mul_inv V A G s t a W _ _ _ _).2 h2 h2).2
  have h4 : Im t a W (x * (κ d)⁻¹) (b * 1⁻¹) := ((GlobalTheory.UU.image_one_mul_inv V A G s t a W _ _ _ _).2 h h3).1
  rw [inv_one, _root_.mul_one] at h4
  refine ⟨_, ?_, h4⟩
  rw [mul_pow, h1, inv_pow, map_pow, mul_inv_cancel]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (t : Tower s) (a : t.Alg) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F]
    [Algebra.IsAlgebraic (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (N : ℕ) (hN : 1 ≤ N)
    (hfin : Finite {x : TF (R := V) F ⟶ a.B // x ^ N = 1}) :
    ∃ (W : Subalgebra V F) (_ : IsLocalRing W),
      IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧ IsLocalHom (algebraMap V W) ∧
      (∀ z : F, z ^ N = 1 → z ∈ W) ∧ ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 →
        ∃ (y : PT V W ⟶ G) (b : PT V W ⟶ a.B), y ^ N = 1 ∧ Im t a W y b ∧
          Spec.map (CommRingCat.ofHom W.val.toRingHom) ≫ b.left = x.left := by
  obtain ⟨h1, h2, h3⟩ := s.cdvr
  have hfs : FaithfulSMul V F := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _)
  have halg : Algebra.IsAlgebraic V F := (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V)).2 inferInstance
  have hp := a.isAb.proper
  have hTF : (TF (R := V) F).hom = Spec.map (CommRingCat.ofHom (algebraMap V F)) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨T, hT⟩ := GlobalTheory.exists_finset_points_extend_valuationSubalgebra V F a.B
    (Set.range fun x : {x : TF (R := V) F ⟶ a.B // x ^ N = 1} => x.1.left) (Set.finite_range _)
    (by rintro _ ⟨x, rfl⟩; exact (Over.w x.1).trans hTF)
  obtain ⟨W₁, hW₁, -, hc₁, hf₁, -, hl₁, hfr, -⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra V F T
  have hb : ∀ x : {x : TF (R := V) F ⟶ a.B // x ^ N = 1}, ∃ b : PT V W₁ ⟶ a.B,
      Spec.map (CommRingCat.ofHom W₁.val.toRingHom) ≫ b.left = x.1.left := fun x => by
    obtain ⟨y, hy, hy'⟩ := hT W₁ inferInstance hfr _ ⟨x, rfl⟩
    exact ⟨Over.homMk y hy, hy'⟩
  choose b hb using hb
  let q : TF (R := V) F ⟶ PT V W₁ := Over.homMk (Spec.map (CommRingCat.ofHom W₁.val.toRingHom))
    ((Over.w (ptMap W₁.val)).trans hTF.symm)
  have hbN : ∀ x, b x ^ N = 1 := fun x => by
    have hq : q ≫ b x = x.1 := Over.OverMorphism.ext (hb x)
    refine GlobalTheory.over_points_ext_of_injective _ a.B W₁ F W₁.val.toRingHom Subtype.val_injective _ _ _ ?_
    have : q ≫ (b x ^ N) = q ≫ 1 := by rw [MonObj.comp_pow, MonObj.comp_one, hq, x.2]
    exact congrArg (·.left) this
  have hy : ∀ x, ∃ y : PT V W₁ ⟶ G, Im t a W₁ y (b x) := fun x =>
    GlobalTheory.AbelianPartLift.main V A G s t a W₁ hc₁ hl₁ (b x)
  choose y hy using hy
  have hc : ∀ x, ∃ c, Tp t W₁ (y x ^ N) c := fun x =>
    (GlobalTheory.UU.image_eq_one_iff_torus_point V A G s t a W₁ hc₁ hl₁ _).1 (by
      have := (hy x).pow N
      rw [hbN] at this
      exact this)
  choose c hc using hc
  obtain ⟨W, hW, hle, hcW, hlW, hz, hd⟩ := exists_big V F W₁ N hN c
  refine ⟨W, hW, hcW, hlW, hz, fun x hx => ?_⟩
  obtain ⟨d, hd⟩ := hd ⟨x, hx⟩
  have h5 := (hc ⟨x, hx⟩).pull (Subalgebra.inclusion hle)
  rw [← hd, MonObj.comp_pow] at h5
  obtain ⟨y', hy1, hy2⟩ := correct hcW hlW ((hy ⟨x, hx⟩).pull (Subalgebra.inclusion hle)) N d h5
  refine ⟨y', _, hy1, hy2, ?_⟩
  rw [← hb ⟨x, hx⟩]
  change Spec.map _ ≫ Spec.map _ ≫ _ = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem torsion_lift : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (N : ℕ), 1 ≤ N → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : W →+* F), Function.Injective φ ∧ φ.comp (algebraMap V W) = (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)) ∧ IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧ IsLocalHom (algebraMap V W) ∧ (∀ z : F, z ^ N = 1 → z ∈ φ.range) ∧ ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → ∃ (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), y ^ N = 1 ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (y).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) ∧ (Spec.map (CommRingCat.ofHom φ)) ≫ b.left = x.left := by
  intro hcard V _ _ _ A G _ _ s t a F _ _ _ _ N hN
  letI : Algebra V F := ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) F := IsScalarTower.of_algebraMap_eq' rfl
  have hch : CharZero V := s.cdvr.2.2
  haveI : CharZero F := charZero_of_injective_ringHom (f := algebraMap V F)
    ((algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim V a.B a.isAb
  have hn := GlobalTheory.card_torsion_geometricPoint_of_field hcard _ a.B a.isAb g hg F (TF (R := V) F).hom N
    (Nat.cast_ne_zero.2 (by omega))
  have hfin : Finite {x : TF (R := V) F ⟶ a.B // x ^ N = 1} :=
    Nat.finite_of_card_ne_zero (hn.trans_ne (pow_ne_zero _ (by omega)))
  obtain ⟨W, hW, h1, h2, h3, h4⟩ := finiteRing_sq_sub_mul_sq_eq_of_card t a F N hN hfin
  exact ⟨W, inferInstance, hW, inferInstance, W.val.toRingHom, Subtype.val_injective, rfl, h1, h2,
    fun z hz => ⟨⟨z, h3 z hz⟩, rfl⟩, h4⟩

end GlobalTheory.TorsionLift
end
