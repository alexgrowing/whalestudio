import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace TorusToProper

variable {K : Type} [Field K]

noncomputable abbrev sp (K : Type) [Field K] (R : Type) [CommRing R] [Algebra K R] :
    Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R)))

noncomputable def spm {R R' : Type} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
    (g : R →ₐ[K] R') : sp K R' ⟶ sp K R :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp)

lemma spm_comp {R R' R'' : Type} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
    [CommRing R''] [Algebra K R''] (g : R →ₐ[K] R') (h : R' →ₐ[K] R'') :
    spm h ≫ spm g = spm (h.comp g) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

lemma spm_id {R : Type} [CommRing R] [Algebra K R] : spm (AlgHom.id K R) = 𝟙 _ := by
  ext1
  exact Spec.map_id _

lemma point_ext {V F : Type} [CommRing V] [IsDomain V] [Algebra K V] [CommRing F] [Algebra K F]
    (j : V →ₐ[K] F) (hj : Function.Injective j)
    {B : Over (Spec (CommRingCat.of K))} [IsSeparated B.hom] {b b' : sp K V ⟶ B}
    (h : spm j ≫ b = spm j ≫ b') : b = b' := by
  ext1
  have hd : IsDominant (Spec.map (CommRingCat.ofHom j.toRingHom)) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j.toRingHom).2
      (by rw [(RingHom.injective_iff_ker_eq_bot j.toRingHom).1 hj]; exact bot_le)
  have : IsReduced (sp K V).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of V)))
  exact ext_of_isDominant_of_isSeparated B.hom ((Over.w b).trans (Over.w b').symm)
    (Spec.map (CommRingCat.ofHom j.toRingHom)) (congrArg CommaMorphism.left h)

lemma point_extend {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Algebra K V] [Field F]
    [Algebra K F] [Algebra V F] [IsScalarTower K V F] [IsFractionRing V F]
    {B : Over (Spec (CommRingCat.of K))} [IsProper B.hom] (p : sp K F ⟶ B) :
    ∃ b : sp K V ⟶ B, spm (IsScalarTower.toAlgHom K V F) ≫ b = p := by
  have hE : ValuativeCriterion.Existence B.hom := by
    have h : UniversallyClosed B.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq B.hom :=
    { R := V, K := F, i₁ := p.left, i₂ := Spec.map (CommRingCat.ofHom (algebraMap K V)),
      commSq := ⟨(Over.w p).trans (Over.w (spm (IsScalarTower.toAlgHom K V F))).symm⟩ }
  obtain ⟨⟨l, h1, h2⟩⟩ := hE S
  exact ⟨Over.homMk l h2, by ext1; exact h1⟩

open PowerSeries in

lemma units_family_trivial {B : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsProper B.hom]
    (Φ : ∀ (R : Type) [CommRing R] [Algebra K R], Rˣ →* (sp K R ⟶ B))
    (hΦ : ∀ (R R' : Type) [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R'] (g : R →ₐ[K] R')
      (x : Rˣ), Φ R' (Units.map (g : R →* R') x) = spm g ≫ Φ R x)
    (L : Type) [Field L] [Algebra K L] (x : Lˣ) : Φ L x = 1 := by
  let F := FractionRing L⟦X⟧
  let j : L⟦X⟧ →ₐ[K] F := IsScalarTower.toAlgHom K L⟦X⟧ F
  have hj : Function.Injective j := IsFractionRing.injective L⟦X⟧ F
  let σ : L⟦X⟧ →ₐ[K] L⟦X⟧ := (rescaleAlgHom (x : L)).restrictScalars K
  have hσ : ∀ a, σ a = rescale (x : L) a := fun a =>
    RingHom.congr_fun (coe_rescaleAlgHom (x : L)) a
  have hσi : Function.Injective (j.comp σ) := by
    intro a b hab
    have h1 : σ a = σ b := hj hab
    rw [hσ, hσ] at h1
    exact rescale_injective x.ne_zero h1
  let τ : F →ₐ[K] F := IsFractionRing.liftAlgHom (g := j.comp σ) hσi
  have hτ : τ.comp j = j.comp σ := by
    ext a
    simp [τ, j]
  let c : L →ₐ[K] L⟦X⟧ := IsScalarTower.toAlgHom K L L⟦X⟧
  let ev : L⟦X⟧ →ₐ[K] L := { toRingHom := constantCoeff, commutes' := fun r => by simp [PowerSeries.algebraMap_apply] }
  have hev : ∀ a, ev a = constantCoeff a := fun _ => rfl
  have h1 : ev.comp σ = ev := by
    ext a
    rw [AlgHom.comp_apply, hσ, hev, hev, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
    simp
  have h2 : ev.comp c = AlgHom.id K L := by
    ext a
    simp [hev, c, PowerSeries.algebraMap_apply]
  have hX : j X ≠ 0 := fun h => X_ne_zero (hj (h.trans (map_zero j).symm))
  let u : Fˣ := Units.mk0 (j X) hX
  obtain ⟨b, hb⟩ := point_extend (K := K) (V := L⟦X⟧) (Φ F u)
  have hu : Units.map (τ : F →* F) u = Units.map ((j.comp c : L →ₐ[K] F) : L →* F) x * u := by
    ext
    have := congrArg (fun g : L⟦X⟧ →ₐ[K] F => g X) hτ
    simp only [AlgHom.comp_apply, hσ, rescale_X, map_mul] at this
    simpa [u, c, PowerSeries.algebraMap_apply] using this
  have key : spm σ ≫ b = (spm c ≫ Φ L x) * b := by
    apply point_ext j hj
    rw [← Category.assoc, spm_comp, ← hτ, ← spm_comp, Category.assoc, MonObj.comp_mul, hb, ← hΦ, hu,
      map_mul, hΦ, ← Category.assoc, spm_comp]
  have k2 := congrArg (fun t => spm ev ≫ t) key
  simp only [MonObj.comp_mul, ← Category.assoc, spm_comp, h1, h2, spm_id, Category.id_comp] at k2
  exact right_eq_mul.1 k2

lemma mul_left_fst {S S' A : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {a : A ⟶ S'} {c : A ⟶ S}
    (x y : Over.mk a ⟶ (Over.pullback f).obj G) (x₀ y₀ : Over.mk c ⟶ G)
    (hx : x₀.left = x.left ≫ pullback.fst G.hom f) (hy : y₀.left = y.left ≫ pullback.fst G.hom f) :
    (x * y).left ≫ pullback.fst G.hom f = (x₀ * y₀).left := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  let z : Over.mk a ⟶ (Over.pullback f).obj (G ⊗ G) :=
    lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G
  have z₁ : z ≫ (Over.pullback f).map (fst G G) = x := by simp [z]
  have z₂ : z ≫ (Over.pullback f).map (snd G G) = y := by simp [z]
  have hz : (lift x₀ y₀).left = z.left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · show (lift x₀ y₀ ≫ fst G G).left = _ ≫ (fst G G).left
      rw [lift_fst, hx, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₁]
    · show (lift x₀ y₀ ≫ snd G G).left = _ ≫ (snd G G).left
      rw [lift_snd, hy, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₂]
  have hxy : x * y = z ≫ (Over.pullback f).map μ[G] := by
    rw [Hom.mul_def, Functor.obj.μ_def, ← Category.assoc]
  rw [hxy, Over.comp_left, Category.assoc, A, ← Category.assoc, ← hz]
  rfl

variable (K) (X : Type) [AddCommGroup X]

noncomputable def charAlg (R : Type) [CommRing R] (φ : Multiplicative X →* Rˣ) :
    letI : Algebra (ULift.{0} ℤ) R := ULift.algebra' ℤ R
    AddMonoidAlgebra (ULift.{0} ℤ) X →ₐ[ULift.{0} ℤ] R :=
  letI : Algebra (ULift.{0} ℤ) R := ULift.algebra' ℤ R
  AddMonoidAlgebra.lift (ULift.{0} ℤ) R X ((Units.coeHom R).comp φ)

noncomputable def charRing (R : Type) [CommRing R] (φ : Multiplicative X →* Rˣ) :
    AddMonoidAlgebra (ULift.{0} ℤ) X →+* R :=
  letI : Algebra (ULift.{0} ℤ) R := ULift.algebra' ℤ R
  (charAlg X R φ).toRingHom

lemma charRing_single (R : Type) [CommRing R] (φ : Multiplicative X →* Rˣ) (a : X) :
    charRing X R φ (AddMonoidAlgebra.single a 1) = φ (Multiplicative.ofAdd a) := by
  simp [charRing, charAlg]

noncomputable def ptFun (R : Type) [CommRing R] [Algebra K R] (φ : Multiplicative X →* Rˣ) :
    sp K R ⟶ splitTorus (Spec (CommRingCat.of K)) X :=
  Over.homMk (pullback.lift (Spec.map (CommRingCat.ofHom (charRing X R φ)) :
    _ ⟶ (splitTorusAff ZU X).left) (sp K R).hom (specULiftZIsTerminal.hom_ext _ _))
    (pullback.lift_snd _ _ _)

lemma ptFun_fst (R : Type) [CommRing R] [Algebra K R] (φ : Multiplicative X →* Rˣ) :
    (ptFun K X R φ).left ≫ Rosenlicht.torusFst _ X = Spec.map (CommRingCat.ofHom (charRing X R φ)) :=
  pullback.lift_fst _ _ _

variable {K X} in
lemma torus_ext {Z : Over (Spec (CommRingCat.of K))} {t t' : Z ⟶ splitTorus (Spec (CommRingCat.of K)) X}
    (h : t.left ≫ Rosenlicht.torusFst _ X = t'.left ≫ Rosenlicht.torusFst _ X) : t = t' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact (Over.w t).trans (Over.w t').symm

lemma ptFun_mul (R : Type) [CommRing R] [Algebra K R] (φ ψ : Multiplicative X →* Rˣ) :
    ptFun K X R (φ * ψ) = ptFun K X R φ * ptFun K X R ψ := by
  letI : Algebra (ULift.{0} ℤ) R := ULift.algebra' ℤ R
  apply torus_ext
  have h := mul_left_fst (toZ (Spec (CommRingCat.of K))) (splitTorusAff ZU X)
    (ptFun K X R φ) (ptFun K X R ψ)
    (Spec.mapMulEquiv (WithConv.toConv (charAlg X R φ)))
    (Spec.mapMulEquiv (WithConv.toConv (charAlg X R ψ)))
    (ptFun_fst K X R φ).symm (ptFun_fst K X R ψ).symm
  have h2 : WithConv.toConv (charAlg X R φ) * WithConv.toConv (charAlg X R ψ) =
      WithConv.toConv (charAlg X R (φ * ψ)) := by
    apply WithConv.ofConv_injective
    apply AddMonoidAlgebra.algHom_ext
    · intro a
      simp [AlgHom.convMul_apply, charAlg]
    · exact Subsingleton.elim _ _
  have h3 := (Spec.mapMulEquiv (R := ULift.{0} ℤ) (S := AddMonoidAlgebra (ULift.{0} ℤ) X) (T := R)).map_mul
    (WithConv.toConv (charAlg X R φ)) (WithConv.toConv (charAlg X R ψ))
  rw [h2] at h3
  rw [ptFun_fst]
  exact (congrArg CommaMorphism.left h3).trans h.symm

noncomputable def pt (R : Type) [CommRing R] [Algebra K R] :
    (Multiplicative X →* Rˣ) →* (sp K R ⟶ splitTorus (Spec (CommRingCat.of K)) X) :=
  MonoidHom.mk' (ptFun K X R) (ptFun_mul K X R)

lemma pt_nat {R R' : Type} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R'] (g : R →ₐ[K] R')
    (φ : Multiplicative X →* Rˣ) :
    pt K X R' ((Units.map (g : R →* R')).comp φ) = spm g ≫ pt K X R φ := by
  apply torus_ext
  change (ptFun K X R' _).left ≫ _ = (Spec.map _ ≫ (ptFun K X R φ).left) ≫ _
  rw [Category.assoc, ptFun_fst, ptFun_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply Rosenlicht.ringHom_ext_ZU
  intro y
  simp [charRing_single]

noncomputable def univ : Multiplicative X →* (AddMonoidAlgebra K X)ˣ :=
  (AddMonoidAlgebra.of K X).toHomUnits

lemma pt_univ : (pt K X _ (univ K X)).left = (Rosenlicht.torusIso K X).hom := by
  apply pullback.hom_ext
  · refine (ptFun_fst K X _ _).trans (Eq.trans ?_ (Rosenlicht.torusIso_hom_fst K X).symm)
    congr 2
    apply Rosenlicht.ringHom_ext_ZU
    intro y
    rw [charRing_single]
    simp [univ]
  · exact (Over.w (pt K X _ (univ K X))).trans (Rosenlicht.torusIso_hom_hom K X).symm

variable {X} in

def coch (l : X →+ ℤ) (G : Type) [CommGroup G] : G →* (Multiplicative X →* G) where
  toFun x :=
    { toFun := fun a => x ^ l a.toAdd
      map_one' := by simp
      map_mul' := fun a b => by simp [zpow_add] }
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_zpow]

lemma char_eq_prod {I : Type} [Fintype I] (e : Module.Basis I ℤ X) (G : Type) [CommGroup G]
    (φ : Multiplicative X →* G) :
    φ = ∏ i, coch (e.coord i).toAddMonoidHom G (φ (Multiplicative.ofAdd (e i))) := by
  refine MonoidHom.ext fun a => ?_
  rw [MonoidHom.finset_prod_apply]
  conv_lhs => rw [← ofAdd_toAdd a, ← e.sum_repr a.toAdd, ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  rfl

end TorusToProper

open TorusToProper in

theorem splitTorus_hom_proper_trivial_field (K : Type) [Field K] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Spec (CommRingCat.of K))) [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of K)) X ⟶ B) (hf : IsMonHom f) :
    f = toUnit _ ≫ η[B] := by
  let Ψ : ∀ (R : Type) [CommRing R] [Algebra K R], (Multiplicative X →* Rˣ) →* (sp K R ⟶ B) :=
    fun R _ _ => (MonoidHom.mk' (fun t => t ≫ f) (fun s t => MonObj.mul_comp s t f)).comp (pt K X R)
  have hΨ : ∀ (R : Type) [CommRing R] [Algebra K R] φ, Ψ R φ = pt K X R φ ≫ f := fun _ _ _ _ => rfl
  have h1 : ∀ (l : X →+ ℤ) (L : Type) [Field L] [Algebra K L] (x : Lˣ), Ψ L (coch l Lˣ x) = 1 := by
    intro l L _ _ x
    refine units_family_trivial (fun R _ _ => (Ψ R).comp (coch l Rˣ)) ?_ L x
    intro R R' _ _ _ _ g y
    simp only [MonoidHom.comp_apply, hΨ]
    rw [← Category.assoc, ← pt_nat]
    congr 2
    refine MonoidHom.ext fun a => ?_
    exact (map_zpow (Units.map (g : R →* R')) y _).symm
  have h2 : ∀ (L : Type) [Field L] [Algebra K L] φ, Ψ L φ = 1 := by
    intro L _ _ φ
    rw [char_eq_prod X (Module.Free.chooseBasis ℤ X) _ φ, ← MonoidHom.mem_ker]
    exact Subgroup.prod_mem _ fun i _ => h1 _ L _
  have : IsDomain (AddMonoidAlgebra K X) := NoZeroDivisors.to_isDomain _
  let R := AddMonoidAlgebra K X
  let F := FractionRing R
  have h3 : pt K X R (univ K X) ≫ f = pt K X R (univ K X) ≫ toUnit _ ≫ η[B] := by
    apply point_ext (IsScalarTower.toAlgHom K R F) (IsFractionRing.injective R F)
    rw [← Category.assoc, ← pt_nat, ← hΨ, h2, ← Category.assoc, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have h4 : (pt K X R (univ K X)).left ≫ f.left =
      (pt K X R (univ K X)).left ≫ (toUnit _ ≫ η[B]).left := congrArg CommaMorphism.left h3
  rw [pt_univ] at h4
  ext1
  exact (cancel_epi _).1 h4

end GlobalTheory
