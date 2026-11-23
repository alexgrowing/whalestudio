import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPolAVFiniteTypeSubring
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsRelAcyclicPolAVBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SpreadPolAV

theorem exists_spread : ∀ (F Ω : Type) [Field F] [Field Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (I : Type) [Finite I] (y : I → (baseOver (Sp Ω) ⟶ A.A)), ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : Algebra F T) (jT : T →+* Ω) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left) (y₀ : I → (baseOver (Sp T) ⟶ P.A)), Algebra.FiniteType F T ∧ Function.Injective jT ∧ jT.comp (algebraMap F T) = em ∧ IsGrpPullback A.A P.A (spMap jT) φ ∧ LBIso A.L (P.L.pull φ) ∧ ∀ i, (y i).left ≫ φ = spMap jT ≫ (y₀ i).left := by
  classical
  intro F Ω _ _ em A I _ y
  obtain ⟨R, P₀, φ₀, ftR, -, H₀, iso₀⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring Ω A
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have := P₀.smoothDim
  have : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g _
  have : LocallyOfFinitePresentation P₀.A.hom := inferInstance

  have hx : ∀ i, ((y i).left ≫ φ₀) ≫ P₀.A.hom = spMap (algebraMap R Ω) := by
    intro i
    rw [Category.assoc, H₀.1.w, ← Category.assoc, Over.w (y i)]
    exact Category.id_comp _
  obtain ⟨R', y', hR', -, hy'⟩ :=
    GlobalTheory.Spread.exists_fg_points P₀.A.hom (fun i => (y i).left ≫ φ₀) hx ⊥ Subalgebra.fg_bot
  have ftR' : Algebra.FiniteType ℤ R' :=
    Algebra.FiniteType.trans ftR ((Subalgebra.fg_iff_finiteType R').1 hR')
  obtain ⟨s₀, hs₀⟩ := ftR'.out

  letI : Algebra F Ω := em.toAlgebra
  let f₀ : R' →ₐ[ℤ] Ω := R'.val.restrictScalars ℤ
  let T : Subalgebra F Ω := Algebra.adjoin F (f₀ '' (s₀ : Set R'))
  have hTfg : T.FG := ⟨s₀.image f₀, by rw [Finset.coe_image]⟩
  have hR'T : ∀ z ∈ R', z ∈ T := by
    intro z hz
    have h₁ : (⟨z, hz⟩ : R') ∈ Algebra.adjoin ℤ (s₀ : Set R') := by rw [hs₀]; trivial
    have h₂ : f₀ ⟨z, hz⟩ ∈ Algebra.adjoin ℤ (f₀ '' (s₀ : Set R')) := by
      rw [← AlgHom.map_adjoin]
      exact Subalgebra.mem_map.2 ⟨_, h₁, rfl⟩
    have key : Algebra.adjoin ℤ (f₀ '' (s₀ : Set R')) ≤ T.restrictScalars ℤ :=
      Algebra.adjoin_le (Algebra.subset_adjoin (R := F))
    exact key h₂
  have hRT : ∀ r ∈ R, r ∈ T := fun r hr => hR'T r (R'.algebraMap_mem (⟨r, hr⟩ : R))
  let g : R →+* T := R.subtype.codRestrict T fun r => hRT r r.2
  let incl : R' →+* T := R'.val.toRingHom.codRestrict T fun z => hR'T z z.2
  let jT : T →+* Ω := T.val.toRingHom
  have e₁ : spMap jT ≫ spMap g = spMap R.subtype := by
    rw [← Spec.map_comp]; rfl
  have e₂ : spMap jT ≫ spMap incl = spMap R'.val.toRingHom := by
    rw [← Spec.map_comp]; rfl
  have e₃ : spMap incl ≫ spMap (algebraMap R R') = spMap g := by
    rw [← Spec.map_comp]; rfl

  let P : PolAV (Sp T) := GlobalTheory.AmpleSymModel.polPull P₀ (spMap g)
  have Gp : IsGrpPullback P.A P₀.A (spMap g) (pullback.fst P₀.A.hom (spMap g)) :=
    isGrpPullback_pullback P₀.A (spMap g)
  have w : φ₀ ≫ P₀.A.hom = (A.A.hom ≫ spMap jT) ≫ spMap g := by
    rw [Category.assoc, e₁]; exact H₀.1.w
  let φ : A.A.left ⟶ P.A.left := Gp.1.lift _ _ w
  have hφ : φ ≫ pullback.fst P₀.A.hom (spMap g) = φ₀ := Gp.1.lift_fst _ _ w
  have hφ' : φ ≫ P.A.hom = A.A.hom ≫ spMap jT := Gp.1.lift_snd _ _ w
  have hu : ∀ i, (spMap incl ≫ y' i) ≫ P₀.A.hom = 𝟙 (Sp T) ≫ spMap g := by
    intro i
    rw [Category.assoc, (hy' i).1, e₃, Category.id_comp]
  let y₀ : I → (baseOver (Sp T) ⟶ P.A) := fun i =>
    Over.homMk (Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i)) (Gp.1.lift_snd _ _ (hu i))
  refine ⟨T, inferInstance, inferInstance, inferInstance, jT, P, φ, y₀,
    (Subalgebra.fg_iff_finiteType T).1 hTfg, Subtype.val_injective, RingHom.ext fun _ => rfl,
    Gp.cancel (H₀.congr e₁.symm hφ.symm) hφ',
    GlobalTheory.KeyTf.lbIso_pull_pull_of_comp A.isLB P₀.isLB hφ iso₀, fun i => ?_⟩
  apply Gp.1.hom_ext
  · change (y i).left ≫ φ ≫ pullback.fst P₀.A.hom (spMap g) =
      spMap jT ≫ Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i) ≫ pullback.fst P₀.A.hom (spMap g)
    rw [hφ, Gp.1.lift_fst, ← Category.assoc, e₂, (hy' i).2]
  · change (y i).left ≫ φ ≫ P.A.hom = spMap jT ≫ Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i) ≫ P.A.hom
    rw [hφ', Gp.1.lift_snd, ← Category.assoc, Over.w (y i)]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.SpreadPolAV
