import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntermediateFieldOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOfGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfPowEqOneOfLocalHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.PrincipalModel
open GlobalTheory.UU GlobalTheory.AbLaw

theorem exists_common_overfield {k A B : Type} [Field k] [Field A] [Field B] (f : k →+* A) (g : k →+* B) :
    ∃ (L : Type) (_ : Field L) (a : A →+* L) (b : B →+* L), a.comp f = b.comp g := by
  let _ := f.toAlgebra
  let _ := g.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct k A B)
  refine ⟨TensorProduct k A B ⧸ m, Ideal.Quotient.field m,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom),
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)).toRingHom, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  exact congrArg _ (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := k) (A := A) (B := B))

theorem exists_valuationSubring {W F Ω : Type} [CommRing W] [IsLocalRing W] [Field F] [Field Ω] (φ : W →+* F)
    (f : W →+* Ω) [IsLocalHom f] : ∃ (O : ValuationSubring F) (j : W →+* O) (L : Type) (_ : Field L) (a : Ω →+* L)
      (g : O →+* L), (algebraMap O F).comp j = φ ∧ IsLocalHom g ∧ a.comp f = g.comp j := by
  obtain ⟨O, h, hl⟩ := IsLocalRing.exists_factor_valuationRing φ
  let j : W →+* O := φ.codRestrict O.toSubring h
  have : IsLocalHom j := hl
  obtain ⟨L, _, a, b, e⟩ := exists_common_overfield (IsLocalRing.ResidueField.lift f) (IsLocalRing.ResidueField.map j)
  refine ⟨O, j, L, inferInstance, a, b.comp (IsLocalRing.residue O), rfl, inferInstance, ?_⟩
  rw [← IsLocalRing.ResidueField.lift_comp_residue f, ← RingHom.comp_assoc, e, RingHom.comp_assoc,
    IsLocalRing.ResidueField.map_comp_residue, RingHom.comp_assoc]

theorem exists_embedding (V K W : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    [CommRing W] [IsDomain W] [Algebra V W] [Module.Finite V W] (h : Function.Injective (algebraMap V W)) :
    ∃ φ : W →+* AlgebraicClosure K, Function.Injective φ ∧ φ.comp (algebraMap V W) =
      (algebraMap K (AlgebraicClosure K)).comp (algebraMap V K) := by
  have i : Function.Injective (algebraMap V (AlgebraicClosure K)) := by
    rw [IsScalarTower.algebraMap_eq V K]
    exact (algebraMap K _).injective.comp (IsFractionRing.injective V K)
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 h
  have : FaithfulSMul V (AlgebraicClosure K) := (faithfulSMul_iff_algebraMap_injective _ _).2 i
  let φ : W →ₐ[V] AlgebraicClosure K := IsAlgClosed.lift
  refine ⟨φ.toRingHom, ?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    rw [RingHom.comap_ker, show φ.toRingHom.comp (algebraMap V W) = algebraMap V _ from φ.comp_algebraMap]
    exact (RingHom.injective_iff_ker_eq_bot _).1 i
  · rw [← IsScalarTower.algebraMap_eq]; exact φ.comp_algebraMap

theorem triv_comp {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} (x : T ⟶ A) (g : T' ⟶ T)
    (h : Triv (translDiff A L x)) : Triv (translDiff A L (g ≫ x)) := by
  obtain ⟨d, hd⟩ := h
  have h4 : ∃ w : LB.Gen (LB.LinComb L _ _), w.IsGen := ⟨_, DVR.pullGen_isGen _ _ _ d hd (g ▷ A).left⟩
  have h3 : (fun k : Fin 2 => (g ▷ A).left ≫ ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] k) =
      ![(lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] := by
    funext k
    fin_cases k
    · change (g ▷ A ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left =
        (lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    · change (g ▷ A ≫ snd T A).left = (snd T' A).left
      rw [whiskerRight_snd]
  rw [h3] at h4
  exact h4

theorem cubWeil_generic (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : RigLB A} (c : CubicalStr A L) {O F k : Type} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F] [Field k] (g : O →+* k) [IsLocalHom g]
    {p : Sp O ⟶ S} {n : ℕ} (hn : IsUnit (n : O)) (X : Over.mk p ⟶ A) (hX : X ^ n = 1)
    {pk : Sp k ⟶ S} (ρk : Over.mk pk ⟶ Over.mk p) (hk : ρk.left = spMap g)
    {pF : Sp F ⟶ S} (ρF : Over.mk pF ⟶ Over.mk p) (hF : ρF.left = spMap (algebraMap O F))
    (ht : Triv (translDiff A L.L (ρk ≫ X))) (y : Over.mk pF ⟶ A) (hy : y ^ n = 1) :
    CubWeil c n (ρF ≫ X) y 1 := by
  have := hA.proper
  have hE : ValuativeCriterion.Existence A.hom := by
    have h : UniversallyClosed A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have w : y.left ≫ A.hom = spMap (algebraMap O F) ≫ p := (Over.w y).trans ((Over.w ρF).symm.trans (by rw [hF]; rfl))
  obtain ⟨l, hl₁, hl₂⟩ := (hE { R := O, K := F, commSq := ⟨w⟩, .. }).exists_lift
  let Y : Over.mk p ⟶ A := Over.homMk l hl₂
  have hYy : ρF ≫ Y = y := Over.OverMorphism.ext ((congrArg (· ≫ l) hF).trans hl₁)
  have hY : Y ^ n = 1 := by
    refine over_points_ext_of_injective S A O F _ (IsFractionRing.injective O F) p _ _ ?_
    have e : ρF ≫ Y ^ n = ρF ≫ 1 := by rw [MonObj.comp_pow, hYy, hy, MonObj.comp_one]
    have e' : ρF.left ≫ (Y ^ n).left = ρF.left ≫ (1 : Over.mk p ⟶ A).left := congrArg (fun q => q.left) e
    rw [hF] at e'
    exact e'
  obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil c hX hY
  have h₁ := hζ.comp ρk
  have h₂ := KerPair.cubWeil_of_gen hG S A hA L c n _ _ _ h₁.1 h₁.2.1 ht
  have h₃ := h₁.unique h₂
  rw [hk] at h₃
  have h₄ : ζ = 1 := unit_eq_one_of_localHom g hn hζ.pow_eq_one h₃
  have h₅ := hζ.comp ρF
  rwa [h₄, map_one, hYy] at h₅

theorem nondeg_of_isGrpPullback {S S' : Scheme.{0}} {A : Over S'} [GrpObj A] {B : Over S} [GrpObj B] [IsCommMonObj B]
    {L' : LB A.left} {L : LB B.left} (hL' : L'.IsLB) (hL : L.IsLB) {f : S' ⟶ S} {φ : A.left ⟶ B.left}
    (hp : IsGrpPullback A B f φ) (hi : LBIso L' (L.pull φ)) (T : Over S') (n : ℕ)
    (H : ∀ u : T ⟶ A, u ^ n = 1 → (∀ z : T ⟶ A, z ^ n = 1 → WeilIs A L' n u z 1) → u = 1)
    (x : Over.mk (T.hom ≫ f) ⟶ B) (hx : x ^ n = 1)
    (h : ∀ y : Over.mk (T.hom ≫ f) ⟶ B, y ^ n = 1 → WeilIs B L n x y 1) : x = 1 := by
  let β := pushHom hp T
  have inj : Function.Injective β := fun a b e =>
    Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))
  let u : T ⟶ A := Over.homMk (hp.1.lift x.left T.hom (Over.w x)) (hp.1.lift_snd _ _ _)
  have hu : β u = x := Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  have hun : u ^ n = 1 := inj (by rw [map_pow, hu, map_one]; exact hx)
  have : u = 1 := H u hun fun z hz =>
    (weilIs_grpPullback_of_comm _ _ B A f φ L L' hL hL' hp hi T n u z x (β z) 1
      (congrArg (fun q => q.left) hu.symm) rfl).2 (h _ (by rw [← map_pow, hz, map_one]))
  rw [← hu, this, map_one]

theorem eq_one_of_cubWeil (hL : Laws) {S S' : Scheme.{0}} (P : PolAV S') {B : Over S} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {L : RigLB B} (c : CubicalStr B L) {f : S' ⟶ S} {φ : P.A.left ⟶ B.left}
    (hp : IsGrpPullback P.A B f φ) (hi : LBIso P.L (L.L.pull φ)) {F : Type} [Field F] [IsAlgClosed F]
    (t : Sp F ⟶ S') {n : ℕ} (hn : (n : F) ≠ 0) (x : Over.mk (t ≫ f) ⟶ B) (hx : x ^ n = 1)
    (h : ∀ y : Over.mk (t ≫ f) ⟶ B, y ^ n = 1 → CubWeil c n x y 1) : x = 1 := by
  obtain ⟨P', g, hg, -, hmul, tw, htw⟩ := hL.polBaseChange S' _ t P
  have hp' : IsGrpPullback P'.A P.A t g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [show x₀ = toBase hg.w x from Over.OverMorphism.ext hx,
      show y₀ = toBase hg.w y from Over.OverMorphism.ext hy, ← hmul]
    rfl⟩
  have := P.isAb.comm
  have H := nondeg_of_isGrpPullback P'.isLB P.isLB hp' (LBIso.symm ⟨tw, htw⟩) (baseOver _) n
    (hL.weilNondeg F P' n hn)
  have e : (baseOver (Sp F)).hom ≫ t = t := Category.id_comp t
  rw [e] at H
  exact nondeg_of_isGrpPullback P.isLB L.isLB hp hi (Over.mk t) n H x hx fun y hy =>
    (cubWeil_iff_weilIs hL.globalFns hB hx hy 1).1 (h y hy)

theorem torsion_eq_one_of_triv : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : V →+* Ω), IsLocalHom f → ∀ n : ℕ, (n : Ω) ≠ 0 → ∀ x : Over.mk (spMap f) ⟶ B, x ^ n = 1 → GlobalTheory.AbLaw.Triv (translDiff B M.L.L x) → x = 1 := by
  intro hL _ V K _ _ _ _ _ _ P B _ _ M φ hB hp hi _ Ω _ _ f hf n hn x hx ht
  have := hB.smooth
  have := hB.proper
  have hnV : IsUnit (n : V) := isUnit_of_map_unit f _ (by rw [map_natCast]; exact hn.isUnit)
  obtain ⟨W, _, _, _, _, _, f', _, inj, _, _, hf', lifts⟩ := GlobalTheory.exists_finite_extension_torsion_lift hL.unramExt V B n
    hnV Ω f hf {x} (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hx)
  obtain ⟨X, hX, hXx⟩ := lifts x (Finset.mem_singleton_self x)
  obtain ⟨ψ, hψ, eψ⟩ := exists_embedding V K W inj
  obtain ⟨O, j, k, _, a, g, hj, _, e⟩ := exists_valuationSubring ψ f'
  have sp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (u : A →+* B) (v : B →+* C),
      spMap (v.comp u) = spMap v ≫ spMap u := fun u v => by
    rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let TW : Over (Sp V) := Over.mk (spMap (algebraMap V W))
  let TO : Over (Sp V) := Over.mk (spMap j ≫ spMap (algebraMap V W))
  let σ : TO ⟶ TW := Over.homMk (spMap j) rfl
  let ρk : Over.mk (spMap a ≫ spMap f) ⟶ TO := Over.homMk (spMap g) (by
    show spMap g ≫ spMap j ≫ spMap (algebraMap V W) = spMap a ≫ spMap f
    rw [← sp, ← sp, ← sp, ← RingHom.comp_assoc, ← e, RingHom.comp_assoc, hf'])
  let ρF : Over.mk (spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap (algebraMap V K)) ⟶ TO :=
    Over.homMk (spMap (algebraMap O (AlgebraicClosure K))) (by
      show spMap (algebraMap O (AlgebraicClosure K)) ≫ spMap j ≫ spMap (algebraMap V W) =
        spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap (algebraMap V K)
      rw [← sp, ← sp, ← sp, ← RingHom.comp_assoc, hj, eψ])
  let τ : Over.mk (spMap a ≫ spMap f) ⟶ Over.mk (spMap f) := Over.homMk (spMap a) rfl
  have hτ : τ ≫ x = ρk ≫ σ ≫ X := Over.OverMorphism.ext (by
    show spMap a ≫ x.left = spMap g ≫ spMap j ≫ X.left
    rw [← hXx, ← Category.assoc, ← Category.assoc, ← sp, ← sp, e])
  have hσ : (σ ≫ X) ^ n = 1 := by rw [← MonObj.comp_pow, hX, MonObj.comp_one]
  have hnO : IsUnit (n : O) := by simpa using hnV.map (j.comp (algebraMap V W))
  have key : ρF ≫ σ ≫ X = 1 := eq_one_of_cubWeil hL P hB M.c hp hi _
    (by simpa using (hnO.map (algebraMap O (AlgebraicClosure K))).ne_zero) _
    (by rw [← MonObj.comp_pow, hσ, MonObj.comp_one])
    (cubWeil_generic hL.globalFns hB M.c g hnO (σ ≫ X) hσ ρk rfl ρF rfl (hτ ▸ triv_comp x τ ht))
  have hX1 : X = 1 := by
    refine over_points_ext_of_injective _ B W _ ψ hψ _ _ _ ?_
    have e₁ : (ρF ≫ σ) ≫ X = (ρF ≫ σ) ≫ 1 := by rw [Category.assoc, key, MonObj.comp_one]
    have e₂ : (spMap (algebraMap O (AlgebraicClosure K)) ≫ spMap j) ≫ X.left =
        (spMap (algebraMap O (AlgebraicClosure K)) ≫ spMap j) ≫ (1 : TW ⟶ B).left := congrArg (fun q => q.left) e₁
    rw [← sp, hj] at e₂
    exact e₂
  let ρ : Over.mk (spMap f) ⟶ TW := Over.homMk (spMap f') (by
    show spMap f' ≫ spMap (algebraMap V W) = spMap f
    rw [← sp, hf'])
  have : x = ρ ≫ X := Over.OverMorphism.ext hXx.symm
  rw [this, hX1]
  exact MonObj.comp_one _

end GlobalTheory.PrincipalModel
end
