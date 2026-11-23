import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPolarization
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsPower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongDvrArcs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFormAlongDvrStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationRefinedFanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizedFanTorsionRankStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedUniformizationStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.ChartExtend

theorem spMap_jK_sq {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {gam : FractionRing R →+* FractionRing R'} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R' _ (g r)) :
    spMap gam ≫ jK R = jK R' ≫ spMap g := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext h)

theorem extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ)
    (φ : InvFun (𝓞 E)) (d k : ℕ) (DX : GlobalTheory.EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs →
    Refines H (min D.p D.q) φs 𝒩 φ → IsPol (comb d (resInt _ φs) 0 φ) k X DX →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (mξ : SABMap t Y.t ξ)
      (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
      IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso →
      ConeO H φ P.D.toPre.X m γ → InCone P.D.toPre γ →
      ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ → ∃ χ : Sp R ⟶ X.X, jK R ≫ χ = y ≫ X.j := by
  intro E _ _ _ H D l Xo c X Y g φs 𝒩 φ d k DX hgq hφs hRef hpol R _ _ _ ξ t mξ P m γ hCN hEt hFU hTor hCone hIn y hy
  have ⟨hN, hIC, _, hC0⟩ := hCN
  have := isProper_toroidalModel_structureMap X
  have : CompactSpace X.X := hpol.2.compactSpace
  have : QuasiSeparatedSpace X.X := quasiSeparatedSpace_of_quasiSeparated X.s

  obtain ⟨u₀, ⟨n₀⟩⟩ := exists_sabPull y X.oF.t
  obtain ⟨aC, -⟩ := GlobalTheory.LevelCover.sab_comp n₀ X.m (e := y ≫ X.j) rfl
  obtain ⟨n₁, -⟩ := GlobalTheory.LevelCover.sab_comp n₀ X.m0.toSABMap rfl
  obtain ⟨n₂, -⟩ := GlobalTheory.LevelCover.sab_cancel Y.m0.toSABMap n₁ y rfl
  obtain ⟨n₃, -⟩ := GlobalTheory.LevelCover.sab_comp n₂ Y.m (e := y ≫ Y.j) rfl
  obtain ⟨aT, -⟩ := GlobalTheory.LevelCover.sab_cancel mξ n₃ (jK R) hy.symm
  have hu₀ : IsProper u₀.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 X.oF.proper
  obtain ⟨e₁, he₁, hx₁⟩ := GlobalTheory.TraitGen.exists_detOm_gen_extAt hu₀ aT aC
  obtain ⟨e₂, he₂, hx₂⟩ := GlobalTheory.TraitGen.extAt_lbPow _ _ _ _ e₁ k he₁ hx₁

  have hZs : y ≫ X.j ≫ X.s = jK R ≫ ξ ≫ Y.s ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    have hY : y ≫ Y.j ≫ Y.s = jK R ≫ ξ ≫ Y.s := by rw [← Category.assoc, hy, Category.assoc]
    rw [Model.j_s] at hY ⊢
    have hY' : y ≫ pullback.snd _ _ = jK R ≫ ξ ≫ Y.s := by
      rw [← hY]; simp [spMap]
    rw [← Category.assoc, hY']
    simp only [Category.assoc]
  have ext : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (ψ : R →+* V)
      (gam : FractionRing R →+* FractionRing V), (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∃ χ : Sp V ⟶ X.X, spMap gam ≫ y ≫ X.j = jK V ≫ χ := fun V _ _ _ hV ψ gam hg => by
    have := hV.1
    obtain ⟨χ, hχ, -⟩ := val_exists X.s (spMap gam ≫ y ≫ X.j) (spMap ψ ≫ ξ ≫ Y.s ≫ spMap (algebraMap (𝓞 c.F) c.F)) (by
      rw [Category.assoc, Category.assoc, hZs, ← Category.assoc (spMap gam), spMap_jK_sq hg, Category.assoc])
    exact ⟨χ, hχ.symm⟩
  have hA : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V), (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ χ : Sp V ⟶ X.X, spMap gam ≫ y ≫ X.j = jK V ≫ χ → ∃ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be ∧
        ∃ n : ℕ, (n : ℝ) = d * (resInt (𝓞 E) φs).evalZ be ∧ idlAlong DX.idealSheaf χ = Ideal.span {ϖ ^ n} := fun V _ _ _ hV ϖ hϖ ψ gam hg χ hχ => by
    obtain ⟨be, hbe, hF⟩ := GlobalTheory.T.exists_level_form_along_dvr E H R t P hCN V hV ϖ hϖ ψ gam hg
    exact ⟨be, hbe, hF, GlobalTheory.T.polarization_refined_fan E H D l Xo c X Y g φs 𝒩 φ d k DX hgq hφs hRef hpol R ξ t mξ P m γ hCN hEt hFU hTor hCone hIn y hy
      V hV ϖ hϖ ψ gam hg χ hχ be hbe hF⟩
  have hC : Module.Projective (𝓞 E) P.D.toPre.X ∧ Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q := GlobalTheory.T.formally_unramified_uniformization E H D l Xo c Y R ξ t mξ P hCN hEt hFU hTor y hy
  have hB : ∃ q : FractionRing R, q ≠ 0 ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V,
      Irreducible ϖ → ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V),
      (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) → ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be →
      ∃ (n : ℤ) (w : Vˣ), (n : ℝ) = d * (resInt (𝓞 E) φs).evalZ be ∧ gam q = algebraMap V _ w * algebraMap V _ ϖ ^ n := GlobalTheory.T.polarized_fan_torsion_rank E H (min D.p D.q) g d φs 𝒩 φ R t P m γ hgq hφs hRef hC.1 hC.2 hCN hCone hIn
  obtain ⟨q, hq0, hq⟩ := hB

  have hval : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V), (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ χ : Sp V ⟶ X.X, spMap gam ≫ y ≫ X.j = jK V ≫ χ → ∃ (n : ℕ) (w : Vˣ), gam q = algebraMap V _ (w * ϖ ^ n) ∧
        idlAlong DX.idealSheaf χ = Ideal.span {ϖ ^ n} := by
    intro V _ _ _ hV ϖ hϖ ψ gam hg χ hχ
    obtain ⟨be, hbe, hF, nA, hnA, hid⟩ := hA V hV ϖ hϖ ψ gam hg χ hχ
    obtain ⟨n, w, hn, hw⟩ := hq V hV ϖ hϖ ψ gam hg be hbe hF
    have e : n = nA := by
      have : (n : ℝ) = (nA : ℝ) := hn.trans hnA.symm
      exact_mod_cast this
    refine ⟨nA, w, ?_, hid⟩
    rw [hw, e, zpow_natCast, map_mul, map_pow]
  obtain ⟨u, hu⟩ := GlobalTheory.ExtLB.exists_eq_of_traits (R := R) q fun V _ _ _ hV ψ gam hg => by
    have := hV.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨χ, hχ⟩ := ext V hV ψ gam hg
    obtain ⟨n, w, hw, -⟩ := hval V hV ϖ hϖ ψ gam hg χ hχ
    exact ⟨_, hw⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hq0 (by rw [← hu, map_zero])
  have hD : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V),
      (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ χ : Sp V ⟶ X.X, spMap gam ≫ (y ≫ X.j) = jK V ≫ χ → idlAlong DX.idealSheaf χ = Ideal.span {ψ u ^ 1} := by
    intro V _ _ _ hV ψ gam hg χ hχ
    have := hV.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨n, w, hw, hid⟩ := hval V hV ϖ hϖ ψ gam hg χ hχ
    have e : ψ u = w * ϖ ^ n := by
      apply IsFractionRing.injective V (FractionRing V)
      rw [← hw, ← hg, hu]
    rw [hid, pow_one, e, Ideal.span_singleton_mul_left_unit w.isUnit]
  obtain ⟨e₃, he₃, hx₃⟩ := GlobalTheory.TraitGen.exists_dual_gen_extAt X.X DX R u hu0 (y ≫ X.j) 1 hD
  obtain ⟨e, he, hx⟩ := GlobalTheory.TraitGen.exists_tens_extAt _ _ _ _ _ e₂ e₃ he₂ he₃ hx₂ hx₃
  refine GlobalTheory.ExtLB.exists_extension X.X (polOf X k DX) hpol.2.isLB (fun z => GlobalTheory.PolFin.exists_H0_of_isAmpleLB hpol.2 z) R
    (y ≫ X.j) e he fun V _ _ _ hV ψ gam hg => ?_
  obtain ⟨χ, hχ⟩ := ext V hV ψ gam hg
  exact ⟨χ, hχ, hx V hV ψ gam hg χ hχ⟩

end GlobalTheory.ChartExtend
