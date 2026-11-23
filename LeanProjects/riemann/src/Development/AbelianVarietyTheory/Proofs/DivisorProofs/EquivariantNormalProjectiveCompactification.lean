import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientOfFiniteGroup
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCover
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExistsIffTopExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionToNormalization
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

noncomputable section
namespace GlobalTheory.EqModel

theorem isProjOver_pi_const {R : Type} [CommRing R] (κ : Type) [Finite κ] (A : Over (Sp R))
    (h : IsProjOver A.hom) : IsProjOver (∏ᶜ fun _ : κ => A).hom := by
  let n := Nat.card κ
  let e : κ ≃ Fin n := Finite.equivFin κ
  let I₁ : (∏ᶜ fun _ : κ => A) ≅ ∏ᶜ fun _ : Fin n => A := (Pi.reindex e.symm (fun _ : κ => A)).symm
  let I₂ : (∏ᶜ fun _ : Fin n => A) ≅ ReciprocityTheory.ChartRestriction.G.Out.powObj A n :=
    (limit.isLimit _).conePointUniqueUpToIso (ReciprocityTheory.ChartRestriction.G.Out.powIsLimit A n)
  have : IsIso (I₁ ≪≫ I₂).hom.left := ((Over.forget _).mapIso (I₁ ≪≫ I₂)).isIso_hom
  have hp := Models.FamInh.isProjOver_powObj A h n
  have e' := ProjSpace.isProjOver_comp_of_isClosedImmersion (I₁ ≪≫ I₂).hom.left hp
  rwa [Over.w] at e'

theorem isOpenImmersion_toNormalization {V P X : Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact c] [QuasiSeparated c] (h : c ≫ p = j) :
    IsOpenImmersion c.toNormalization := by
  first
  | (rename_i h_5 h_7 h_8 h_9; revert V P X c p h_5 j h_7 h_8 h_9 h; exact @_root_.GlobalTheory.NormalizationOpenImmersion.main)
  | exact @_root_.GlobalTheory.NormalizationOpenImmersion.main
  | exact _root_.GlobalTheory.NormalizationOpenImmersion.main
  | (apply _root_.GlobalTheory.NormalizationOpenImmersion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormalizationOpenImmersion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormalizationOpenImmersion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormalizationOpenImmersion.main ..)

theorem isQProjOver_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsQProjOver f := by
  obtain ⟨N, i, _, e⟩ := h
  exact ⟨N, i, inferInstance, inferInstance, e⟩

theorem exists_projective_quotient {F : Type} [Field F] {X : Scheme.{0}} (s : X ⟶ Sp F) {Γ : Type}
    [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (hs : IsProjOver s) (hρ : ∀ g, (ρ g).hom ≫ s = s) :
    ∃ (W : Scheme.{0}) (q : X ⟶ W) (sW : W ⟶ Sp F), IsAffineQuotient ρ q ∧ q ≫ sW = s ∧
      IsProjOver sW ∧ IsFinite q ∧ Surjective q := by
  have := OrbitsInAffineOpens.of_isQProjOver (isQProjOver_of_isProjOver' hs) ρ
  obtain ⟨W, q, hq⟩ := QuotientGluing.exists_isAffineQuotient ρ
  have hqs := hq.comp_desc s hρ
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hs).1
  have : IsProper (q ≫ hq.desc s hρ) := by rw [hqs]; infer_instance
  have : LocallyOfFiniteType (q ≫ hq.desc s hρ) := by rw [hqs]; infer_instance
  have : IsProper (hq.desc s hρ) := hq.isProper _
  obtain ⟨L, hL⟩ := GaloisQuotient.exists_isAmpleLB_of_isAffineQuotient hq
    (isQProjOver_of_isProjOver' hs)
  exact ⟨W, q, hq.desc s hρ, hq, hqs, hL.isProjOver _, hq.isFinite (hq.desc s hρ), hq.surjective⟩

theorem exists_equivariant_model : ∀ (F : Type) [Field F] [NumberField F] (X V : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (j : V ⟶ X) [IsOpenImmersion j] (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut V), IsProjOver sX → Nonempty V → GlobalTheory.IsNormalScheme V → (∀ γ, (ρ γ).hom ≫ j ≫ sX = j ≫ sX) → ∃ (X' W : Scheme.{0}) (φ : X' ⟶ X) (ℓ : V ⟶ X') (ρ' : Γ →* Aut X') (q : X' ⟶ W) (sW : W ⟶ Sp F) (_ : IsIntegral X'), GlobalTheory.IsNormalScheme X' ∧ IsProjOver (φ ≫ sX) ∧ IsOpenImmersion ℓ ∧ ℓ ≫ φ = j ∧ (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) ∧ IsAffineQuotient ρ' q ∧ q ≫ sW = φ ≫ sX ∧ IsProjOver sW ∧ IsIntegral W ∧ IsFinite q ∧ Surjective q := by
  intro F _ _ X V _ sX j _ Γ _ _ ρ hX hne hN hρ
  classical
  let A : Over (Sp F) := Over.mk sX
  let P : Over (Sp F) := ∏ᶜ fun _ : Γ => A
  let B : Over (Sp F) := Over.mk (j ≫ sX)
  let c : B ⟶ P := Pi.lift fun γ => Over.homMk ((ρ γ).hom ≫ j) (by simpa [A, B] using hρ γ)
  have hcπ (γ : Γ) : c.left ≫ (Pi.π (fun _ : Γ => A) γ).left = (ρ γ).hom ≫ j := by
    rw [← Over.comp_left, Pi.lift_π]; rfl

  let σ₀ (g : Γ) : P ⟶ P := Pi.lift fun γ => Pi.π (fun _ : Γ => A) (γ * g)
  have hσπ (g γ : Γ) : σ₀ g ≫ Pi.π (fun _ : Γ => A) γ = Pi.π (fun _ : Γ => A) (γ * g) :=
    Pi.lift_π _ _
  have hσ (g h : Γ) : σ₀ g ≫ σ₀ h = σ₀ (h * g) :=
    Pi.hom_ext _ _ fun γ => by rw [Category.assoc, hσπ, hσπ, hσπ, mul_assoc]
  have hσ1 : σ₀ 1 = 𝟙 P := Pi.hom_ext _ _ fun γ => by rw [hσπ, mul_one, Category.id_comp]
  let σI (g : Γ) : P.left ≅ P.left :=
    { hom := (σ₀ g).left, inv := (σ₀ g⁻¹).left,
      hom_inv_id := by rw [← Over.comp_left, hσ, inv_mul_cancel, hσ1]; rfl,
      inv_hom_id := by rw [← Over.comp_left, hσ, mul_inv_cancel, hσ1]; rfl }
  let σ : Γ →* Aut P.left := MonoidHom.mk' σI fun g h => Iso.ext (by
    change (σ₀ (g * h)).left = (σ₀ h).left ≫ (σ₀ g).left
    rw [← Over.comp_left, hσ])
  have hσP (g : Γ) : (σ g).hom ≫ P.hom = P.hom := Over.w (σ₀ g)
  have hρmul (g γ : Γ) : (ρ (γ * g)).hom = (ρ g).hom ≫ (ρ γ).hom := by rw [map_mul]; rfl
  have H (g : Γ) : (ρ g).hom ≫ c.left = c.left ≫ (σ g).hom := by
    have e : (Over.homMk (ρ g).hom (by simpa [B] using hρ g) : B ⟶ B) ≫ c = c ≫ σ₀ g :=
      Pi.hom_ext _ _ fun γ => by
        rw [Category.assoc, Category.assoc, hσπ]
        ext1
        simp only [Over.comp_left, hcπ, Over.homMk_left, hρmul, Category.assoc]
    exact congrArg CommaMorphism.left e

  have : IsProper sX := ((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX).1
  have hP : IsProjOver P.hom := isProjOver_pi_const Γ A hX
  have : IsProper P.hom := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hP).1
  have hcP : c.left ≫ P.hom = j ≫ sX := Over.w c
  have hc1 : c.left ≫ (Pi.π (fun _ : Γ => A) 1).left = j := by rw [hcπ, map_one]; rfl
  have : IsSeparated (c.left ≫ P.hom) := by rw [hcP]; infer_instance
  have : QuasiSeparated c.left := .of_comp c.left P.hom
  have : IsSeparated (Pi.π (fun _ : Γ => A) 1).left := by
    have : IsSeparated ((Pi.π (fun _ : Γ => A) 1).left ≫ sX) := Over.w (Pi.π (fun _ : Γ => A) 1) ▸ inferInstance
    exact .of_comp _ sX
  have : IsIntegral V := isIntegral_of_isOpenImmersion j
  have : IsIntegral B.left := ‹IsIntegral V›
  have : GlobalTheory.IsNormalScheme B.left := hN
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (j ≫ sX)
  have : CompactSpace V := ⟨by
    rw [j.isOpenEmbedding.isInducing.isCompact_iff, Set.image_univ]
    exact NoetherianSpace.isCompact _⟩
  have : IsNoetherian V := {}
  have : QuasiCompact (c.left ≫ (Pi.π (fun _ : Γ => A) 1).left) := by
    rw [hc1]
    exact quasiCompact_of_noetherianSpace_source j
  have : QuasiCompact c.left := .of_comp c.left (Pi.π (fun _ : Γ => A) 1).left
  have : LocallyOfFiniteType (c.left ≫ P.hom) := by rw [hcP]; infer_instance
  have : LocallyOfFiniteType c.left := locallyOfFiniteType_of_comp c.left P.hom

  have hfin : IsFinite c.left.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType c.left P.hom fun x _ =>
      charZero_of_injective_ringHom
        ((Scheme.ΓSpecIso (.of F)).inv ≫ (j ≫ sX).appTop ≫ V.Γevaluation x).hom.injective
  let φ : c.left.normalization ⟶ X := c.left.fromNormalization ≫ (Pi.π (fun _ : Γ => A) 1).left
  have hφ : φ ≫ sX = c.left.fromNormalization ≫ P.hom := by
    simp only [φ, Category.assoc]
    congr 1
    exact Over.w (Pi.π (fun _ : Γ => A) 1)
  have hproj : IsProjOver (φ ≫ sX) := hφ ▸ isProjOver_comp_of_isFinite _ hP
  have hnorm : GlobalTheory.IsNormalScheme c.left.normalization :=
    IsNormalScheme.normalization_of_isIntegral c.left
  let ρ' := normalizationAction c.left ρ σ H
  have hρ' (g : Γ) : (ρ' g).hom ≫ φ ≫ sX = φ ≫ sX := by
    rw [hφ, normalizationAction_fromNormalization_assoc, hσP]
  obtain ⟨W, q, sW, hq, hqs, hW, hqf, hqs'⟩ := exists_projective_quotient (φ ≫ sX) ρ' hproj hρ'
  refine ⟨c.left.normalization, W, φ, c.left.toNormalization, ρ', q, sW, inferInstance, hnorm, hproj,
    isOpenImmersion_toNormalization c.left (Pi.π (fun _ : Γ => A) 1).left j hc1, ?_,
    fun g => (toNormalization_normalizationAction c.left ρ σ H g).symm, hq, hqs, hW, hq.isIntegral,
    hqf, hqs'⟩
  simp only [φ, Scheme.Hom.toNormalization_fromNormalization_assoc, hc1]

end GlobalTheory.EqModel
