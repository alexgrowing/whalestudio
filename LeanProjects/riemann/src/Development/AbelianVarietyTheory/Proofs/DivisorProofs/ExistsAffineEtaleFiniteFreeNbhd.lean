import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAwayOfIsAlgebraicOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeAwayMulOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleAwayOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfFiniteAppLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEInjectiveOfGenericPointMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicAppLE
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.GenFinEtField

theorem finrank_app_eq_residueDegree {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (h : f (genericPoint Y) = genericPoint X) {U : X.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen (f ⁻¹ᵁ U)) (hxU₀ : genericPoint X ∈ U) :
    letI := (f.app U).hom.toAlgebra
    Module.finrank Γ(X, U) Γ(Y, f ⁻¹ᵁ U) = f.residueDegree (genericPoint Y) := by
  have hxU : f (genericPoint Y) ∈ U := h ▸ hxU₀
  letI := (f.app U).hom.toAlgebra
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  letI : Algebra Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Y)).hom.toAlgebra
  letI : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (f.app U ≫ Y.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(X, U) (X.residueField (f (genericPoint Y)))
      (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' congr($(Scheme.evaluation_naturality f _ hxU).hom).symm
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation X hU h hxU
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation Y hU' rfl hxU
  exact (IsFractionRing.finrank_eq Γ(X, U) (X.residueField (f (genericPoint Y)))
    Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y))).symm

theorem exists_affine_finite_etale_free : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k], IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧ (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  intro k _ X Y _ _ p q _ hX hY π hπ hg hδ
  have hpP : IsProper p := by
    obtain ⟨N, j, _, hj⟩ := hX
    have := isProper_str k N
    exact hj ▸ inferInstance
  have hqP : IsProper q := by
    obtain ⟨N, j, _, hj⟩ := hY
    have := isProper_str k N
    exact hj ▸ inferInstance
  have : IsSeparated (π ≫ p) := hπ ▸ (inferInstance : IsSeparated q)
  have hsep : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ (inferInstance : LocallyOfFiniteType q)
  have hlft : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U₀, hU₀, hxU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X))
  have hyU₀ : genericPoint Y ∈ π ⁻¹ᵁ U₀ := by
    show π (genericPoint Y) ∈ U₀
    rw [hg]; exact hxU₀
  obtain ⟨V₀, hV₀, hyV₀, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hyU₀
  haveI : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩
  haveI : Nonempty V₀ := ⟨⟨_, hyV₀⟩⟩
  letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
  haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  haveI : CharZero Γ(X, U₀) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U₀ le_top).hom.charZero_iff
      (RingHom.injective (R := k) _)).1 ‹CharZero k›
  haveI : FaithfulSMul Γ(X, U₀) Γ(Y, V₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (GlobalTheory.appLE_injective_of_genericPoint_map π hg ⟨_, hyV₀⟩ hVle)
  haveI : Algebra.FiniteType Γ(X, U₀) Γ(Y, V₀) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType π hlft ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ hVle
  haveI : Algebra.IsAlgebraic Γ(X, U₀) Γ(Y, V₀) := GlobalTheory.GenDegAlg.isAlgebraic_appLE π hg hδ hU₀ ⟨_, hyV₀⟩ hVle
  obtain ⟨a₁, ha₁, H₁⟩ := GlobalTheory.finite_away_of_isAlgebraic_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₂, ha₂, H₂⟩ := GlobalTheory.free_away_mul_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₃, ha₃, H₃⟩ := GlobalTheory.GenericEtale.exists_etale_away_of_isAlgebraic (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  have ha : a₁ * a₂ * a₃ ≠ 0 := mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₃
  have hUU₀ : X.basicOpen (a₁ * a₂ * a₃) ≤ U₀ := X.basicOpen_le _
  have hUa : IsAffineOpen (X.basicOpen (a₁ * a₂ * a₃)) := hU₀.basicOpen _
  have hxU : genericPoint X ∈ X.basicOpen (a₁ * a₂ * a₃) := by
    have hne : X.basicOpen (a₁ * a₂ * a₃) ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff _).1 h)
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (a₁ * a₂ * a₃)).isOpen).2
      ⟨z, trivial, hz⟩
  set U : X.Opens := X.basicOpen (a₁ * a₂ * a₃) with hU_def
  set V : Y.Opens := Y.basicOpen (π.appLE U₀ V₀ hVle (a₁ * a₂ * a₃)) with hV_def
  have hVV₀ : V ≤ V₀ := Y.basicOpen_le _
  have hVe : V = V₀ ⊓ π ⁻¹ᵁ U := Scheme.basicOpen_appLE π V₀ U₀ hVle _
  have hVU : V ≤ π ⁻¹ᵁ U := by rw [hVe]; exact inf_le_right
  have hVa : IsAffineOpen V := hV₀.basicOpen _
  have hyV : genericPoint Y ∈ V := by
    rw [hVe]; exact ⟨hyV₀, show π (genericPoint Y) ∈ U from hg ▸ hxU⟩
  letI iA : Algebra Γ(X, U₀) Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra
  letI iB : Algebra Γ(Y, V₀) Γ(Y, V) := (Y.presheaf.map (homOfLE hVV₀).op).hom.toAlgebra
  letI iAB : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hVU).hom.toAlgebra
  letI iAB' : Algebra Γ(X, U₀) Γ(Y, V) := (π.appLE U₀ V (hVV₀.trans hVle)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U₀) Γ(X, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.map_appLE hVU (homOfLE hUU₀).op).symm)
  haveI : IsScalarTower Γ(X, U₀) Γ(Y, V₀) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.appLE_map hVle (homOfLE hVV₀).op).symm)
  haveI hlA : IsLocalization.Away (a₁ * a₂ * a₃) Γ(X, U) :=
    hU₀.isLocalization_of_eq_basicOpen _ (homOfLE hUU₀) rfl
  haveI hlB : IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) (a₁ * a₂ * a₃)) Γ(Y, V) :=
    hV₀.isLocalization_of_eq_basicOpen _ (homOfLE hVV₀) rfl
  have e1 : a₁ * (a₂ * a₃) = a₁ * a₂ * a₃ := (mul_assoc _ _ _).symm
  have e2 : a₂ * (a₁ * a₃) = a₁ * a₂ * a₃ := by ring
  have e3 : a₃ * (a₁ * a₂) = a₁ * a₂ * a₃ := by ring
  have hfin : Module.Finite Γ(X, U) Γ(Y, V) :=
    H₁ (a₂ * a₃) Γ(X, U) Γ(Y, V) (by rw [e1]; exact hlA) (by rw [e1]; exact hlB)
  have hfree : Module.Free Γ(X, U) Γ(Y, V) :=
    H₂ (a₁ * a₃) Γ(X, U) Γ(Y, V) (by rw [e2]; exact hlA) (by rw [e2]; exact hlB)
  have het : Algebra.Etale Γ(X, U) Γ(Y, V) :=
    H₃ (a₁ * a₂) Γ(X, U) Γ(Y, V) (by rw [e3]; exact hlA) (by rw [e3]; exact hlB)
  have hpre : π ⁻¹ᵁ U = V := GlobalTheory.preimage_eq_of_finite_appLE π hUa hVa ⟨_, hyV⟩ hVU hfin
  have key : ∀ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U → (π.appLE U W hW).hom.Etale →
      (π.appLE U W hW).hom.Finite →
      (letI := (π.appLE U W hW).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, W)) →
      (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    rintro W hW rfl h1 h2 h3
    rw [Scheme.Hom.app_eq_appLE]
    exact ⟨h1, h2, h3⟩
  obtain ⟨h1, h2, h3⟩ := key V hVU hpre.symm het hfin hfree
  exact ⟨U, hUa, hxU, hpre ▸ hVa, h1, h2, h3, finrank_app_eq_residueDegree π hg hUa (hpre ▸ hVa) hxU⟩

end GlobalTheory.GenFinEtField
