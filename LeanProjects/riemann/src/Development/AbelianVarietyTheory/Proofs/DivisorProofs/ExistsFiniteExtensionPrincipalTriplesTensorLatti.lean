import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEigenLineDegreeFormula
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriod
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorDecompositionPureTypeCmTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsTenBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.TenPair

theorem spMap_comp_ringHom {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem mapRingHom_comp {K K' K'' : Type} [Field K] [Field K'] [Field K''] (f : K →+* K') (g : K' →+* K'') :
    (RingOfIntegers.mapRingHom g).comp (RingOfIntegers.mapRingHom f) = RingOfIntegers.mapRingHom (g.comp f) :=
  RingHom.ext fun _ => rfl

theorem exists_isTen_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (A B : PAT H (Sp (𝓞 K))) (r s : ℕ),
    ρ ^ 2 = -(H.d : 𝓞 K) → HasType H A.t.act ρ r 0 → HasType H B.t.act ρ s 0 →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (j : K →+* K') (ω : 𝓞 K') (C : Ell H (𝓞 K') ω)
      (A' B' : PAT H (Sp (𝓞 K'))) (_ : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
      (_ : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (DA DB : Datum H)
      (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H),
      DA.p + DA.q = r ∧ DB.p + DB.q = s ∧ Nonempty (IsTen C DA hA A') ∧ Nonempty (IsTen C DB hB B') := by
  intro E _ _ _ H K _ _ ρ A B r s hρ hA hB
  have hU : ThetaUnifAV := GlobalTheory.thetaUnifAV_all
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hE : HomExtDvr := GlobalTheory.homExtension_semiAbelian_dvr_unconditional
  have hC : CMCurve := GlobalTheory.cmCurve_closed
  have hPB : Out.PolBaseChangeSt := hL.polBaseChange
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  obtain ⟨χ, hχ⟩ := GlobalTheory.exists_isKroneckerChar (d := H.d) H.d_prime.ne_zero (Or.inr (by have := H.d_mod; omega))
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hρ₀ : (σ (ρ : K)) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (σ.comp (algebraMap (𝓞 K) K)) hρ
    simpa using this
  obtain ⟨M, _, ω, C, x, hω, hP, -, -⟩ := GlobalTheory.CM.EllExists.exists_ell hC hU hL hE E H χ hχ _ hρ₀
  obtain ⟨k, _, j, i, hj, hi⟩ := PureDeg.exists_compositum K σ M
  obtain ⟨A', mA', -⟩ := PAT.exists_pullback E H _ _ (spMap (RingOfIntegers.mapRingHom j)) A
  obtain ⟨C', φ', hC'⟩ := exists_ellMap hPB E H _ ω C _ (RingOfIntegers.mapRingHom i)
  have e : 2 * RingOfIntegers.mapRingHom i ω - 1 = RingOfIntegers.mapRingHom j ρ := by
    apply RingOfIntegers.ext
    apply Subtype.ext
    have h1 : (((RingOfIntegers.mapRingHom j ρ : 𝓞 k) : k) : ℂ) = σ ρ := hj _
    have h2 : (((RingOfIntegers.mapRingHom i ω : 𝓞 k) : k) : ℂ) = (ω : M) := hi _
    rw [h1, ← hω, ← h2]
    rfl
  have hA' : HasType H A'.t.act (2 * RingOfIntegers.mapRingHom i ω - 1) r 0 := by
    rw [e]
    exact (hasType_baseChange E H _ _ _ A.t A'.t mA' ρ r 0).1 (PureDeg.mapRingHom_injective j) hA
  have hP' : C'.IsPrincipalAt ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) := by
    refine (EllComp.ellMap_comp E H _ ω C _ _ C' _ φ' hC').2.1 _ ?_
    convert hP using 1
    ext a
    exact hi _
  obtain ⟨k₁, _, hk, ω₁, C₁, φ₁, A₁, mA₁, DA, -, ha, hC₁, hDA, -, -, ⟨tA⟩⟩ :=
    GlobalTheory.CM.Recog.exists_isTen_of_hasType hU hL hE E H k _ C' A' r hP' hA'
  let j₁ : K →+* k₁ := (IntermediateField.inclusion hk).toRingHom.comp j
  obtain ⟨B₁, mB₁, -⟩ := PAT.exists_pullback E H _ _ (spMap (RingOfIntegers.mapRingHom j₁)) B
  have e₁ : 2 * ω₁ - 1 = RingOfIntegers.mapRingHom j₁ ρ := by
    have h3 := congrArg (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) e
    simp only [map_sub, map_mul, map_ofNat, map_one, hC₁.1] at h3
    rw [h3]
    rfl
  have hB₁ : HasType H B₁.t.act (2 * ω₁ - 1) s 0 := by
    rw [e₁]
    exact (hasType_baseChange E H _ _ _ B.t B₁.t mB₁ ρ s 0).1 (PureDeg.mapRingHom_injective j₁) hB
  have hP₁ : C₁.IsPrincipalAt ((algebraMap k₁ ℂ).comp (algebraMap (𝓞 k₁) k₁)) := by
    refine (EllComp.ellMap_comp E H _ _ C' _ _ C₁ _ φ₁ hC₁).2.1 _ ?_
    convert hP' using 1
    ext a
    rfl
  obtain ⟨k₂, _, hk', ω₂, C₂, φ₂, B₂, mB₂, DB, -, hb, hC₂, hDB, -, -, ⟨tB⟩⟩ :=
    GlobalTheory.CM.Recog.exists_isTen_of_hasType hU hL hE E H k₁ ω₁ C₁ B₁ s hP₁ hB₁
  obtain ⟨A₂, mA₂, -⟩ := PAT.exists_pullback E H _ _
    (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk').toRingHom)) A₁
  obtain ⟨tA₂, -⟩ := isTen_baseChange E H _ ω₁ C₁ DA ha A₁ tA _ ω₂ C₂ _ φ₂ A₂ mA₂ hC₂
  let J : K →+* k₂ := (IntermediateField.inclusion hk').toRingHom.comp j₁
  obtain ⟨nA₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mA' mA₁
  obtain ⟨nA, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp nA₁ mA₂
  obtain ⟨nB, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mB₁ mB₂
  have eA : spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk').toRingHom) ≫
      (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) ≫
        spMap (RingOfIntegers.mapRingHom j)) = spMap (RingOfIntegers.mapRingHom J) := by
    rw [spMap_comp_ringHom, spMap_comp_ringHom, mapRingHom_comp, mapRingHom_comp]
  have eB : spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk').toRingHom) ≫
      spMap (RingOfIntegers.mapRingHom j₁) = spMap (RingOfIntegers.mapRingHom J) := by
    rw [spMap_comp_ringHom, mapRingHom_comp]
  exact ⟨k₂, inferInstance, inferInstance, J, ω₂, C₂, A₂, B₂, eA ▸ nA, eB ▸ nB, DA, DB, ha, hb, hDA, hDB,
    ⟨tA₂⟩, ⟨tB⟩⟩

end GlobalTheory.CM.TenPair
end
