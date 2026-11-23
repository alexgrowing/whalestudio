import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleRestrictNormalFiniteIndex
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleOfRestrictNormalFiniteIndex
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal
  Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace LocalParameterTwist

section SS

variable {k : Type} [Field k] {a : ℕ}

theorem isInv_iff_of_image {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] (ρ₁ : Γ₁ →* GL (Fin a) k)
    (ρ₂ : Γ₂ →* GL (Fin a) k) (h₁₂ : ∀ g, ∃ g', ρ₂ g' = ρ₁ g) (h₂₁ : ∀ g', ∃ g, ρ₁ g = ρ₂ g')
    (W : Submodule k (Fin a → k)) : IsInv ρ₁ W ↔ IsInv ρ₂ W := by
  constructor
  · intro hW g v hv
    obtain ⟨g₁, e⟩ := h₂₁ g
    rw [← e]
    exact hW g₁ v hv
  · intro hW g v hv
    obtain ⟨g₂, e⟩ := h₁₂ g
    rw [← e]
    exact hW g₂ v hv

theorem isSSRep_of_image {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] (ρ₁ : Γ₁ →* GL (Fin a) k)
    (ρ₂ : Γ₂ →* GL (Fin a) k) (h₁₂ : ∀ g, ∃ g', ρ₂ g' = ρ₁ g) (h₂₁ : ∀ g', ∃ g, ρ₁ g = ρ₂ g')
    (h : IsSSRep ρ₁) : IsSSRep ρ₂ := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((isInv_iff_of_image ρ₁ ρ₂ h₁₂ h₂₁ W).2 hW)
  exact ⟨W', (isInv_iff_of_image ρ₁ ρ₂ h₁₂ h₂₁ W').1 h1, h2⟩

theorem isSSRep_comp_subtype [CharZero k] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k) (H : Subgroup Γ)
    [H.FiniteIndex] (hρ : IsSSRep ρ) : IsSSRep (ρ.comp H.subtype) := by
  have h1 := GlobalTheory.TraceSemisimple.isSSRep_comp_subtype_of_normal_finiteIndex Γ k a ρ H.normalCore
    H.normalCore_normal inferInstance hρ
  refine GlobalTheory.ssRep_of_normal_finiteIndex H k a (ρ.comp H.subtype) (H.normalCore.subgroupOf H)
    (H.normalCore_normal.subgroupOf H) inferInstance (isSSRep_of_image _ _ ?_ ?_ h1)
  · intro n
    exact ⟨⟨⟨n.1, H.normalCore_le n.2⟩, Subgroup.mem_subgroupOf.2 n.2⟩, rfl⟩
  · intro n
    exact ⟨⟨n.1.1, Subgroup.mem_subgroupOf.1 n.2⟩, rfl⟩

end SS

section Range

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

omit [NumberField E] [IsAlgClosure E Ω] in

theorem range_resG (X : CMExt E Ω) :
    (resG E (E' := X.M) (Ω := Ω)).range = (IsScalarTower.toAlgHom E X.M Ω).fieldRange.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_range, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨τ, rfl⟩ x hx
    obtain ⟨m, rfl⟩ := (AlgHom.mem_fieldRange).1 hx
    show τ (algebraMap X.M Ω m) = algebraMap X.M Ω m
    exact τ.commutes m
  · intro hσ
    refine ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv)
      (fun m => hσ (algebraMap X.M Ω m) ((AlgHom.mem_fieldRange).2 ⟨m, rfl⟩)), ?_⟩
    ext x
    rfl

theorem finiteIndex_range_resG (X : CMExt E Ω) : (resG E (E' := X.M) (Ω := Ω)).range.FiniteIndex := by
  have : IsGalois E Ω := {}
  rw [range_resG]
  set L := (IsScalarTower.toAlgHom E X.M Ω).fieldRange with hL
  have hfd : FiniteDimensional E L := by
    let g : X.M →ₗ[E] L :=
      { toFun := fun m => ⟨algebraMap X.M Ω m, (AlgHom.mem_fieldRange).2 ⟨m, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (map_add (algebraMap X.M Ω) x y)
        map_smul' := fun c x => Subtype.ext (by
          simp [Algebra.smul_def, IsScalarTower.algebraMap_apply E X.M Ω]) }
    refine Module.Finite.of_surjective g fun y => ?_
    obtain ⟨m, hm⟩ := (AlgHom.mem_fieldRange).1 y.2
    exact ⟨m, Subtype.ext hm⟩
  exact ⟨fun h0 => (Module.finrank_pos (R := E) (M := L)).ne'
    ((IntermediateField.finrank_eq_fixingSubgroup_index (F := E) (E' := Ω) L).trans h0)⟩

end Range

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

omit [NumberField E] [IsAlgClosure E Ω] in

theorem isPlaceOver_under (X : CMExt E Ω) {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 X.M)}
    (h' : IsPlaceOver A w') : IsPlaceOver A (w'.under (𝓞 E)) := by
  intro x
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, ← h' (algebraMap (𝓞 E) (𝓞 X.M) x)]
  have e : algebraMap X.M Ω ((algebraMap (𝓞 E) (𝓞 X.M) x : 𝓞 X.M) : X.M) = algebraMap E Ω (x : E) := by
    rw [IsScalarTower.algebraMap_apply E X.M Ω]
    rfl
  rw [e]

omit [NumberField E] [IsAlgClosure E Ω] in

theorem natCast_notMem_under (X : CMExt E Ω) {w' : HeightOneSpectrum (𝓞 X.M)} {l : ℕ}
    (hl : ((l : ℕ) : 𝓞 X.M) ∉ w'.asIdeal) : ((l : ℕ) : 𝓞 E) ∉ (w'.under (𝓞 E)).asIdeal := by
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
  exact hl

theorem charPol_locPar_tw (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra K Ω] [IsAlgClosure K Ω] {a : ℕ} (π : CuspSub K a) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)}
    (h : IsPlaceOver A w) {B : Multiset ℂˣ} (hB : (CG.mk π).HasSat w B) (s : ℝ) (σ : Weil h) :
    ((ParLaws.locPar hL (CG.mk π) h).lpTw s).charPol σ =
      (B.map fun b : ℂˣ => X - C ((((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) ^ deg σ * ((b⁻¹ : ℂˣ) : ℂ) ^ deg σ)).prod := by
  obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL K a π w
  obtain ⟨α, rfl, hα⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π hB hσ₀
  have hα' : GlobalTheory.SmGL.HasSatake (ParLaws.toRep σ₀).ρ α := hα
  rw [ParLaws.locPar_mk hL hσ₀ h, ParLaws.rec_eq_diag (ParLaws.isRec_locRec hL h) hα', WD.lpTw_mk,
    WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ]
  have e2 : ∀ (c : ℂ) (d : Fin a → ℂ), c • diagEnd d = diagEnd fun i => c * d i := fun c d =>
    LinearMap.ext fun v => funext fun i => by simp [mul_assoc]
  rw [e2, charpoly_diagEnd, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

theorem wdOf_eq_locPar (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Type} [Field K] [NumberField K] [IsCMField K]
    [Algebra K Ω] [IsAlgClosure K Ω] {a : ℕ} {π : CuspSub K a} {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {χ : HChar (maximalRealSubfield K)} {r : G K Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ}
    (H : IsGalRepOf π χ ι r wt HT) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A w)
    (hl : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    wdOf h hl ι r = (ParLaws.locPar hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2) := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL K a π w
  rw [H.wdOf_eq hl (ParLaws.isRec_locRec hL h) hσ]
  exact congrArg (fun x : WD h => x.lpTw _) (ParLaws.locPar_mk hL hσ h).symm

theorem scal_eq (q f : ℕ) (s : ℝ) (d : ℤ) (b : ℂˣ) :
    ((((q ^ f : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) ^ d * (((b ^ f)⁻¹ : ℂˣ) : ℂ) ^ d) =
      (((q : ℂ) ^ ((s : ℝ) : ℂ)) ^ ((f : ℤ) * d) * ((b⁻¹ : ℂˣ) : ℂ) ^ ((f : ℤ) * d)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : (((q ^ f : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) = ((q : ℂ) ^ ((s : ℝ) : ℂ)) ^ f := by
    have e0 : ((q ^ f : ℕ) : ℂ) = (((q : ℝ) ^ f : ℝ) : ℂ) := by push_cast; ring
    rw [e0, ← Complex.ofReal_cpow (pow_nonneg hq f), ← Real.rpow_natCast_mul hq, mul_comm,
      Real.rpow_mul_natCast hq, Complex.ofReal_pow, Complex.ofReal_cpow hq, Complex.ofReal_natCast]
  have h2 : (((b ^ f)⁻¹ : ℂˣ) : ℂ) = ((b⁻¹ : ℂˣ) : ℂ) ^ f := by
    rw [← inv_pow, Units.val_pow_eq_pow_val]
  rw [h1, h2, ← zpow_natCast ((q : ℂ) ^ ((s : ℝ) : ℂ)), ← zpow_natCast ((b⁻¹ : ℂˣ) : ℂ), ← zpow_mul, ← zpow_mul]

theorem charpoly_eq_at (hL : GlobalTheory.Published.LocalLanglandsGL) [IsCMField E] (X : CMExt E Ω) {a : ℕ} {π : CuspSub E a}
    {P : CuspSub X.M a} {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} {r' : G X.M Ω →* GL (Fin a) (Qbar l)} {wt' : ℤ}
    {HT' : (X.M →+* Qbar l) → Multiset ℤ} (H : IsGalRepOf π (quadChar E ^ a) ι r wt HT)
    (H' : IsGalRepOf P (quadChar X.M ^ a) ι r' wt' HT') {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 X.M)}
    (h' : IsPlaceOver A w') (hl' : ((l : ℕ) : 𝓞 X.M) ∉ w'.asIdeal)
    (hW : ∀ f : ℕ, normV w' = normV (w'.under (𝓞 E)) ^ f →
      ∃ B, (CG.mk π).HasSat (w'.under (𝓞 E)) B ∧ (CG.mk P).HasSat w' (B.map (· ^ f)))
    (σ : Weil h') :
    ((r' σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      ((r (resG E (σ : G X.M Ω)) : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := by
  have h := isPlaceOver_under X h'
  have hl := natCast_notMem_under X hl'
  obtain ⟨B, hB, hB'⟩ := hW (resF h h') (normV_eq_pow_resF h h')
  refine Polynomial.map_injective ι.toRingHom ι.injective ?_
  have e1 := charPol_wdOf hl' ι (Units.continuous_val.comp H'.cont) σ
  have e2 := charPol_wdOf hl ι (Units.continuous_val.comp H.cont) (resW h h' σ)
  rw [coe_resW] at e2
  rw [← e1, ← e2, wdOf_eq_locPar hL H' h' hl', wdOf_eq_locPar hL H h hl,
    charPol_locPar_tw hL P h' hB', charPol_locPar_tw hL π h hB, deg_resW, normV_eq_pow_resF h h',
    Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [scal_eq]

end Local

end LocalParameterTwist

open LocalParameterTwist in

theorem weak_lift_galois_restriction : FinitePlaceStep := by
  intro hL E Ω _ _ _ _ _ _ a ha π X P hWL l _ ι r wt HT r' wt' HT' H H'
  have hss : IsSSRep (r.comp (resG E (E' := X.M) (Ω := Ω))) := by
    have := finiteIndex_range_resG X
    refine isSSRep_of_image (r.comp (resG E (E' := X.M) (Ω := Ω)).range.subtype) _ ?_ ?_
      (isSSRep_comp_subtype r _ H.ss)
    · rintro ⟨g, g', e⟩
      exact ⟨g', by simp [e]⟩
    · intro g'
      exact ⟨⟨resG E g', g', rfl⟩, rfl⟩
  have hWL' : ∀ᶠ w' : HeightOneSpectrum (𝓞 X.M) in Filter.cofinite, ∀ f : ℕ,
      normV w' = normV (w'.under (𝓞 E)) ^ f →
        ∃ B, (CG.mk π).HasSat (w'.under (𝓞 E)) B ∧ (CG.mk P).HasSat w' (B.map (· ^ f)) := hWL
  have hev := (GlobalTheory.HeightCounting.eventually_natCast_notMem X.M l).and hWL'
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := X.M) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hev)
  have hall := GlobalTheory.TypeLeaf.charpoly_eq_of_dense (G X.M Ω) (Qbar l) a
    (fun g => ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))
    (fun g => ((r (resG E g) : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) _ hD
    (Units.continuous_val.comp H'.cont) ((Units.continuous_val.comp H.cont).comp continuous_resG) (by
      rintro g ⟨v, hv, -, B, hB, hg⟩
      have hv' := not_not.1 hv
      exact charpoly_eq_at hL X ι H H' hB hv'.1 hv'.2 ⟨g, mem_Weil_of_isFrob hB hg⟩)
  obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix (r.comp (resG E (E' := X.M) (Ω := Ω))) r' hss H'.ss
    fun g => (hall g).symm
  exact ⟨Pm⁻¹, fun g => by rw [hPm g, inv_inv]; rfl⟩

end PositivityTheory.Pf1.CLGD.K

end
