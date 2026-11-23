import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsPullQk
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalIffOfIsPullDegTauBimultStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDataDescendsPrincipalIdealSubringStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvrStatement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem isPolFibre_prj {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'}
    {D₀ : Out.DegPre R} {D₁ : Out.DegPre R'} (p : Out.IsPullDeg f D₀ D₁) : IsPolFibre f D₀.P D₁.P (prj p) :=
  ⟨H1.dim_unique _ D₁.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D₀.P.smoothDim)
    (eSec D₁.P.A (Classical.arbitrary (PrimeSpectrum R'))), pull_grp p, LBIso.symm ⟨p.w, p.w_gen⟩⟩

theorem exists_arcIn_over_valuationRing : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (ρ : 𝓞 K₁ →+* Tv.V) (O : Type) [CommRing O] (β : O →+* c.F) (b : O →+* Tv.V), (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → (∀ x, algebraMap Tv.V Tv.Fr (b x) = io (algebraMap c.F K₁ (β x))) → ∃ (aw : ArcIn Dw l β Tv.V b) (aK : ArcIn Dw l (RingHom.id c.F) Tv.Fr (io.comp (algebraMap c.F K₁))) (pw : Out.IsPullDeg (algebraMap Tv.V Tv.Fr) aw.D₀ aK.D₀) (pK : Out.IsPullDeg io a.D₀ aK.D₀) (ψ : aw.D₀.P.A.left ⟶ s.B.A.left), InBC (algebraMap Tv.V Tv.Fr) aw (aK.restrict β) pw ∧ InBC io a aK pK ∧ IsPolFibre ρ s.B aw.D₀.P ψ ∧ prj pw ≫ ψ = prj pK ≫ s.φB ∧ TauCan aw.D₀ n' := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s Tv io ρ O _ β b hρ hb
  letI := H.starRing
  obtain ⟨aK, pK, hBC, -⟩ := GlobalTheory.ArcPull.exists_isBC hK.laws.polBaseChange hK.laws.globalFns a io io.injective
  have hB : IsPolFibre (algebraMap (𝓞 K₁) K₁) s.B a.D₀.P s.φB :=
    (isFibreOf_iff_isPolFibre _ _ _ s.B s.toCMPart.xB s.φB).1 s.good.2.2.2.1
  obtain ⟨Pv, ψ, hψ⟩ := exists_isPolFibre hK.laws.polBaseChange ρ s.B
  have hcomp : io.comp (algebraMap (𝓞 K₁) K₁) = (algebraMap Tv.V Tv.Fr).comp ρ :=
    RingHom.ext fun x => (hρ x).symm
  have hχ : IsPolFibre ((algebraMap Tv.V Tv.Fr).comp ρ) s.B aK.D₀.P (prj pK ≫ s.φB) :=
    hcomp ▸ GlobalTheory.CM.EllComp.isPolFibre_comp hB (isPolFibre_prj pK)
  obtain ⟨φ, hφψ, hφ⟩ := GlobalTheory.CM.EllComp.exists_isPolFibre_lift hψ hχ
  obtain ⟨DV, p, rfl, hp, hq⟩ := GlobalTheory.T.exists_degenerationData_extension_over_dvr hK Tv.V Tv.Fr Pv aK.D₀ φ hφ
  obtain rfl : prj p = φ := eq_of_heq hp
  obtain ⟨oB, hoB⟩ := polOActPull _ _ _ s.B DV.P ψ hψ.2.1 hψ.2.2 (𝓞 E) s.oa
  have htau : TauCan aK.D₀ n' :=
    (GlobalTheory.T.isTauCanonical_iff_of_isPullDeg_tauBimult hK K₁ Tv.Fr io a.D₀ aK.D₀ pK n' io.injective a.bimult aK.bimult).1 s.tau
  have hact : ∀ x, (aK.oa.onB.act x).left ≫ prj p = prj p ≫ (oB.act x).left := fun x => by
    have h₁ : (aK.oa.onB.act x).left ≫ prj pK = prj pK ≫ (a.oa.onB.act x).left := hBC.act x
    have w := hφ.2.1.1.w
    generalize prj p = u at hφψ w ⊢
    generalize prj pK = u' at hφψ h₁
    refine hψ.2.1.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hoB, reassoc_of% hφψ, hφψ, reassoc_of% h₁, s.act]
    · rw [Category.assoc, Category.assoc, Over.w, w, ← Category.assoc, Over.w]
  obtain ⟨aw, pw, rfl, hpw, hin, ht⟩ := GlobalTheory.T.arcData_descends_principalIdealSubring hK E H Dw l c O β Tv.V Tv.Fr (algebraMap Tv.V Tv.Fr) b
    ((io.comp (algebraMap c.F K₁)).comp β) (aK.restrict β) DV p n' oB (IsFractionRing.injective _ _)
    (RingHom.ext fun x => (hb x).symm) s.n_pos htau hact (fun v => hq _ _ aK.bimult) (fun v => hq _ _ aK.bimult)
  obtain rfl : pw = p := eq_of_heq hpw
  exact ⟨aw, aK, pw, pK, ψ, hin, (inBC_iff_isBC io a aK pK).2 hBC, hψ, hφψ, ht⟩

end GlobalTheory.ArcCM
