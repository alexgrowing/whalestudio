import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PrimAn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAnalyticModelOnFrameOrbitIsolatingStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormAnOnOrbit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmLatticeDataAbelianPartSplitPointStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmObjOfPeriod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmObjBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibreStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalTrivialisationIffNormalisedArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcMatchesFrameOfModelOnOrbitStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataDescentNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsScaled
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobi
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicIndexSums
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM.Exist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_lift_fibre {R R₂ K : Type} [CommRing R] [CommRing R₂] [Field K] {B : GlobalTheory.CM.PAT H (Sp R)}
    {B₂ : GlobalTheory.CM.PAT H (Sp R₂)} {j : R →+* R₂} (m : SABMap B₂.t B.t (spMap j)) {f : R →+* K} {f₂ : R₂ →+* K}
    (hf : f₂.comp j = f) {P : Out.PolAV (Sp K)} {ψ : P.A.left ⟶ B.pol.A.left} (hψ : IsPolFibre f B.pol P ψ)
    (act : 𝓞 E → (P.A ⟶ P.A)) (hact : ∀ x, (act x).left ≫ ψ = ψ ≫ (B.t.act.act x).left) :
    ∃ ψ₂ : P.A.left ⟶ B₂.pol.A.left, IsPolFibre f₂ B₂.pol P ψ₂ ∧
      ∀ x, (act x).left ≫ ψ₂ = ψ₂ ≫ (B₂.t.act.act x).left := by
  have hs : spMap f₂ ≫ spMap j = spMap f := (GlobalTheory.ArcId.sp_comp _ _).trans (congrArg spMap hf)
  have w : ψ ≫ B.t.G.hom = (P.A.hom ≫ spMap f₂) ≫ spMap j :=
    hψ.2.1.1.w.trans (by rw [Category.assoc, hs])
  obtain ⟨ψ₂, h₁, h₂⟩ : ∃ ψ₂ : P.A.left ⟶ B₂.t.G.left, ψ₂ ≫ m.φ = ψ ∧ ψ₂ ≫ B₂.t.G.hom = P.A.hom ≫ spMap f₂ :=
    ⟨_, m.cart.1.lift_fst _ _ w, m.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback P.A B₂.t.G (spMap f₂) ψ₂ := m.cart.cancel (hψ.2.1.congr hs.symm h₁.symm) h₂
  refine ⟨ψ₂, ⟨?_, g₂, ?_⟩, fun x => ?_⟩
  · exact H1.dim_unique P.A.hom P.smoothDim
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback g₂.1 B₂.dim)
      (eSec P.A (IsLocalRing.closedPoint K))
  · have e : LBIso (B₂.t.PP.L.pull ψ₂) (B.t.PP.L.pull ψ) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) ψ₂ h₁.symm
    exact LBIso.trans (pull_isLB B₂.t.PP.isLB _) (pull_isLB B.t.PP.isLB _) P.isLB e hψ.2.2
  · apply m.cart.1.hom_ext
    · have e := m.act x
      change ((act x).left ≫ ψ₂) ≫ m.φ = (ψ₂ ≫ (B₂.t.act.act x).left) ≫ m.φ
      rw [Category.assoc, Category.assoc, h₁, hact, e, ← Category.assoc, h₁]
    · rw [Category.assoc, Category.assoc, h₂, Over.w (B₂.t.act.act x), h₂, ← Category.assoc, Over.w (act x)]

theorem one_le_of_isIso {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    {U : Unf Xo c σ r} (hU : IsUnf U) {k : U.Comp} {ξ' : Fin r → E} (hξ : (U.X k).IsIso ξ') :
    1 ≤ Dw.p ∧ 1 ≤ Dw.q := by
  obtain ⟨τ⟩ : Nonempty (U.X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : τ ∈ (U.X k).Ψ
    · exact ⟨⟨τ, h⟩⟩
    · exact ⟨⟨_, by_contra fun h' => h (((U.X k).cmType τ).2 h')⟩⟩
  have h := IsotropicIndexSums.isotropicIndex_bounds (U.X k) hξ.2.1 hξ.2.2 τ
  have h1 := hU.1
  have h2 := (hU.2.1 k).1
  omega

theorem exists_cmIn_tie : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La₀ La c₁ : ℝ) (lam : Fin (r - 2) → Fin r → E) (n' : ℕ) (ν₀ : E), IsUnf U → l.A = 1 → 3 ≤ r → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La₀ (hX ▸ x) lam → La₀ ^ 2 ≤ La ^ 2 → 0 < n' → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (em : K₁ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (s : CMIn a e th jj n' La c₁), em.comp (algebraMap c.F K₁) = c.F.val.toRingHom ∧ s.ν₀ = ν₀ ∧ Comparison₂ Uw a em s.ξ k ξ' x := by
  intro hK E _ _ _ H Dw l Xo c _ _ r U Uw k ξ' x Xx hX 𝔄 La₀ La c₁ lam n' ν₀ hU hA hr hξ hx h𝔄 hΛ hS hLa hn hap hν hν₀
    hint htr
  letI := H.starRing
  have hg : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨hp, hq⟩ := one_le_of_isIso hU hξ
  have hpq : 3 ≤ Dw.p + Dw.q := hU.1 ▸ hr
  obtain ⟨A, gam, ξ, jj, DB, tyB, eB, hO, hξ0, hrk, hdvd, hbeta, hprim, hct, hab, hDp, hDq⟩ :=
    GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating E H Dw l Xo c _ r U Uw k ξ' x n' ν₀ hg hU hξ hx hap hν hν₀ hint
  obtain ⟨A', gam', ξ₁, eX, hO', hprim', hnorm', hξ₁, hbe', hab'⟩ :=
    GlobalTheory.ArcShift.exists_normAn_onOrbit E H Dw l Xo c _ r U Uw k ξ' x n' hg hU hξ hx hn A gam ξ hO hξ0 hrk hprim hct
  obtain ⟨tyB', eB', hB'⟩ := hab' DB ⟨tyB, eB, hab⟩
  have hrk' : Module.finrank (𝓞 E) A'.X = 1 := eX.finrank_eq.trans hrk
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_cm_lattice_data_abelianPart_split_point E H Dw l Xo c _ r U Uw k ξ' x Xx hX 𝔄 La₀ lam hg hU hξ hx h𝔄 hΛ hS A' gam' ξ₁ DB
    tyB' eB' hO' hrk' hDp hDq hB'
  obtain ⟨K, _, _, _, σ₁, ρ, X, ex, hσ₁, hρ, hhh, hex⟩ :=
    GlobalTheory.ArcCM.exists_cmObj_of_period hK E H l c DB _ tyB' _ hB'.2.2.2.2 Z (by omega) hB'.2.1 hA
  obtain ⟨aC, Λ, hΛA, φ, hφ, hφa, hlift⟩ := GlobalTheory.T.exists_complexArcDatum_cmFibre hK E H Dw l Xo c _ r U Uw k ξ' x (𝓞 K) X.B _ hg hU hA A' gam'
    ξ₁ DB tyB' eB' ex hO' hrk' (fun y y' => (hbe' y y').symm ▸ hdvd _ _) hprim' hB' hDp hDq hp hq hex
  subst hΛA
  have htau : TauCan aC.D₀ n' := (GlobalTheory.KappaAn.tauCan_iff_normAn E H Dw l c _ _ _ aC Λ.toGtAn₀ n').2 hnorm'
  let fC : aC.D₀.X ≃ₗ[𝓞 E] A.X := Λ.eX.symm.trans eX
  let ξC : Module.Dual ℤ aC.D₀.X := ξ.comp (fC.toLinearMap.restrictScalars ℤ)
  have htie := GlobalTheory.T.holomorphicArc_matches_frame_of_model_on_orbit hK E H Dw l Xo c _ r U Uw k ξ' x aC Λ.toGtAn₀ ξC hg hU hξ hx hA gam' ξ₁ hO'
    (fun y => by rw [hξ₁]; exact congrArg (fun z => ξ (eX z)) (Λ.eX.symm_apply_apply y)) hlift
  obtain ⟨K₂, _, _, _, i, σ₂, a, p, ψ, hσ₂, hbc, htau₂, hψ, hψa⟩ :=
    GlobalTheory.T.exists_cmArcData_descent_numberField hK E H Dw l c K σ₁ _ X.B aC φ n' hσ₁ hn hφ hφa htau
  obtain ⟨ρ₂, X₂, m, hρ₂, hh₂⟩ := GlobalTheory.ArcCM.exists_cmObj_baseChange hK E H K ρ σ₁ _ _ X K₂ i σ₂ hσ₂
  obtain ⟨ψ₂, hψ₂, hψa₂⟩ := exists_lift_fibre m (f₂ := algebraMap (𝓞 K₂) K₂) (RingHom.ext fun _ => rfl) hψ
    a.oa.onB.act hψa
  let f : aC.D₀.X ≃ₗ[𝓞 E] a.D₀.X := { p.xe with map_smul' := hbc.2.1 }
  let g : a.D₀.X ≃ₗ[𝓞 E] A.X := f.symm.trans fC
  have hem : σ₂.comp (algebraMap c.F K₂) = c.F.val.toRingHom := by
    rw [← hσ₁, ← hσ₂]
    exact RingHom.ext fun y => congrArg σ₂ (i.commutes y).symm
  have hbe : ∀ y z, a.be y z = A.be (g y) (g z) := fun y z => by
    obtain ⟨y, rfl⟩ := (Λ.eX.trans f).surjective y
    obtain ⟨z, rfl⟩ := (Λ.eX.trans f).surjective z
    refine (hbc.2.2.1 _ _).symm.trans ((Λ.be_eq _ _).trans ((hbe' _ _).trans ?_))
    simp [g, fC]
  have hhh₂ : ∀ j (τ : E →+* ℂ), ‖τ (X₂.hh j : E)‖ ≤ La ^ 2 := fun j τ => by
    rw [hh₂, hhh]; exact (hZ j τ).trans hLa
  have hρ' : σ₂ (ρ₂ : K₂) = H.rt0 := by rw [hρ₂, ← hρ, ← hσ₂]; rfl
  clear m hh₂
  generalize DB.p = p₁, DB.q = q₁ at X₂ hDp hDq hhh₂ ψ₂ hψ₂ hψa₂
  subst hDp hDq
  obtain ⟨e, th, s, hs, hsν⟩ := GlobalTheory.ArcCM.Letters.exists_cmIn hK E H Dw l c K₂ a ρ₂ σ₂ X₂ ψ₂ n' La c₁
    (ξ.comp (g.toLinearMap.restrictScalars ℤ)) ν₀ jj hp hq hpq hem hρ' hhh₂ hψ₂ hψa₂ hn htau₂
    (g.finrank_eq.trans hrk)
    (fun h => hξ0 (LinearMap.ext fun y => by
      obtain ⟨y, rfl⟩ := g.surjective y
      exact LinearMap.congr_fun h y))
    (GlobalTheory.ArcId.betaAt_comp g ξ hbe hbeta) htr
  refine ⟨K₂, _, _, _, σ₂, a, e, th, jj, s, hem, hsν, aC, p, ξC, hbc, fun y => ?_, htie⟩
  rw [hs]
  exact congrArg (fun z => ξ (fC z)) (f.symm_apply_apply y).symm

end GlobalTheory.ArcCM.Exist
