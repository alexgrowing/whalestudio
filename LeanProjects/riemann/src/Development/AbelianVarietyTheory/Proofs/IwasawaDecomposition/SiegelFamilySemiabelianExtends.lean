import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoDetAffDetOm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroEssFiniteTypeStalk
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory

namespace GlobalTheory.SiegLoc

theorem isAmpleLB_tens_pull {X S : Scheme.{0}} (π : X ⟶ S) [IsFinite π] {Ω : LB S} {Ω' : LB X} (hΩ : Ω.IsLB)
    (hΩ' : Ω'.IsLB) (e : LBIso Ω' (Ω.pull π)) (BD : EffCartierData S) (h : BD.KeepsRegular π) (M : ℕ)
    (hA : IsAmpleLB (CechPic.tens (lbPow Ω M) (CechPic.dual BD.lb))) :
    IsAmpleLB (CechPic.tens (lbPow Ω' M) (CechPic.dual (BD.pull π h).lb)) := by
  have hB := BD.isLB_lb
  have hB' := (BD.pull π h).isLB_lb
  have hT := CechPic.isLB_tens (isLB_lbPow hΩ M) (CechPic.isLB_dual hB)
  have hT' := CechPic.isLB_tens (isLB_lbPow hΩ' M) (CechPic.isLB_dual hB')
  refine (hA.pull_of_isFinite π).of_lbIso hT' ((CechPic.cls_eq_iff hT' (pull_isLB hT π)).1 ?_)
  rw [CechPic.cls_pull hT, CechPic.cls_tens (isLB_lbPow hΩ M) (CechPic.isLB_dual hB),
    CechPic.cls_tens (isLB_lbPow hΩ' M) (CechPic.isLB_dual hB'), CechPic.cls_lbPow hΩ, CechPic.cls_lbPow hΩ',
    CechPic.cls_dual hB, CechPic.cls_dual hB', map_add, map_nsmul, map_neg,
    (CechPic.cls_eq_iff hΩ' (pull_isLB hΩ π)).2 e, (CechPic.cls_eq_iff hB' (pull_isLB hB π)).2 (BD.lbIso_pull π h),
    CechPic.cls_pull hΩ, CechPic.cls_pull hB]

theorem isAmpleLB_polOf_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (φ φs : InvFun ℤ) (F : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S) (h : BD.KeepsRegular π) (M : ℕ), 1 ≤ D.p + D.q → 3 ≤ n → Odd n → n ∣ l.M → IsPolFan id (Module.finrank ℚ E / 2 * (D.p + D.q)) φ → AgreesPsd (Module.finrank ℚ E / 2 * (D.p + D.q)) φs φ → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → SiegData (Module.finrank ℚ E / 2 * (D.p + D.q)) φ n F S s j G e BD d N → (∀ x, ((ω (κ x) : c.F) : ℂ) = (x : ℂ)) → IsSiegPull s j G e κ C π → IsAmpleLB (CechPic.tens (lbPow (hodge G (Module.finrank ℚ E / 2 * (D.p + D.q))) M) (CechPic.dual BD.lb)) → IsAmpleLB (polOf C M (BD.pull π h)) := by
  intro E _ _ _ H D l Xo c n R _ b ω φ φs F S s j _ G _ e BD d N κ C π h M _ _ _ _ _ _ hω _ hloc hS _ hP hA
  obtain ⟨-, -, -, -, hG, hsm, -⟩ := hS
  obtain ⟨μ, -, -, -, hfin, -, hμ, -⟩ := hP
  haveI := c.fin
  haveI : NumberField c.F := {}
  letI : Algebra (𝓞 c.F) R := b.toAlgebra
  haveI : Algebra.FiniteType ℤ R := by
    have h₁ : Algebra.FiniteType (𝓞 c.F) R := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (n : 𝓞 c.F)) R
    exact Algebra.FiniteType.trans (S := 𝓞 c.F) inferInstance h₁
  have hO := ThetaDedekind.isLB_detOm hω C
  have hV := LieVB.isVB_omega G (Module.finrank ℚ E / 2 * (D.p + D.q))
  have hV' := LieVB.isVB_omega_of_isGrpPullback hμ hV
  have e₁ := HodgeCech.lbIso_detOm_det C hO hV'
  have e₂ := (hV.lbIso_det_pullback π).trans (pull_isLB hV.isLB_det π) (hV.pullback π).isLB_det hV'.isLB_det
    ((hV.pullback π).lbIso_det_of_iso (asIso (LieVB.omegaBase hμ)))
  exact isAmpleLB_tens_pull π hV.isLB_det hO
    (e₁.trans hO hV'.isLB_det (pull_isLB hV.isLB_det π) e₂.symm) BD h M hA

end GlobalTheory.SiegLoc
