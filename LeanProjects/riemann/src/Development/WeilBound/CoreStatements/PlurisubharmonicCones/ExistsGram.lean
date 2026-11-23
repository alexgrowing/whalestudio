import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFormOfIsHodgeGram
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramPullbackIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogenyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace LevelTowerAlt.Gram

theorem exists_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (x : Sp ℂ ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), (∀ i, IsTanAt t.G x (v i)) → ∃ Γ : Matrix (Fin n) (Fin n) ℂ, IsHodgeGram t.G t.PP.L x v Γ := by
  intro E _ _ _ H S t hp hA hK x n v hv
  obtain ⟨Q, ψ, -, hQ, hQL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H S t hp hA hK ℂ x
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, -, hAH, -, d₁, -⟩ := GlobalTheory.thetaUnifAV_all Q rig hrig
  have hl : ∀ a, ∃ t' : epsR ℂ ⟶ Q.A, t'.left ≫ ψ = (v a).left ∧ IsTangent t' := by
    intro a
    have sq : (v a).left ≫ t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x := Over.w (v a)
    let t' : epsR ℂ ⟶ Q.A := Over.homMk (hQ.1.lift _ _ sq) (hQ.1.lift_snd _ _ _)
    have h1 : t'.left ≫ ψ = (v a).left := hQ.1.lift_fst _ _ _
    refine ⟨t', h1, (ReciprocityTheory.ChartRestriction.G.Chart.tan_push hQ t').2 ?_⟩
    rw [h1]
    exact hv a
  choose t' h1 h2 using hl
  choose W hW _ using fun a => d₁ (t' a) (h2 a)
  exact ⟨Matrix.of fun a b => Real.pi * hermForm Hm (W a) (W b), Q, ψ, t', u, Hm, χ, W, hQ, hQL.symm, hAH,
    fun a => ⟨h1 a, hW a⟩, fun _ _ => rfl⟩

theorem gram_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (Γ Γ' : Matrix (Fin n) (Fin n) ℂ), L.IsLB → (∀ i, IsTanAt G x (v i)) → IsHodgeGram G L x v Γ → (∀ p q, HodgeIP G L x (v p) (v q) (Γ' p q)) → Γ' = Γ.transpose := by
  intro S G _ L x n v Γ Γ' hL hv hG hIP
  obtain ⟨Q, ψ, v', u, Hm, χ, W, hp, hiso, hAH, hvW, hΓ⟩ := hG
  have hM := pull_isLB hL ψ
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  obtain ⟨ht₁, ht₂, -⟩ := GlobalTheory.AnyUnif.tangent_and_unimodular GlobalTheory.thetaUnifAV_all Q u
  have htan : ∀ a, IsTangent (v' a) := fun a =>
    (ReciprocityTheory.ChartRestriction.G.Chart.tan_push hp (v' a)).2 (by rw [(hvW a).1]; exact hv a)
  ext p q
  obtain ⟨-, -, -, A, _, φ, g, u', Hm', χ', a', b', a, b, h1, h2, h3, h4, h5, h6, e⟩ :=
    hodgeInnerProduct_iff_hodgeForm.1 (hIP p q)
  have key := GlobalTheory.T.hol_unif_compare_isogeny S G L x Q.A A ψ φ Q.g g (GlobalTheory.TorsionTauCompare.transport Q.isLB hM hw u) u' Hm Hm' χ χ'
    hL Q.isAb hp h1 ht₁ ht₂ (GlobalTheory.TorsionTauCompare.isAH_transport Q.isLB hM hw u hAH) h2 (v' q) (v' p) a' b' (W q) (W p) a b
    (htan q) (htan p) (h3.trans (hvW q).1.symm) (h4.trans (hvW p).1.symm) (hvW q).2 (hvW p).2 h5 h6
  rw [e, key, Matrix.transpose_apply, hΓ]

end LevelTowerAlt.Gram
