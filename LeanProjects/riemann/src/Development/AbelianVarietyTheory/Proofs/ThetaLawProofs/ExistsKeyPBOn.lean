import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTf

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : IsLieBasis (fun i : Fin m => v (i.cast e)) := by
  subst e
  exact hv

theorem exists_keyPB_on : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (y : KeyIn R) (P' : Out.PolAV (Sp R')) (φ : P'.A.left ⟶ y.P.A.left) (hg : 1 ≤ P'.g), P'.g = y.P.g → IsGrpPullback P'.A y.P.A (spMap f) φ → LBIso P'.L (y.P.L.pull φ) → ∃ rig hr th hth v hv, KeyPB ⟨P', hg, rig, hr, th, hth, v, hv⟩ y f := by
  intro R R' _ _ f x P' φ hg e h ⟨w, hw₀⟩
  have hL' := P'.isLB
  have hw := (isGen_iff _).1 hw₀
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec x.P.A := PolBaseChange.eSec_comm h
  have hr₀ : (rigPullOf φ (spMap f) he x.P.L x.rig).IsGen :=
    Out.LBxP.isGen_pullAlong x.P.L φ (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) x.rig x.rig_gen
  obtain ⟨rig, hr, hm⟩ := Transport.exists_transport (pull_isLB hL' (eSec P'.A))
    (pull_isLB (pull_isLB x.P.isLB φ) (eSec P'.A))
    (LB.linCombIso w (K := PUnit) (fun _ => eSec P'.A) (fun _ => 1)) (DVR.linCombIso_isGen w hw₀ _ _) _ hr₀
  obtain ⟨th', hth'⟩ := sec_pull_down hw x.P.isLB hL' x.th
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange R R' f x.P.A P'.A φ h x.P.isAb.smooth x.P.g x.v x.basis
  refine ⟨rig, hr, th', fun s => ?_, fun i => v' (i.cast e), isLieBasis_cast e hb',
    φ, he, w, e, Chart.dualMapR f, h, hw₀, hm,
    appLE_eq_of_stalk _ x.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv' _⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨k', hk'⟩ := exists_chart hL' y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨k', hk', ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (x.th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e' := hth' _ (𝟙 _) y k k' hk hk'
    rw [Category.id_comp] at e'
    exact isUnit_of_mul_isUnit_right (e' ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.KeyTf
