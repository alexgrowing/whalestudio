import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseDataPullbackAlongMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDataRefines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyPullbackLocalUniformisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TChart.Taut

theorem unif_pull_of_canonOn : ∀ {g n : ℕ} {φ : InvFun ℤ} (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  intro g n φ C G₁ _ _ P hM hC V' _ _ _ θ hV hθ hs D' e hD
  obtain ⟨Q', e', hr, hd⟩ := hD
  have h₁ := GlobalTheory.T.tautological_base_data_pullback_along_map C.T C.R V' θ C.iw C.s C.form n C.Q C.e Q' _ hs C.data hd
  have h₂ := GlobalTheory.Mum.pullData_refines C.R V' θ C.Q Q' _ D'.toPre D'.tau_bimult e' h₁ hr
  refine GlobalTheory.T.canonical_mumford_family_pullback_local_uniformised C.R V' θ hM.1 hV hθ C.Q _ G₁ P hM.2.2.1 hC ?_ D' _ h₂
  rw [genericPoint_eq_bot_of_affine]
  show (∏ k, C.t k) ∉ Ideal.comap θ (⊥ : PrimeSpectrum V').asIdeal
  rw [Ideal.mem_comap, map_prod]
  exact Finset.prod_ne_zero_iff.2 fun k _ => hs (.inl k)

end GlobalTheory.TChart.Taut
