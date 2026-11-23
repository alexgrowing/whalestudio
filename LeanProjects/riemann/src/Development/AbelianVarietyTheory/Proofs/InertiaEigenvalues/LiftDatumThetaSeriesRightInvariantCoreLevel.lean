import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayFieldAny
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompatStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.LevelInv

theorem cast_mul {D : D7} {V W : HSp D} (e : V = W) (a b : GA D V) :
    cast (congrArg (GA D) e) (a * b) = cast (congrArg (GA D) e) a * cast (congrArg (GA D) e) b := by
  subst e
  rfl

theorem apply_eq_castDict {D : D7} {V W : HSp D} (e : V = W) (φ : GA D V → ℂ) (x : GA D V) :
    φ x = castDict e φ (cast (congrArg (GA D) e) x) := by
  subst e
  rfl

theorem thetaKO_mul_right {D : D7} {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (h : GA D V)
    (g κ : GA D W) (f : WO V W → ℂ) : thetaKO om h (g * κ) f = thetaKO om h g (om (1, κ) f) := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem ser_right_inv_levelK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ) (h : GA D (Vc D j)), h ∈ GfC (Vc D j) → ∀ (w : (Rl.cV j).W) (a : ℂ) (φ : GA D (T.V ((j : ℕ) + 1) T.σ₀) → ℂ), castDict hV φ = (fun g => a * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w g) → ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, φ (g * k) = φ g := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
    u h hh w a φ hφ k hk g
  have hpb : T.pb = Rl.toRealDat.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore Rl.toRealDat hT.toLawsM hcore.lev (hpins.2.tuple ()).half
  set k' : GA D (Wc D j) := cast (congrArg (GA D) hV) k with hk'def
  have hkk : cast (congrArg (GA D) hV.symm) k' = k := by rw [hk'def]; simp
  have hlift : Formalism.IndefR.Lev.IsLevelLift (Wc D j) (Rl.toRealDat.βW j) (Rl.toRealDat.datWp j Rl.toRealDat.triv) 1 k' :=
    (GlobalTheory.T.level_character_embedding_compat T Rl.toRealDat κ v₀ hcore.lev hti hpb j T.σ₀ T.toCore.good_σ₀ hV k').2 (by rw [hkk]; exact hk)
  have hv : Rl.toRealDat.ωP j A3.A.μ0 (1, k') (Rl.toRealDat.vP j A3.A.μ0) = (1 : ℂ) • Rl.toRealDat.vP j A3.A.μ0 := by
    have e := GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar Rl.toRealDat hcore.lev hcore.models.inf hcore.thP.ωP hcore.thP.vP j A3.A.μ0 1 1 k'
      (GlobalTheory.RawLift.LevelFix.realDatum_identity_lifts_identity Rl.toRealDat j A3.A.μ0) hlift
    rw [e, GlobalTheory.RawLift.LevelFix.levChi_flag_one Rl.toRealDat j A3.A.μ0, inv_one]
  have hP : ∀ P, Rl.toRealDat.ωP j A3.A.μ0 (1, k') (Rl.toRealDat.ptP j A3.A.μ0 P) = Rl.toRealDat.ptP j A3.A.μ0 P := by
    intro P
    have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite Rl.toRealDat.ψ Rl.toRealDat.θ (Vc D j) (Wc D j) _ _
      (Rl.toRealDat.ωP j A3.A.μ0) hcore.models.inf (hcore.thP.ωP j A3.A.μ0) _ _ _ _ _ (hcore.thP.pt_theta j A3.A.μ0) 1
      (Subgroup.one_mem _) k' hlift.1 1 hv P
    exact this.trans (one_smul ℂ _)
  have hser : ∀ x, ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w (x * k') = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w x := by
    intro x
    rw [ser_vP, ser_vP, thetaKO_mul_right, hP]
  have e1 : φ (g * k) = castDict hV φ (cast (congrArg (GA D) hV) g * k') := by
    exact (apply_eq_castDict hV φ (g * k)).trans (congrArg (castDict hV φ) (cast_mul hV g k))
  have e2 : φ g = castDict hV φ (cast (congrArg (GA D) hV) g) := apply_eq_castDict hV φ g
  rw [e1, e2, hφ]
  exact congrArg (fun z => a * z) (hser _)

end GlobalTheory.SeriesTie.LevelInv
