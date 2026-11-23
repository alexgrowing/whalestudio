import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackInclusionFactorSymmetric
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_pullback_inclusion_factor_symmetric : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (L : LB G'.left), L.IsLB → ∀ (O : Type) [Ring O] [StarRing O] (oG : RingAct G' O), (∀ a : O, LBIso (cubeLB G' ![fst G' G' ≫ oG.act a, snd G' G'] L) (cubeLB G' ![fst G' G', snd G' G' ≫ oG.act (star a)] L)) → ∀ (e f : O) (inc : G ⟶ G'), IsMonHom inc → inc ≫ oG.act e = inc → star e * f * e = star e * star f * e → ∀ P : LB (G2 G).left, P.IsLB → LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act f)).left) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) := by
  first | exact @GlobalTheory.MumSymPull.lbIso_swap | exact GlobalTheory.MumSymPull.lbIso_swap | (intros; apply GlobalTheory.MumSymPull.lbIso_swap <;> assumption)
