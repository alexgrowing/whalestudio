import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section
namespace GlobalTheory.EighthPowerBundle

open GlobalTheory.CechPic

def pre0 {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left)
    (hP : IsSymmetricPair h A P) : SiegPre 0 1 (0 : ℤ) (specZIsTerminal.from S) where
  A := A
  ab := hP.1
  P := P
  isLB := hP.2.2.1
  rig₁ := hP.2.2.2.1
  rig₂ := hP.2.2.2.2.1
  symm := hP.2.2.2.2.2
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := fun k _ _ x β z _ hz => by
    rw [map_zero] at hz
    exact absurd hz z.ne_zero

theorem powLB_props : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left),
    IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → IsAbelianScheme (Out.powObj A 8) ∧ (powLB A P).IsLB ∧
      Out.RelAmple (Out.powObj A 8) (powLB A P) ∧ Out.Rigidified (Out.powObj A 8) (powLB A P) ∧
      Out.Sym (Out.powObj A 8) (powLB A P) := by
  intro S h A _ _ P hP hA
  let c := pre0 h A P hP
  have hA' : Out.RelAmple c.A c.diag := hA
  obtain ⟨hpos, -⟩ := isE8_W8
  let pr : Fin 8 → (Out.powObj A 8 ⟶ A) := Out.powPr A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A 8, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (powLB A P).IsLB := LB.isLB_linComb hP.2.2.1 _ _
  have hLW : cls (powLB A P) hL = PrincipalIntegral.quad (cls c.P c.isLB) W8 pr := cls_linComb hP.2.2.1 _ _ _
  have hadd := PrincipalIntegral.pair_mul c SemiRigid.globalFns hA'
  exact ⟨AbelianSchemeGerms.isAbelianScheme_powObj A hP.1 7, hL,
    PosDefAmple.relAmple_linComb_of_posDef SemiRigid.globalFns 0 1 8 ℤ 0 S _ c (Out.powObj A 8) pr W8 hmon huniv hA'
      hpos,
    PrincipalIntegral.rigidified hadd hmon hL hLW,
    PrincipalIntegral.sym hadd (PrincipalIntegral.pair_comm c) hmon hL hLW⟩

end GlobalTheory.EighthPowerBundle
