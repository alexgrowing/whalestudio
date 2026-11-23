import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedPointMemRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickeningsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TowerAlg

theorem isPullback_of_grp {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B'] {f : S' ⟶ S}
    {F : B'.left ⟶ B.left} (h : IsGrpPullback B' B f F) : IsPullback F B'.hom B.hom f := h.1

theorem exists_alg (hG : GlobalFnsSt) (hE : Ega) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
    (hA : admitted R I) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)]
    [∀ e, IsCommMonObj (Y e)] (hY : ∀ e, IsAbelianScheme (Y e)) (N : ∀ e, CP (Y e))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (h : ∀ e, IsCPPullback (N e) (N (e + 1)) (thickTrans R I e) (β e))
    (hamp : RelAmple (Y 0) (N 0).L.L) :
    ∃ (B : Over (Spec (CommRingCat.of R))) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : CP B)
      (b : ∀ e, (Y e).left ⟶ B.left), IsAbelianScheme B ∧ RelAmple B Q.L.L ∧
      (∀ e, IsCPPullback (N e) Q (thick R I e) (b e)) ∧ ∀ e, β e ≫ b (e + 1) = b e := by
  have hN : IsNoetherianRing R := hA.1.1
  have hI : I ≠ ⊤ := hA.2.2.2.1.ne_top
  have hc : IsAdicComplete I R := hA.1.2.2.2
  choose hβ v hv using h
  obtain ⟨B, M, b, hp, hs, hM, ha, hb, hβb, hiso⟩ := hE.1 R I hI hc hA.2.1 Y β
    (fun e => (N e).L.L) v (fun e => isPullback_of_grp (hβ e)) (fun e => (hY e).smooth)
    (fun e => ⟨(N e).L.isLB, (hv e).gen⟩) hamp
  obtain ⟨g, hB, hg⟩ := GlobalTheory.T.isAbelianScheme_of_abelian_thickenings hE R I hA Y β hY hβ B b hp hs hb hβb
  have c := hB.comm
  obtain ⟨Q, hQ, hq⟩ := exists_cp_alg hG hE.2.2.1 hI hc N hB hp hg hM hiso hY
  exact ⟨B, g, c, Q, b, hB, by rw [hQ]; exact ha, hq, hβb⟩

theorem nonempty_alg : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X), RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L → Nonempty T.Alg := by
  intro hL _ hE R _ _ _ I hA G _ _ P X _ T hamp
  obtain ⟨B, _, _, Q, b, h₁, h₂, h₃, h₄⟩ := exists_alg hL.globalFns hE hA (fun e => (T.l e).Q.B)
    (fun e => (T.l e).Q.isAb) (fun e => (T.l e).D.M) T.β T.β_pb hamp
  exact ⟨⟨B, h₁, Q, h₂, b, h₃, h₄⟩⟩

end GlobalTheory.TowerAlg
end
