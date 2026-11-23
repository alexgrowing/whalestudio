import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KeyVals

variable {S : Scheme.{0}}

abbrev FF (S : Scheme.{0}) [IsIntegral S] : Type := S.presheaf.stalk (genericPoint S)

instance fieldFF (S : Scheme.{0}) [IsIntegral S] : Field (FF S) := inferInstanceAs (Field S.functionField)

def genPt (S : Scheme.{0}) [IsIntegral S] : Sp (FF S) ⟶ S := S.fromSpecStalk (genericPoint S)

theorem genPt_le [IsIntegral S] (U : S.Opens) (h : genericPoint S ∈ U) : ⊤ ≤ genPt S ⁻¹ᵁ U := by
  intro p _
  have hp : (genPt S).base p ∈ Set.range (S.fromSpecStalk (genericPoint S)).base := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  exact hp.mem_open U.isOpen h

theorem spMap_germ_fromSpec [IsIntegral S] (W : S.Opens) (hW : IsAffineOpen W) (h : genericPoint S ∈ W) :
    spMap (S.presheaf.germ W (genericPoint S) h).hom ≫ hW.fromSpec = genPt S :=
  hW.fromSpecStalk_eq_fromSpecStalk h

abbrev bG {R : Type} [CommRing R] (G : Over S) (ξ : Sp R ⟶ S) : Over (Sp R) := (Over.pullback ξ).obj G

instance isCommMonObj_bG {R : Type} [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp R ⟶ S) :
    IsCommMonObj (bG G ξ) := Functor.isCommMonObj_obj

def eb {R : Type} [CommRing R] (ξ : Sp R ⟶ S) : (𝟙_ (Over (Sp R))).left ⟶ (𝟙_ (Over S)).left := ξ

theorem eSec_bG {R : Type} [CommRing R] (G : Over S) [GrpObj G] (ξ : Sp R ⟶ S) :
    eSec (bG G ξ) ≫ pullback.fst G.hom ξ = eb ξ ≫ eSec G :=
  LieVB.unitSec_comp (isGrpPullback_pullback G ξ)

def bL {R : Type} [CommRing R] {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (ξ : Sp R ⟶ S) :
    RigLB (bG G ξ) where
  L := L.L.pull (pullback.fst G.hom ξ)
  rig := rigPullOf (G' := bG G ξ) (G := G) (pullback.fst G.hom ξ) (eb ξ) (eSec_bG G ξ) L.L L.rig
  isLB := LB.isLB_pull L.isLB _
  rigGen := LBxP.isGen_pullAlong L.L (pullback.fst G.hom ξ) (eb ξ) (fun _ : PUnit => eSec G) (fun _ => 1)
    (fun _ => eSec (bG G ξ)) (fun _ => eSec_bG G ξ) L.rig L.rigGen

def IsLocSec {R : Type} [CommRing R] {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {δ : LB S}
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (ξ : Sp R ⟶ S) (s : (bL L ξ).L.Sec) : Prop :=
  ∀ (j : (bL L ξ).L.ι) (h : (bL L ξ).L.U j ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i)),
    s.f j = ((pullback.fst G.hom ξ).appLE _ _ h).hom (σ.f (j PUnit.unit, fun _ => i))

def pfr {R : Type} [CommRing R] {G : Over S} [GrpObj G] {g : ℕ} (c : VB.Chart (LieVB.omega G) g) (ξ : Sp R ⟶ S)
    (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) (k : Fin g) : Γ(LieVB.omega (bG G ξ), ⊤) :=
  (LieVB.omegaBase (isGrpPullback_pullback G ξ)).app ⊤ (QCoh.pullbackSections ξ (LieVB.omega G) hc (c.e k))

def IsDual {R : Type} [CommRing R] {G : Over S} [GrpObj G] {g : ℕ} (c : VB.Chart (LieVB.omega G) g)
    (ξ : Sp R ⟶ S) (y : Fin g → (epsR R ⟶ bG G ξ)) : Prop :=
  ∃ hc : ⊤ ≤ ξ ⁻¹ᵁ c.U, ∀ j, ∃ v : Pdiv.LieG (bG G ξ), v.1 = y j ∧ ∀ k,
    VB.dualApp (LieVB.tangent v) le_top (pfr c ξ hc k) = if j = k then 1 else 0

def IsKeyVal (κ : Rule) [IsIntegral S] [CharZero (FF S)] {G : Over S} [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G)
    {δ : LB S} (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (c : VB.Chart (LieVB.omega G) g) (i : δ.ι) (v : FF S) : Prop :=
  ∃ (s : (bL L (genPt S)).L.Sec) (y : Fin g → (epsR (FF S) ⟶ bG G (genPt S))) (x : KeyIn (FF S)) (hg : x.P.g = g),
    IsLocSec σ i (genPt S) s ∧ IsDual c (genPt S) y ∧
    KeyOn (RingHom.id (FF S)) x (bG G (genPt S)) (bL L (genPt S)) s (fun j => y (j.cast hg)) ∧ v = κ (FF S) x

end GlobalTheory.KeyVals

end
