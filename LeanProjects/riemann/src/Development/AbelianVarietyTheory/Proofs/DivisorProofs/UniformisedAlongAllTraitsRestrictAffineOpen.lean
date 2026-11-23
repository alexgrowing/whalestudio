import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseChangeUniformization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUniformizationIdentityPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdentityPullbackDegeneration
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.CubicalPullBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals

open GlobalTheory.TorsionFormCompare GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum in

theorem hasUnif_of_iso {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (hV : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (G G₀ : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀]
    [IsCommMonObj G₀] (ε : G ≅ G₀) (hε : IsMonHom ε.hom) (hsa : IsSemiAbelian G₀) (L₀ : LB G₀.left)
    (h : HasUnif G₀ L₀) : HasUnif G (L₀.pull ε.hom.left) := by
  obtain ⟨D, A₀, U₀, hL⟩ := h
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have he : eSec G ≫ ε.hom.left = 𝟙 _ ≫ eSec G₀ := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε.hom)
  let L' : RigLB G := ⟨U₀.LG.L.pull ε.hom.left, rigPullOf ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig,
    LB.isLB_pull U₀.LG.isLB _,
    GlobalTheory.CubePullLawChecks.rigPullIsGen ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig U₀.LG.isLB U₀.LG.rigGen⟩
  let w : LB.Iso L'.L (U₀.LG.L.pull ε.hom.left) := idIso L'.L
  have hw : RigAlong ε.hom U₀.LG L' w :=
    ⟨idIso_isGen L'.isLB, (maps_iff w _ (fun _ => eSec G₀) _ L'.rig U₀.LG.rig (𝟙 _) _
      (rigPull_le _ _ he U₀.LG.L) (fun _ => rfl)).1 (idIso_maps L')⟩
  obtain ⟨W, hW, hψ⟩ := psiOnExists V (IsLocalRing.maximalIdeal V) hR D
  obtain ⟨hD, -⟩ := exists_isIdPull V D.toPre W hW hψ
  obtain ⟨bc, U, -, -, hLG, -, -⟩ :=
    exists_unif_move V (IsLocalRing.maximalIdeal V) D A₀ G₀ G ε hR hsa hε U₀ L' w hw hD
  refine ⟨D, A₀, U, ?_⟩
  rw [hLG]
  exact LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) hL

theorem unifAlong_bG {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) {R : Type} [CommRing R]
    (f : Sp R ⟶ S) (hG : IsSemiAbelian G) (h : UnifAlong G L.L) : UnifAlong (bG G f) (bL L f).L := by
  intro V _ _ _ _ hV hf ξ hξ _
  have hξ' : ((ξ ≫ f) ⁻¹' abLocus G).Nonempty := by
    obtain ⟨p, hp⟩ := hξ
    refine ⟨p, ?_⟩
    have := (abLocus_pullback (G' := bG G f) abLocusOne hG (isGrpPullback_pullback G f).1 (ξ p)).2 hp
    simpa using this
  obtain ⟨ε, hε, hφ⟩ := grpPullback_iso ((isGrpPullback_pullback (bG G f) ξ).comp (isGrpPullback_pullback G f))
    (isGrpPullback_pullback G (ξ ≫ f))
  obtain ⟨D, A, U, hU⟩ := hasUnif_of_iso hV _ _ ε hε (IsSemiAbelian.pullback (ξ ≫ f) G hG) _ (h V hV hf (ξ ≫ f) hξ')
  refine ⟨D, A, U, LBIso.trans U.LG.isLB (LB.isLB_pull (LB.isLB_pull L.isLB _) _)
    (LB.isLB_pull (bL L f).isLB _) hU ?_⟩
  exact LBIso.chartPull (h := ε.hom.left)
    (chartPullLinComb L.L _ (fun _ : PUnit => ε.hom.left) (fun _ => pullback.fst G.hom (ξ ≫ f)) (fun _ => 1) _ fun _ => rfl)
    (chartPullLinComb L.L _ (fun _ : PUnit => pullback.fst (bG G f).hom ξ) (fun _ => pullback.fst G.hom (ξ ≫ f))
      (fun _ => 1) _ fun _ => hφ.symm)
    (PolBaseChange.lbIso_refl (LB.isLB_pull L.isLB _))

theorem unifAlong_affineOpen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsSemiAbelian G → UnifAlong G L.L → UnifAlong (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L :=
  fun _ G _ _ L _ hW hG h => unifAlong_bG G L hW.fromSpec hG h

end GlobalTheory.KeyVals

end
