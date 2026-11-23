import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationCompleteDvrOfLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EgaBundleFromLaws

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.UU GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnifNormal

theorem thetaNZ_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [Smooth G.hom] (L : LB G.left)
    (h : ∃ θ : LB.Sec L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) : ThetaNZ G L := by
  obtain ⟨θ, x, hx, hc⟩ := h
  refine ⟨θ, fun y => ?_⟩
  have ho : IsOpen (G.hom '' (nonzeroLocus θ : Set G.left)) := G.hom.isOpenMap _ (nonzeroLocus θ).isOpen
  have hy : y ∈ G.hom '' (nonzeroLocus θ : Set G.left) :=
    (IsLocalRing.specializes_closedPoint (R := R) y).mem_open ho ⟨x, hx, hc⟩
  obtain ⟨g, hg, e⟩ := hy
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hg
  exact ⟨g, i, e, hi⟩

theorem exists_polAV_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L)
    (W : S.Opens) (hG : IsSemiAbelian G) (hs : L.IsSymmetric) (hp : IsProper (pullback.snd G.hom W.ι))
    (ha : RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)))
    (hk : KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)))
    {K : Type} [Field K] (x : Sp K ⟶ S) (hx : Set.range x ⊆ W) :
    ∃ (A : PolAV (Sp K)) (gen : (Over.pullback x).obj G ≅ A.A), IsMonHom gen.hom ∧
      LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom x)) := by
  have hx' : Set.range x ⊆ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
  let x' : Sp K ⟶ W.toScheme := IsOpenImmersion.lift W.ι x hx'
  have ex : x' ≫ W.ι = x := IsOpenImmersion.lift_fac _ _ _
  let φ : ((Over.pullback x).obj G).left ⟶ ((Over.pullback W.ι).obj G).left :=
    pullback.lift (pullback.fst G.hom x) (pullback.snd G.hom x ≫ x') (by
      rw [Category.assoc, ex]; exact pullback.condition)
  have eφ : φ ≫ pullback.fst G.hom W.ι = pullback.fst G.hom x := pullback.lift_fst _ _ _
  have h := isGrpPullback_pullback G x
  have hφ : IsGrpPullback ((Over.pullback x).obj G) ((Over.pullback W.ι).obj G) x' φ :=
    (isGrpPullback_pullback G W.ι).cancel (h.congr ex.symm eφ.symm) (pullback.lift_snd _ _ _)
  have hW := IsSemiAbelian.pullback W.ι G hG
  have hab : IsAbelianScheme ((Over.pullback W.ι).obj G) := ⟨hW.comm, hW.smooth, hp, hW.geomConnected⟩
  have hL := pull_isLB L.isLB (pullback.fst G.hom x)
  have hiso : LBIso (L.L.pull (pullback.fst G.hom x)) ((L.L.pull (pullback.fst G.hom W.ι)).pull φ) :=
    LBIso.chartPull (chartPullSame L.L _ _ _ φ fun _ => eφ.symm) (Geo.Tor.chartPullPull _ φ φ rfl)
      (PolBaseChange.lbIso_refl (pull_isLB L.isLB (pullback.fst G.hom W.ι)))
  obtain ⟨h₁, h₂, h₃⟩ := GlobalTheory.pol_pull _ _ _ _ x' φ _ _ (pull_isLB L.isLB _) hL hab hφ hiso
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim K _ h₁
  obtain ⟨hL', hr, -, hs'⟩ := Out.CubePf.cubePull _ _ G _ (cubeMapOf h) L c
  obtain ⟨-, w, hw, -⟩ := hs' hs
  refine ⟨⟨(Over.pullback x).obj G, h₁, g, hg, L.L.pull (pullback.fst G.hom x), hL, ⟨_, hr⟩,
    fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩, h₂ ha, h₃ hk⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 _)), ?_⟩
  exact LBIso.chartPull (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (chartPullId _) (PolBaseChange.lbIso_refl hL)

theorem exists_unif_psiUnitOn : Laws → Laws2 → Laws3 → Laws4 → Laws5 → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) := by
  intro h₁ h₂ h₃ h₄ h₅ R _ _ _ hz hn hi hc G _ _ L c W hG hs hS hE hθ hW hab hp ha hk
  have : (IsLocalRing.maximalIdeal R).IsMaximal := inferInstance
  have hadm : admitted R (IsLocalRing.maximalIdeal R) :=
    ⟨⟨hn, inferInstance, hi, hc⟩, hc, hz, inferInstance,
      inferInstanceAs (IsIntegrallyClosed (IsLocalRing.ResidueField R))⟩
  have hgen : Set.range (jK R) ⊆ W := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := hW
    refine Specializes.mem_open (y := y) ?_ W.isOpen hy
    refine (PrimeSpectrum.le_iff_specializes (R := R) _ _).1 fun r hr => ?_
    have hz0 : z.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ z.2
    have hr' : algebraMap R (FractionRing R) r ∈ z.asIdeal := hr
    rw [hz0, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at hr'
    rw [hr']
    exact Ideal.zero_mem _
  obtain ⟨A, gen, hm, hL⟩ := exists_polAV_fibre G L c W hG hs hp ha hk (jK R) hgen
  obtain ⟨P, rfl, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric h₁ R A G hG gen hm L c hs
  have := hG.smooth
  obtain ⟨D, U, hU, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocalDomain_prime h₁ h₂ h₃ (GlobalTheory.LN.ega_of_laws h₁ h₂) (GlobalTheory.LN.uniformisation_dvr h₁ h₂ h₃ h₄ h₅) R _ hadm
    (inferInstanceAs (IsPrincipalIdealRing (IsLocalRing.ResidueField R))) G P hG hS hE
    (thetaNZ_of_closedPoint G _ hθ) A gen hm hL
  refine ⟨D, A, U, hU, ?_⟩
  rw [hab]
  exact GlobalTheory.T.psiUnitOn_abelian_locus_uniformisation h₁ h₂ h₃ h₄ h₅ R _ hadm D A G hG U (hab ▸ W.isOpen)

end GlobalTheory.UnifNormal

end
