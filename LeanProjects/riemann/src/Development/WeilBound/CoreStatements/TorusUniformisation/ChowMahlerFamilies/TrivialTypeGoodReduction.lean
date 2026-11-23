import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.TrivialTypeGoodReduction

open GlobalTheory GlobalTheory.PointUnif GlobalTheory.EigenSplit
open scoped CategoryTheory.Obj

noncomputable def fibPol {X : Scheme.{0}} (P : Out.PolAV X) {z : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A]
    {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A z φ) : Out.PolAV (Sp ℂ) :=
  have hL := pull_isLB P.isLB φ
  have H := pol_pull _ _ P.A A _ φ P.L _ P.isLB hL P.isAb h (PolBaseChange.lbIso_refl hL)
  { A := A, isAb := H.1, g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull φ, isLB := hL, rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym, ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }

theorem dim_eq_zero {E : Type} [Field E] [NumberField E] {X : Scheme.{0}} (P : Out.PolAV X)
    (act : OAct (𝓞 E) P.A) (y : Sp ℂ ⟶ X) (hy : ∀ τ : 𝓞 E →+* ℂ, LieMult act y τ 0) : P.g = 0 := by
  classical
  have hab := P.isAb
  have := hab.comm
  have hφ := isGrpPullback_pullback P.A y
  obtain ⟨rig, hr⟩ := (fibPol P hφ).rigid
  obtain ⟨u, Hm, χ, Ef, -, -, h1, h2, hF, -⟩ := thetaUnifAV_all (fibPol P hφ) rig hr
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ _) y (Category.id_comp _).symm
  have he := isExp_push hφ u h1 h2 Φ hΦ
  have hker : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  obtain ⟨ρ, hρ⟩ := he.exists_rep act u.Λ u.discrete hker fun a => by
    obtain ⟨F, hF⟩ := hF ((OAct.pullback y P.A act).act a) ((OAct.pullback y P.A act).hom a)
    have hact : ((OAct.pullback y P.A act).act a).left ≫ pullback.fst P.A.hom y =
      pullback.fst P.A.hom y ≫ (act.act a).left := pullback.lift_fst _ _ _
    refine ⟨F, fun z => Over.OverMorphism.ext ?_⟩
    refine (hΦ _).trans ((congrArg (fun q => q.left ≫ pullback.fst P.A.hom y) (hF z)).trans ?_)
    refine (Category.assoc _ _ _).trans ((congrArg ((u.ex z).left ≫ ·) hact).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (act.act a).left) (hΦ _).symm)
  have h0 := (eigenEquiv (isSplitting_embeddings (E := E)) ρ).finrank_eq
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype] at h0
  exact h0.trans (Finset.sum_eq_zero fun i _ => he.finrank_eigenSub act ρ hρ (hy _))

theorem isIso_of_dim_zero {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (hB : IsAbelianScheme B)
    (hg : SmoothOfRelativeDimension 0 B.hom) : IsIso B.hom := by
  have := hB.proper
  have := hB.geomConnected
  have := hB.smooth
  have : Etale B.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hg
  have hs : eSec B ≫ B.hom = 𝟙 (Sp k) := Models.RankZero.section_w η[B]
  obtain ⟨ho, hcl⟩ := isOpenImmersion_and_isClosedImmersion_of_section_of_etale B.hom (eSec B) hs
  have : ConnectedSpace B.left := (GroupConn.connectedSpace_group _ B).1
  have hne : (Set.range (eSec B)).Nonempty := ⟨_, (default : PrimeSpectrum k), rfl⟩
  have hsurj : Function.Surjective (eSec B) :=
    Set.range_eq_univ.1 (IsClopen.eq_univ ⟨(eSec B).isClosedEmbedding.isClosed_range,
      (eSec B).isOpenEmbedding.isOpen_range⟩ hne)
  have : Epi (eSec B).base := (TopCat.epi_iff_surjective _).2 hsurj
  have : IsIso (eSec B) := IsOpenImmersion.isIso _
  have : IsIso (eSec B ≫ B.hom) := by
    rw [hs]
    exact inferInstanceAs (IsIso (𝟙 (Sp k)))
  exact IsIso.of_isIso_comp_left (eSec B) B.hom

end PositivityTheory.Xgn.TrivialTypeGoodReduction

theorem PositivityTheory.Xgn.trivial_type_good_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∀ (σ : L →+* ℂ) (τ : 𝓞 E →+* ℂ), LieMult t.act (spMap σ) τ 0) → ∃ t' : SAB H (Sp (𝓞 L)), Nonempty (SABMap t t' (spMap (algebraMap (𝓞 L) L))) := by
  intro E _ _ _ H L _ _ t ⟨hp, hA, hK⟩ hL
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim L t.G hab
  obtain ⟨σ⟩ : Nonempty (L →+* ℂ) := inferInstance
  obtain rfl : g = 0 := PositivityTheory.Xgn.TrivialTypeGoodReduction.dim_eq_zero
    (GlobalTheory.GenericPol.toPolAV t g hg hp hA hK) t.act (spMap σ) (hL σ)
  exact ⟨GlobalTheory.Models.Inhab.zeroTriple H _, GlobalTheory.Models.RankZero.nonempty_sabMap
    (PositivityTheory.Xgn.TrivialTypeGoodReduction.isIso_of_dim_zero t.G hab hg) (GlobalTheory.Models.RankZero.isIso_zeroTriple _) _⟩
