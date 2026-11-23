import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedToIdempotents
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeZeroOfLe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LePreimageOpenPartIffTestCoordinates
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomGenericPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanRowsClassZeroEqInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricTestMapClassicalPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialFibreTestGeometricTestStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusActionWeightedChartsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LeOfClosedPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.GradedCharts
open GlobalTheory.ProjSpace GlobalTheory.ZJ Matrix

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem split_geoTest (hL : GlobalTheory.UT.LL) [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (hBig : S.Big)
    {l : Q.Λ} {A A' : Matrix S.J S.J Ω} (hAA : A' * A = 1) {T : AddSubgroup S.Gam} [Finite (T →+ ZMod S.N)]
    {wt : S.J → (T →+ ZMod S.N)}
    (hwt : ∀ i, (S.proj _ (wt i)).map (algebraMap o Ω) *ᵥ (A * Q.B l) i = (A * Q.B l) i)
    {X : Scheme.{0}} (a : X ⟶ Q.P.left) (b : X ⟶ M.Z) {H : LB X} {s : S.J → H.Sec}
    (haff : ∀ i, wt i = 0 → IsAffineOpen (nonzeroLocus (s i))) (hcov : ⨆ i : {i // wt i = 0}, nonzeroLocus (s i.1) = ⊤)
    (hcrd : ∀ (K : Type) [Field K] (x : Sp K ⟶ X),
      ∃ x' : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme, x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x ≫ a ∧
        ∀ w, Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x' w → Crd H s x (A.map (M.val (x ≫ b)) *ᵥ w))
    {p : ℕ} [Fact p.Prime] {y : Sp (ZH.OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} (g : ρ.GeoTest p y₀) (c : Q.Fac y g.u)
    (tm : Q.TMap g c) (hU : Set.range (ZH.gPt p ≫ y) ⊆ U₀) (hl : y (ZH.cPt p) ∈ Q.W l)
    (hT : T = S.TT M (y (ZH.cPt p))) (hO : ∀ i j, A i j ∈ M.O (y (ZH.cPt p)) ∧ A' i j ∈ M.O (y (ZH.cPt p)))
    (φ : g.mod.Φ.G.left ⟶ X) [IsAffineHom φ] (hφ1 : φ ≫ a = g.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι)
    (hφ2 : φ ≫ b = g.mod.Φ.G.hom ≫ ZH.rPt p ≫ y) :
    ∃ d ≤ S.g, ∃ cc : Fin d → (T →+ ZMod S.N), ((ofSec wt 0 s haff hcov).pull φ).Split (H := g.mod.Φ.G) cc := by
  obtain ⟨m, cl, hm, hcl, hcl0, hmw, hmv⟩ := exists_matrix hB Q hAA hwt g c tm hU hl hT hO
  have : IsAlgClosed (ZH.kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have := g.mod.smooth
  have : Smooth g.u.G.hom := SmoothOfRelativeDimension.smooth S.g _
  have : Smooth g.mod.Φ.G.hom := MorphismProperty.of_isPullback g.mod.cart.1 this
  have : IsReduced g.mod.Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced g.mod.Φ.G.hom
  choose F hF using fun i => (GlobalTheory.SecRatio.existsUnique_isLin g.mod.Φ.G.hom g.mod.F (m i)).exists
  have hlr := locus_ratio g.mod.Φ.G.hom φ s F fun u hu => by
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists (g.mod.Φ.H_isLB 1) g.mod.F u
    obtain ⟨x', hx', hc⟩ := hcrd _ (u ≫ φ)
    obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) x'
    rw [Category.assoc, hφ1] at hx'
    obtain ⟨k, hk⟩ := hmv u x' v w hu hx' hv hw
    have h3 := hc w hw
    rw [Category.assoc, hφ2, reassoc_of% hu, hk] at h3
    have h4 := crd_lin hF (ψ := RingHom.id _) (hu.trans (Spec.map_id _).symm) hv
    exact ⟨_, CrdCalc.crd_smul k h4, h3⟩
  exact ⟨_, le_of_add_le_right g.mod.dim.le,
    GlobalTheory.T.exists_torus_action_weighted_charts hL.1 hL.2.1 _ g.mod.Φ S.g S.N (S.r * S.N) _ S.J _ g.mod.F F g.mod.pol m
    ((ofSec wt 0 s haff hcov).pull φ) (Equiv.refl _) (fun α => cl (g.mod.xe α))
    ⟨(GlobalTheory.ZH.utest_dim_and_split hL o Ω S ρ p y₀ g.u).2.2.2.1, hBig.1, hBig.2.1⟩ g.mod.good g.mod.dim hm hF
    (fun α β => (hcl _ _).trans ⟨fun ⟨n, hn⟩ => ⟨g.mod.xe.symm n, g.mod.xe.injective (by simpa using hn)⟩,
      fun ⟨n, hn⟩ => ⟨g.mod.xe n, by simp [hn]⟩⟩)
    ((congrArg cl (map_zero _)).trans hcl0)
    (fun i j hij => (hmw i j hij).trans (congrArg cl (g.mod.xe.apply_symm_apply _).symm))
    fun i => hlr i.1⟩

theorem hasCharts : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → ex.core.HasCharts := by
  intro hL o Ω _ _ _ hA S ρ M U₀ EE hB Q ex hBig hGeo hFib z
  change M.Z at z
  obtain ⟨W, l, A, A', wt, hW, hz, hle, hsup, hO, hAA, hwt⟩ := exists_adapted hB Q z
  obtain ⟨R, _, _, t, ht, htz, htW⟩ := exists_immersion hW hz
  have hT : ∀ q, S.TT M z = S.TT M (t q) := fun q => by
    have h1 : z ⤳ t q := htz ▸ ((PrimeSpectrum.le_iff_specializes ⊥ q).1 bot_le).map t.continuous
    have h2 : S.supI M z = S.supI M (t q) :=
      (hsup _ (htW (Set.mem_univ q))).antisymm fun a ha => RatModel.Div.of_specializes ha h1
    exact congrArg (fun I => S.perp (AddSubgroup.closure I)) h2
  obtain ⟨H, s, haff, hcov, hcrd⟩ := exists_sections hB Q hAA hwt ⟨z, hz⟩ hle hO t htW hT
  have := FreeNear.finite_char S (S.TT M z)
  refine ⟨R, inferInstance, inferInstance, t, ht, htz, ofSec wt 0 s haff hcov, fun p _ y τ x hx h hh h1 h2 => ?_⟩
  have hU := cl_of_test τ
  obtain ⟨y₀, g, c, ⟨tm⟩⟩ := (GlobalTheory.T.exists_geometricTest_map_classicalPoint hL o Ω S ρ M U₀ EE hB Q hBig hGeo).1 p y hU
  obtain ⟨e, he, hef⟩ := GlobalTheory.T.exists_iso_special_fibre_test_geometric_test hL o Ω S ρ M U₀ EE hB Q ex p y y₀ g c tm τ hBig hFib
  have hy : t (x (IsLocalRing.closedPoint _)) = y (ZH.cPt p) :=
    (congrArg (fun f => f (IsLocalRing.closedPoint (ZH.kb p))) hx).trans
      (congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (ZH.OO p))))
  have hyW := (congrArg (· ∈ W) hy).mp (htW (Set.mem_univ _))
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have hei : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hie : e.hom.left ≫ e.inv.left = 𝟙 _ := by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  obtain ⟨h', hh'⟩ : ∃ h' : ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H).left ⟶
    pullback (Q.G.ι ≫ Q.P.hom) t, h' = h := ⟨h, rfl⟩
  subst hh'
  have : IsAffineHom h' := hh
  have hφ1 : (e.inv.left ≫ h') ≫ pullback.fst _ _ ≫ Q.G.ι = g.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
    have h3 : h' ≫ pullback.fst (Q.G.ι ≫ Q.P.hom) t ≫ Q.G.ι =
        e.hom.left ≫ g.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι :=
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h1).trans (Category.assoc _ _ _))).trans hef.symm
    rw [Category.assoc, h3, reassoc_of% hei]
  have hφ2 : (e.inv.left ≫ h') ≫ pullback.snd _ _ ≫ t = g.mod.Φ.G.hom ≫ ZH.rPt p ≫ y := by
    have h3 : h' ≫ pullback.snd (Q.G.ι ≫ Q.P.hom) t ≫ t =
        ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H).hom ≫ ZH.rPt p ≫ y :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t) h2).trans ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) hx)))
    rw [Category.assoc, h3]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ ZH.rPt p ≫ y) (Over.w e.inv))
  obtain ⟨d, hd, cc, hs⟩ := split_geoTest hL hB Q hBig hAA hwt _ _ haff hcov hcrd g c tm hU (hle hyW)
    ((hT _).trans (congrArg (S.TT M) hy)) (hO _ hyW) (e.inv.left ≫ h') hφ1 hφ2
  exact ⟨d, hd, cc, split_pull_of_comp e _ h' _ (by rw [reassoc_of% hie]) hs⟩

end GlobalTheory.ZH.GradedCharts
end
