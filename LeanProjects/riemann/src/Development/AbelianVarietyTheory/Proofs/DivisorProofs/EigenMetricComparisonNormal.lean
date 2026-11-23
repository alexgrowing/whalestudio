import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepOfIsEigBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalAdaptedSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixOfAdaptedCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixUniqueUpToTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixGradedQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagBundleFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagBundleFamilyDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagFamilyChernLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagFamilyHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationValuative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationUnfoldingFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfStalkwiseLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfProperInjectivePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationSeparatedProper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationGenericLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSurjectiveLiftAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalOfGenericFibrePullback
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairCovGen

open GlobalTheory.ShFam.Pad.Guard GlobalTheory.TangentOrigin GlobalTheory.FlagSec

section Pull

variable {B Y X : Scheme.{0}} {M : B.Modules} {r : ℕ}

theorem adapted_pull {N : Y.Modules} [N.IsQuasicoherent] {fl : Vert.Flag N r} {W : Y.Opens} {s : Fin r → Γ(N, W)}
    (hs : Adapted fl s) (ρ : X ⟶ Y) :
    Adapted (fl.pull ρ) fun i => QCoh.pullbackSections ρ N (le_refl (ρ ⁻¹ᵁ W)) (s i) := by
  refine ⟨hs.1.pullback ρ, fun k => ?_⟩
  obtain ⟨t, ht, e⟩ := hs.2 k
  have := (fl.isVB k).isQuasicoherent
  refine ⟨_, ht.pullback ρ, fun i => ?_⟩
  exact (QCoh.pullback_map_app_pullbackSections ρ (fl.ι k) _ _).trans (congrArg _ (e i))

theorem flagMat_pull (hM : IsVB M r) (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) {V : B.Opens}
    {f : Fin r → Γ(M, V)} (hf : IsFrame f) (ρ : X ⟶ Y) {K : Type} [CommRing K] [IsLocalRing K] (y : Sp K ⟶ X)
    (hV : ⊤ ≤ ((y ≫ ρ) ≫ π) ⁻¹ᵁ V) {A : Matrix (Fin r) (Fin r) K} (hA : FlagMat hM π fl hf (y ≫ ρ) A) :
    haveI := hM.isQuasicoherent
    FlagMat (hM.pullback π) ρ (fl.pull ρ) (hf.pullback π) y A := by
  have := hM.isQuasicoherent
  have := (hM.pullback π).isQuasicoherent
  obtain ⟨W, s, hWV, hp, hs⟩ := exists_adapted Y _ r fl ((y ≫ ρ) (IsLocalRing.closedPoint K)) (π ⁻¹ᵁ V)
    (hV (Set.mem_univ (IsLocalRing.closedPoint K)))
  have hy : ⊤ ≤ (y ≫ ρ) ⁻¹ᵁ W := (Scheme.preimage_eq_top_of_closedPoint_mem (y ≫ ρ) hp).ge
  have hy' : ⊤ ≤ y ⁻¹ᵁ (ρ ⁻¹ᵁ W) := hy
  have h0 := AdaptMat.flagMat_of_adapted B Y M r hM π fl V f hf K (y ≫ ρ) W hWV hy s hs
  have h1 := AdaptMat.flagMat_of_adapted Y X _ r (hM.pullback π) ρ (fl.pull ρ) _ _ (hf.pullback π) K y (ρ ⁻¹ᵁ W)
    (ρ.preimage_mono hWV) hy' _ (adapted_pull hs ρ)
  have e : (Matrix.of fun i => coordAt (hM.pullback π) ρ (hf.pullback π) y (ρ.preimage_mono hWV) hy'
      (QCoh.pullbackSections ρ _ (le_refl (ρ ⁻¹ᵁ W)) (s i))) =
      Matrix.of fun i => coordAt hM π hf (y ≫ ρ) hWV hy (s i) := by
    ext i b
    exact (congrArg (evalPt y _ hy') ((hf.pullback π).pullback_basis_repr ρ hWV le_rfl (s i) b)).trans
      (evalPt_appLE ρ y W _ le_rfl hy' hy _)
  rw [e] at h1
  obtain ⟨T, hT, hT', rfl⟩ := (flagMat_local B Y M r hM π fl V f hf K (y ≫ ρ) hV).2.1 _ _ h0 hA
  exact h1.mul hT hT'

theorem evalPt_trCo_pull [M.IsQuasicoherent] (π : Y ⟶ B) {V V' : B.Opens} {f : Fin r → Γ(M, V)} {f' : Fin r → Γ(M, V')}
    (hf : IsFrame f) {K : Type} [CommRing K] (y : Sp K ⟶ Y) (z : Sp K ⟶ B) (hz : z = y ≫ π)
    (hy : ⊤ ≤ y ⁻¹ᵁ (π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ V')) (hxx : ⊤ ≤ z ⁻¹ᵁ (V ⊓ V')) (b a : Fin r) :
    evalPt y _ hy (trCo (hf.pullback π) (fun i => QCoh.pullbackSections π M (le_refl (π ⁻¹ᵁ V')) (f' i)) b a) =
      evalPt z _ hxx (trCo hf f' b a) := by
  subst hz
  have h2 : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ V' ≤ π ⁻¹ᵁ (V ⊓ V') := fun p hp => hp
  rw [← evalPt_appLE π y _ _ h2 hy hxx]
  congr 1
  refine Eq.trans ?_ (hf.pullback_basis_repr π inf_le_left h2 _ b)
  unfold trCo
  congr 2
  exact (QCoh.res_pullbackSections π M _ _ _).trans (QCoh.pullbackSections_res π M h2 inf_le_right _).symm

end Pull

open ReciprocityTheory.ChartRestriction.G.PullbackSections MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem exists_comb_vecMul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {K : Type} [CommRing K] (x : Sp K ⟶ X) {r : ℕ}
    {uu v : Fin r → (Sp (DualNumber K) ⟶ t.G.left)}
    (hu : ∀ i, IsTanAtG t x (uu i)) (hv : ∀ i, IsTanAtG t x (v i)) {d : Matrix (Fin r) (Fin r) K}
    (hd : ∀ i, IsCombAtG t x uu (d i) (v i)) (cf : Fin r → K) :
    ∃ w, IsCombAtG t x uu (Matrix.vecMul cf d) w ∧ IsCombAtG t x v cf w := by
  have h (i) : GlobalTheory.LieMet.tanOf (hv i) = ∑ b, d i b • GlobalTheory.LieMet.tanOf (hu b) :=
    (GlobalTheory.LieMet.isComb_iff (fun b => GlobalTheory.LieMet.tanOf (hu b)) _ (GlobalTheory.LieMet.tanOf (hv i))).1 (hd i)
  refine ⟨_, (GlobalTheory.LieMet.isComb_iff (fun b => GlobalTheory.LieMet.tanOf (hu b)) _ _).2 ?_,
    (GlobalTheory.LieMet.isComb_iff (fun b => GlobalTheory.LieMet.tanOf (hv b)) cf _).2 rfl⟩
  simp only [h, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  exact Finset.sum_comm

theorem exists_isFrameSecX {D : D7} {O : Setup D} {c : O.s.Comp} {Bs : Scheme.{0}} (σ : D.host.E →+* ℂ)
    {M : Bs.Modules} (hM : IsVB M (O.S.Dw.mult σ)) {Bg : Scheme.{0}} {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen O.s.T.Z}
    {t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB} (ht : IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t)
    {Y X : Scheme.{0}} {π : Y ⟶ Bs} {ρ : X ⟶ Y} (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) (O.S.Dw.mult σ))
    {G : Scheme.{0}} [IsIntegral G] {j : G ⟶ X} {φ : (O.var c).Fn →+* G.functionField} {jG : G ⟶ Bg}
    (h1 : jG ≫ jB = j ≫ ρ ≫ π) {χ : O.κ.c.F →+* G.functionField} {x : Sp G.functionField ⟶ O.s.T.Z.X}
    (g : EigFrame O.s.T.Z χ x) (hg : (O.Φ.C c).f0.IsMap φ g) (hx : x = (genPt G ≫ jG) ≫ πB ≫ genι O.s.T.Z)
    (hχ : (genPt G ≫ jG) ≫ πB ≫ genStr O.s.T.Z = spMap χ)
    (hA : AgreeAt O.s.T.Z hM jB t π fl false (genPt G ≫ j ≫ ρ) (genPt G ≫ jG) x (g.v σ)) (i : Fin (O.S.Dw.mult σ)) :
    ∃ r, GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM jB πB t π ρ (fl.pull ρ) j φ jG i r := by
  have := hM.isQuasicoherent
  have := (hM.pullback π).isQuasicoherent
  have hx' : genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z = x := (hx.trans (Category.assoc _ _ _)).symm
  have hv : (fun l => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v σ l) = g.v σ := funext fun l => (hg _ l).symm
  have hz : (genPt G ≫ jG) ≫ jB = ((genPt G ≫ j) ≫ ρ) ≫ π := by simp only [Category.assoc, h1]
  have hvi : Indep O.s.T.Z.t x (g.v σ) :=
    indep_of_isEigBasis ⟨fun k => ⟨g.tan _ k, g.eig _ k⟩, fun w hw => g.basis _ w hw.1 hw.2⟩
  have hb (V : Bs.Opens) (f : Fin (O.S.Dw.mult σ) → Γ(M, V)) (hf : IsFrame f)
      (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V) :
      IsEigBasis O.s.T.Z χ x σ (t V f hf G.functionField (genPt G ≫ jG) hxV) := by
    have h1 := ht.1 V f hf G.functionField (genPt G ≫ jG) hxV (χ.comp O.κ.e.toRingHom) (by
      rw [← Category.assoc πB, ← Category.assoc, hχ, ← Spec.map_comp]; rfl)
    have h2 : (χ.comp O.κ.e.toRingHom).comp O.κ.e.symm.toRingHom = χ :=
      RingHom.ext fun z => congrArg χ (O.κ.e.apply_symm_apply z)
    rwa [h2, ← hx] at h1
  have hut := fun V f hf hxV k => ((hb V f hf hxV).1 k).1
  have hT := fun V V' f f' hf hf' hx hx' hxx => ht.2.1 V V' f f' hf hf' G.functionField (genPt G ≫ jG) hx hx' hxx
  rw [← hx] at hT
  have key (V : Bs.Opens) (f : Fin (O.S.Dw.mult σ) → Γ(M, V)) (hf : IsFrame f)
      (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V) :
      ∃ d : Matrix (Fin (O.S.Dw.mult σ)) (Fin (O.S.Dw.mult σ)) G.functionField,
        (∀ i, IsCombAtG O.s.T.Z.t x (t V f hf G.functionField (genPt G ≫ jG) hxV) (d i) (g.v σ i)) ∧
        FlagMat (hM.pullback π) ρ (fl.pull ρ) (hf.pullback π) (genPt G ≫ j) d := by
    choose d hd _ using fun l => (hb V f hf hxV).2 (g.v σ l) ⟨g.tan _ l, g.eig _ l⟩
    refine ⟨Matrix.of d, hd, flagMat_pull hM π fl hf ρ _ (hz ▸ hxV) ?_⟩
    rw [Category.assoc]
    exact hA V f hf hxV (Matrix.of d) hd
  have hA1 (k : Fin (O.S.Dw.mult σ + 1)) (V : Bs.Opens) (f : Fin (O.S.Dw.mult σ) → Γ(M, V)) (hf : IsFrame f)
      (W : X.Opens) (hWV : W ≤ ρ ⁻¹ᵁ (π ⁻¹ᵁ V)) (s : Γ((fl.pull ρ).F k, W)) (hy : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W)
      (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V) :
      ∃ w cf, IsCombAtG O.s.T.Z.t x (t V f hf G.functionField (genPt G ≫ jG) hxV)
          (coordAt (hM.pullback π) ρ (hf.pullback π) (genPt G ≫ j) hWV hy (((fl.pull ρ).ι k).app W s)) w ∧
        IsCombAtG O.s.T.Z.t x (g.v σ) cf w ∧ (∀ l : Fin (O.S.Dw.mult σ), (k : ℕ) ≤ l → cf l = 0) ∧
        ∃ d, FlagMat (hM.pullback π) ρ (fl.pull ρ) (hf.pullback π) (genPt G ≫ j) d ∧
          coordAt (hM.pullback π) ρ (hf.pullback π) (genPt G ≫ j) hWV hy (((fl.pull ρ).ι k).app W s) =
            Matrix.vecMul cf d := by
    obtain ⟨d, h2, h4⟩ := key V f hf hxV
    obtain ⟨cf, hc1, hc2⟩ := h4.2 k W hWV s hy
    obtain ⟨w, hw1, hw2⟩ := exists_comb_vecMul _ x (hut V f hf hxV) (g.tan _) h2 cf
    exact ⟨w, cf, hc2 ▸ hw1, hw2, hc1, d, h4, hc2⟩
  have main := fun ch : (((fl.pull ρ).root i).pull j).ι => exists_unit
    (fun val : G.functionField => ∃ (V : Bs.Opens) (f : _ → Γ(M, V)) (hf : IsFrame f) (W : X.Opens)
      (hW : W ≤ (ch PUnit.unit).U) (hWV : W ≤ ρ ⁻¹ᵁ (π ⁻¹ᵁ V)) (s : Γ((fl.pull ρ).F i.succ, W))
      (_ : ((fl.pull ρ).π i).app W s = Twist.resM _ hW ((ch PUnit.unit).e 0))
      (hy : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V)
      (w : Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left) (cf : Fin (O.S.Dw.mult σ) → G.functionField),
      IsCombAtG O.s.T.Z.t x (t V f hf G.functionField (genPt G ≫ jG) hxV)
        (coordAt (hM.pullback π) ρ (hf.pullback π) (genPt G ≫ j) hWV hy (((fl.pull ρ).ι i.succ).app W s)) w ∧
      IsCombAtG O.s.T.Z.t x (g.v σ) cf w ∧ cf i = val)
    (by
      rintro _ ⟨V, f, hf, W, hW, hWV, s, hs, hy, hxV, w, cf, hw, hc, rfl⟩
      obtain ⟨w', cf', hw', hc', -, d, hd, e⟩ := hA1 i.succ V f hf W hWV s hy hxV
      obtain rfl := comb_unique (hut V f hf hxV) hw hw'
      rw [hvi _ _ _ hc hc']
      exact FlagMat.coeff_ne_zero _ _ _ _ (hM.pullback π) ρ (fl.pull ρ) _ _ (hf.pullback π) _ _ _ hd i
        (ch PUnit.unit) W hW hWV s hs hy cf' e)
    (by
      rintro _ _ ⟨V, f, hf, W, hW, hWV, s, hs, hy, hxV, w, cf, hw, hc, rfl⟩
        ⟨V', f', hf', W', hW', hWV', s', hs', hy', hxV', w', cf', hw', hc', rfl⟩
      have hy'' : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ (W ⊓ W') := fun p hp => ⟨hy hp, hy' hp⟩
      have hxx : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ (V ⊓ V') := fun p hp => ⟨hxV hp, hxV' hp⟩
      have hyy : ⊤ ≤ ((genPt G ≫ j) ≫ ρ) ⁻¹ᵁ (π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ V') := fun p hp => ⟨hWV (hy hp), hWV' (hy' hp)⟩
      obtain ⟨s₀, hs₀⟩ := coord_rel ρ (fl.pull ρ) (genPt G ≫ j) _ rfl i _ (hf.pullback π) (hf'.pullback π) hW hW' hWV
        hWV' s s' hs hs' hy hy' hy'' hyy
      simp only [evalPt_trCo_pull π hf _ _ hz hyy hxx] at hs₀
      obtain ⟨w₀, d, hw₀, hd, h0, -⟩ := hA1 i.castSucc V f hf _ (inf_le_left.trans hWV) s₀ hy'' hxV
      rw [coeff_eq (hut V f hf hxV) (g.tan _) hvi (hT V V' f f' hf hf' hxV hxV' hxx) hs₀ hw hc hw' hc' hw₀ hd,
        Pi.add_apply, h0 i le_rfl, add_zero])
  choose r hr using main
  refine ⟨r, fun ch V f hf W hW hWV s hs hy hxV => ?_⟩
  obtain ⟨w, cf, hw, hc, h0, -⟩ := hA1 i.succ V f hf W hWV s hy hxV
  intro aG uu v x'
  have hv' : v = g.v σ := hv
  have hx'' : x' = x := hx'
  rw [hv', hx'']
  exact ⟨w, cf, hw, hc, hr ch _ ⟨V, f, hf, W, hW, hWV, s, hs, hy, hxV, w, cf, hw, hc, rfl⟩, fun k hk => h0 k hk⟩

set_option maxHeartbeats 1000000 in

theorem exists_map {D : D7} {O : Setup D} (c : O.s.Comp) {Bs : Scheme.{0}} {q : Bs ⟶ Sp (𝓞 D.what₂.LL)}
    {E : (D.host.E →+* ℂ) → Bs.Modules} (hE : ∀ σ, IsVB (E σ) (O.S.Dw.mult σ))
    {Bg : Scheme.{0}} {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen O.s.T.Z} (u : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB)
    (hpB : IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    (hfB : IsFinite πB) (hrg : Set.range πB = Set.range (O.Φ.C c).π)
    (hLF : ∀ σ, IsLieFrames O.s.T.Z O.κ.e jB πB (E σ) _ σ false (u σ)) {Y₀ : Scheme.{0}} {π₀ : Y₀ ⟶ Bs}
    (fl₀ : ∀ σ, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E σ)) (O.S.Dw.mult σ))
    (hfb : IsFlagBundle π₀ E O.S.Dw.mult fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) {G : Scheme.{0}} [IsIntegral G] {j : G ⟶ Y₀} {s : G ⟶ Sp D.what₂.LL}
    (hpb : IsPullback j s (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    {jG : G ⟶ Bg} (hjG : jG ≫ jB = j ≫ π₀) (hs : jG ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom = s) :
    ∃ (πG : G ⟶ (O.var c).X) (φ : (O.var c).Fn →+* G.functionField),
      jG ≫ πB = πG ≫ (O.Φ.C c).π ∧ πG ≫ (O.var c).str = s ∧ IsFinite πG ∧ Surjective πG ∧
      G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ∧
      ∃ (χ : O.κ.c.F →+* G.functionField) (x : Sp G.functionField ⟶ O.s.T.Z.X) (g : EigFrame O.s.T.Z χ x),
        (O.Φ.C c).f0.IsMap φ g ∧
        Bears O.s.T.Z id (fun _ => false) (fun _ => rfl) hE jB πB u π₀ fl₀ (genPt G ≫ j) (genPt G ≫ jG) g := by
  have hr : ∀ σ : D.host.E →+* ℂ, O.S.Dw.mult σ = O.S.Dw.mult (id σ) := fun _ => rfl
  have hemb : Function.Bijective (id : (D.host.E →+* ℂ) → (D.host.E →+* ℂ)) := Function.bijective_id
  obtain ⟨γ, hγ⟩ : ∃ γ : G ⟶ gen O.s.T.Z, γ = jG ≫ πB := ⟨_, rfl⟩
  let Br : ∀ (K : Type) [CommRing K], (Sp K ⟶ G) → ∀ (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X),
      EigFrame O.s.T.Z χ x → Prop := fun K _ z χ x g =>
    Bears O.s.T.Z id (fun _ => false) hr hE jB πB u π₀ fl₀ (z ≫ j) (z ≫ jG) g
  have hyj : ∀ {K : Type} [CommRing K] (z : Sp K ⟶ G), (z ≫ j) ≫ π₀ = (z ≫ jG) ≫ jB := fun z => by
    simp only [Category.assoc, hjG]
  have P0 : ∀ (K : Type) [CommRing K] (z : Sp K ⟶ G) (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X)
      (g : EigFrame O.s.T.Z χ x), Br K z χ x g → x = z ≫ γ ≫ genι O.s.T.Z ∧ z ≫ γ ≫ genStr O.s.T.Z = spMap χ := by
    intro K _ z χ x g hb
    refine ⟨?_, ?_⟩
    · rw [hb.2.1]; simp only [hγ, Category.assoc]
    · rw [← hb.2.2.1]; simp only [hγ, Category.assoc]
  have P1 : ∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : O.κ.c.F →+* K),
      z ≫ γ ≫ genStr O.s.T.Z = spMap χ → ∃ g : EigFrame O.s.T.Z χ (z ≫ γ ≫ genι O.s.T.Z), Br K z χ _ g := by
    intro K _ _ z χ hz
    exact GlobalTheory.FlagCls.exists_bears _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF hemb K (z ≫ j) (z ≫ jG) χ (hyj z)
      (by simpa only [hγ, Category.assoc] using hz) _ (by simp only [hγ, Category.assoc])
  have P2 : ∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X)
      (g : EigFrame O.s.T.Z χ x) (K' : Type) [CommRing K'] (ψ : K →+* K') (χ' : O.κ.c.F →+* K')
      (x' : Sp K' ⟶ O.s.T.Z.X) (g' : EigFrame O.s.T.Z χ' x') (t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → K'ˣ),
      Br K z χ x g → g.Tri ψ g' t → Br K' (spMap ψ ≫ z) χ' x' g' := by
    intro K _ _ z χ x g K' _ ψ χ' x' g' t hb ht
    have := GlobalTheory.FlagCls.BaseChange.bears_tri _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF K (z ≫ j) (z ≫ jG) χ x g K' ψ χ' x' g' t hb ht
    simpa only [Br, Category.assoc] using this
  have P3 : ∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X)
      (g g' : EigFrame O.s.T.Z χ x), Br K z χ x g → Br K z χ x g' →
      ∃ t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → Kˣ, g.Tri (RingHom.id K) g' t := by
    intro K _ _ z χ x g g' hb hb'
    exact GlobalTheory.FlagCls.BorneUnique.tri_of_bears _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF hemb.2 K (z ≫ j) (z ≫ jG) χ x g g' hb hb'
  have hsep : IsSeparated (genStr O.s.T.Z) := by
    haveI : IsProper O.s.T.Z.s := GlobalTheory.CommonModel.isProper_of_isProjOver O.s.T.Z.proj
    infer_instance
  have hnG : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G :=
    GlobalTheory.FlagCls.isNormalScheme_of_isPullback_fractionField (𝓞 D.what₂.LL) D.what₂.LL Y₀ G (π₀ ≫ q) j s hpb n₀
  have hrng : Set.range γ ⊆ Set.range (O.Φ.C c).π := by
    rintro _ ⟨w, rfl⟩
    rw [← hrg, hγ]
    exact ⟨jG w, rfl⟩
  have hL : ∀ (K : Type) [Field K] (χ : O.κ.c.F →+* K) (x : Sp K ⟶ gen O.s.T.Z), x ≫ genStr O.s.T.Z = spMap χ →
      Set.range x ⊆ Set.range (O.Φ.C c).π → ∀ g : EigFrame O.s.T.Z χ (x ≫ genι O.s.T.Z),
      ∃! p : Sp K ⟶ (O.Φ.C c).Y.X, p ≫ (O.Φ.C c).π = x ∧ (O.Φ.C c).Carries p g := fun K _ χ x hx hx' g =>
    GlobalTheory.FlagCls.Lift.lifts_field _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ _ O.Φ c K χ x hx hx' g

  obtain ⟨χη, hχη⟩ : ∃ χ : O.κ.c.F →+* G.functionField,
      GlobalTheory.FlagCov.genPt G ≫ γ ≫ genStr O.s.T.Z = spMap χ := ⟨_, (Spec.map_preimage _).symm⟩
  obtain ⟨gη, hgη⟩ := P1 G.functionField (GlobalTheory.FlagCov.genPt G) χη hχη
  obtain ⟨pη, ⟨hpη, hcη⟩, -⟩ := hL G.functionField χη (GlobalTheory.FlagCov.genPt G ≫ γ) (by simpa only [Category.assoc] using hχη)
    (fun _ ⟨w, hw⟩ => hw ▸ hrng ⟨_, rfl⟩) gη
  have hCsep : IsSeparated (O.Φ.C c).π := by
    haveI : IsSeparated ((O.Φ.C c).π ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) := by
      rw [(O.Φ.C c).π_str]; infer_instance
    exact IsSeparated.of_comp _ (genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom)
  have hClft : LocallyOfFiniteType (O.Φ.C c).π := by
    haveI : LocallyOfFiniteType ((O.Φ.C c).π ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) := by
      rw [(O.Φ.C c).π_str]; infer_instance
    exact locallyOfFiniteType_of_comp _ (genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom)
  have hq := GlobalTheory.FlagClsLoc.main _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) hsep (fun K _ χ x hx hx' g => hL K χ x hx hx' g)
    G γ Br P0 P1 P2 P3 hnG hrng pη χη gη hgη hpη hcη
  obtain ⟨πG, hπη, hπG⟩ := GlobalTheory.FlagCls.exists_hom_of_forall_stalk G (O.Φ.C c).Y.X (gen O.s.T.Z) γ (O.Φ.C c).π pη hpη hq
  have hcar := GlobalTheory.FlagCls.carries_of_generic _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) G γ Br P0 P1 P2 P3 πG χη gη hgη hπG (by rw [hπη]; exact hcη)
  have hlift : ∀ {K : Type} [CommRing K] (y : Sp K ⟶ Y₀) (xb : Sp K ⟶ Bg), y ≫ π₀ = xb ≫ jB →
      ∃ z : Sp K ⟶ G, z ≫ j = y ∧ z ≫ jG = xb := by
    intro K _ y xb hy
    have hw : y ≫ π₀ ≫ q = (xb ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) ≫
        spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) := by
      rw [← Category.assoc, hy, Category.assoc, hpB.w]; simp only [Category.assoc]
    refine ⟨hpb.lift y _ hw, hpb.lift_fst _ _ _, ?_⟩
    apply hpB.hom_ext
    · rw [Category.assoc, hjG, ← Category.assoc, hpb.lift_fst, hy]
    · rw [Category.assoc, hs, hpb.lift_snd]
  have hsurj : Surjective πG := by
    constructor
    intro y
    let K := AlgebraicClosure ((O.Φ.C c).Y.X.residueField y)
    let p : Sp K ⟶ (O.Φ.C c).Y.X :=
      spMap (algebraMap ((O.Φ.C c).Y.X.residueField y) K) ≫ (O.Φ.C c).Y.X.fromSpecResidueField y
    have hp : p (IsLocalRing.closedPoint K) = y := Scheme.fromSpecResidueField_apply y _
    obtain ⟨χp, hχp⟩ : ∃ χ : O.κ.c.F →+* K, p ≫ (O.Φ.C c).π ≫ genStr O.s.T.Z = spMap χ :=
      ⟨_, (Spec.map_preimage _).symm⟩
    obtain ⟨gp, hgp⟩ := GlobalTheory.CarryAll.carry_some _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) K χp p hχp
    obtain ⟨xb, hxb⟩ := GlobalTheory.FlagCls.finite_exists_lift_algClosed_point Bg (gen O.s.T.Z) πB hfB K (p ≫ (O.Φ.C c).π)
      (by rw [hrg]; exact ⟨p (IsLocalRing.closedPoint K), rfl⟩)
    obtain ⟨y', hy', -⟩ := GlobalTheory.FlagCls.Lift.existsUnique_bears _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF hfb K xb χp _ gp (by simp only [← Category.assoc, hxb])
      (by simp only [← Category.assoc, hxb]; simpa only [Category.assoc] using hχp)
    obtain ⟨z, hzj, hzG⟩ := hlift y' xb hy'.1
    have hbz : Br K z χp _ gp := by simp only [Br, hzj, hzG]; exact hy'
    have hc := hcar K z χp _ gp hbz
    have e1 := (hL K χp (p ≫ (O.Φ.C c).π) (by simpa only [Category.assoc] using hχp)
      (by rintro _ ⟨w, rfl⟩; exact ⟨p w, rfl⟩) gp).unique
      ⟨by rw [Category.assoc, hπG, hγ, ← Category.assoc, hzG, hxb], hc⟩ ⟨rfl, hgp⟩
    refine ⟨z (IsLocalRing.closedPoint K), ?_⟩
    have e2 : (z ≫ πG) (IsLocalRing.closedPoint K) = p (IsLocalRing.closedPoint K) := by rw [e1]
    exact (Scheme.Hom.comp_apply z πG _).symm.trans (e2.trans hp)
  have hsP : IsProper s := by
    haveI : IsProper (π₀ ≫ q) := GlobalTheory.CommonModel.isProper_of_isProjOver ar₀.isProjOver
    exact MorphismProperty.of_isPullback (P := @IsProper) hpb inferInstance
  have hstr : πG ≫ (O.var c).str = s := by
    rw [← hs, ← (O.Φ.C c).π_str, ← Category.assoc, hπG, hγ]; simp only [Category.assoc]
  have hπP : IsProper πG := by
    haveI : IsProper (πG ≫ (O.var c).str) := by rw [hstr]; exact hsP
    exact IsProper.of_comp πG (O.var c).str
  have hfin : IsFinite πG := GlobalTheory.FlagCls.isFinite_of_isProper_of_fieldPoints G (O.Φ.C c).Y.X Bg (gen O.s.T.Z) πG jG πB (O.Φ.C c).π (by rw [hπG, hγ]) hfB hπP (by
    intro K _ z z' h1 h2
    obtain ⟨χ, hχ⟩ : ∃ χ : O.κ.c.F →+* K, z ≫ γ ≫ genStr O.s.T.Z = spMap χ := ⟨_, (Spec.map_preimage _).symm⟩
    obtain ⟨g, hg⟩ := P1 K z χ hχ
    have hx' : z ≫ γ ≫ genι O.s.T.Z = (z' ≫ jG) ≫ πB ≫ genι O.s.T.Z := by
      rw [← h2, hγ]; simp only [Category.assoc]
    obtain ⟨g', hg'⟩ := GlobalTheory.FlagCls.exists_bears _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF hemb K (z' ≫ j) (z' ≫ jG) χ (hyj z')
      (by rw [← h2, ← hχ, hγ]; simp only [Category.assoc]) _ hx'
    have c1 := hcar K z χ _ g hg
    have c2 := hcar K z' χ _ g' hg'
    rw [← h1] at c2
    obtain ⟨t, ht⟩ := GlobalTheory.FlagCls.carries_tri_same _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) K χ _ g' g (z ≫ πG) c2 c1
    have hb := GlobalTheory.FlagCls.BaseChange.bears_tri _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF K (z' ≫ j) (z' ≫ jG) χ _ g' K (RingHom.id K) χ _ g t hg' ht
    rw [show spMap (RingHom.id K) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.id_comp, ← h2] at hb
    have hyy : z ≫ j = z' ≫ j := by
      obtain ⟨y₀, -, hu⟩ := GlobalTheory.FlagCls.Lift.existsUnique_bears _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF hfb K (z ≫ jG) χ _ g (by rw [hγ]; simp only [Category.assoc])
        (by rw [← hχ, hγ]; simp only [Category.assoc])
      exact (hu _ hg).trans (hu _ hb).symm
    apply hpb.hom_ext hyy
    rw [← hs, ← Category.assoc, h2, Category.assoc])
  have hgen : πG (genericPoint G) = genericPoint (O.var c).X := by
    obtain ⟨w, hw⟩ := hsurj.surj (genericPoint (O.var c).X)
    have h1 : πG (genericPoint G) ⤳ πG w := (genericPoint_specializes w).map πG.continuous
    rw [hw] at h1
    exact (h1.antisymm (genericPoint_specializes _)).eq
  obtain ⟨φ, hφ⟩ := GlobalTheory.FlagGenFib.exists_ringHom_of_generic πG hgen
  have hφ' : GlobalTheory.FlagCov.genPt G ≫ πG = spMap φ ≫ genericPt (O.var c) := hφ
  have hχφ : χη = φ.comp (constF O.κ.e (O.var c)) := by
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    have e1 : GlobalTheory.FlagCov.genPt G ≫ γ ≫ genStr O.s.T.Z =
        spMap φ ≫ (genericPt (O.var c) ≫ (O.Φ.C c).π) ≫ genStr O.s.T.Z := by
      rw [← hπG]
      simp only [← Category.assoc]
      rw [hφ']
    rw [← hχη, e1, GlobalTheory.ShFam.TieBase.genericPt_str O.κ.e (O.var c) (O.Φ.C c).π (O.Φ.C c).π_str]
    exact (Spec.map_comp _ _).symm
  obtain ⟨g0, hg0⟩ := GlobalTheory.ShFam.EigFrame.exists_isMap (O.Φ.C c).f0 φ (φ' := χη)
    (x' := GlobalTheory.FlagCov.genPt G ≫ γ ≫ genι O.s.T.Z) hχφ (by
      rw [← hπG]; simp only [← Category.assoc]; rw [hφ'])
  have hc0 : (O.Φ.C c).Carries (GlobalTheory.FlagCov.genPt G ≫ πG) g0 := by
    rw [hφ']
    exact GlobalTheory.FlagCls.carries_genericPt_of_isMap _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) G.functionField φ χη _ g0 hχφ
      (by rw [← hπG]; simp only [← Category.assoc]; rw [hφ']) hg0
  have hcη' := hcar G.functionField (GlobalTheory.FlagCov.genPt G) χη _ gη hgη
  obtain ⟨t0, ht0⟩ := GlobalTheory.FlagCls.carries_tri_same _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) G.functionField χη _ gη g0 _ hcη' hc0
  have hb0 := P2 G.functionField (GlobalTheory.FlagCov.genPt G) χη _ gη G.functionField (RingHom.id _) χη _ g0 t0 hgη ht0
  rw [show spMap (RingHom.id G.functionField) = 𝟙 _ from Spec.map_id _, Category.id_comp] at hb0
  exact ⟨πG, φ, by rw [hπG, hγ], hstr, hfin, hsurj, hφ, χη, _, g0, hg0, hb0⟩

theorem exists_genericFibre : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
  ∀ (D : D7) (O : Setup D), O.Core → ∀ R : ℝ, 2 ≤ R → ∀ (c : O.s.Comp) (B : Scheme.{0}) [IsIntegral B]
    (q : B ⟶ Sp (𝓞 D.what₂.LL)) (E E' : (D.host.E →+* ℂ) → B.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ))
    (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (u : ∀ σ, E σ ⟶ E' σ),
    IsArithVar q (dimGr D.what₂.Tau O.N O.j) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B →
    (∀ σ, IsoHom (h σ) (h' σ) (u σ)) →
    ∀ (Bg : Scheme.{0}) (jB : Bg ⟶ B) (πB : Bg ⟶ gen O.s.T.Z) (t : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB)
      (t' : ∀ σ, FrAssign O.s.T.Z (E' σ) (O.S.Dw.mult σ) jB) (G : ∀ σ', EigMet O.s.T.Z σ'),
    GlobalTheory.PairCov.PairWit O R c q E E' h h' u jB πB t t' G →
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (π : Y ⟶ B)
      (fl : ∀ σ, Vert.Flag ((Scheme.Modules.pullback π).obj (E σ)) (O.S.Dw.mult σ)),
    IsFlagBundle π E O.S.Dw.mult fl → IsArithVar (π ≫ q) (O.var c).dim → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y →
    ∀ (X Gs : Scheme.{0}) [IsIntegral X] [IsIntegral Gs] (ρ : X ⟶ Y) (j : Gs ⟶ X) (s : Gs ⟶ Sp D.what₂.LL),
      IsPullback (j ≫ ρ) s (π ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) →
      IsPullback j s (ρ ≫ π ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) →
    ∃ (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg)
      (r : ∀ σ i, ((((fl σ).pull ρ).root i).pull j).ι → Gs.functionFieldˣ),
      GlobalTheory.PairCov.CovCommon O R c q jB πB G π ρ j πG φ jG ∧
      ∀ σ i, GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ (h σ).isVB jB πB (t σ) π ρ ((fl σ).pull ρ) j φ jG i (r σ i) := by
  intro _ _ _ D O _ R _ c B _ q E E' h h' u _ _ _ Bg jB πB t t' G hW Y _ π fl hfb ar nY X Gs _ _ ρ j s hp hp'
  obtain ⟨hpB, hfB, hrg, hLF, -, -, -, -, hm, -⟩ := hW
  have hw : ((j ≫ ρ) ≫ π) ≫ q = s ≫ spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) := by
    rw [← hp.w]; simp only [Category.assoc]
  have hj := hpB.lift_fst _ _ hw
  obtain ⟨πG, φ, h1, h2, h3, h4, h5, χ, x, g, hg, -, hx, hχ, hA⟩ := exists_map c (fun σ => (h σ).isVB) t hpB hfB hrg hLF
    fl hfb ar nY hp hj (hpB.lift_snd _ _ hw)
  replace hj := hj.trans (Category.assoc _ _ _)
  choose r hr using fun σ i => exists_isFrameSecX σ (h σ).isVB (hLF σ) (fl σ) hj g hg hx hχ (hA σ) i
  exact ⟨πG, φ, _, r, ⟨hpB, hfB, hrg, hm, h2 ▸ hp', h3, h4, h5, hj, h1⟩, hr⟩

end GlobalTheory.PairCovGen

end
