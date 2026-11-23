import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalAdaptedSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixOfAdaptedCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixUniqueUpToTriangularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixChangeOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixGradedQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfInvertibleMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixStepIsomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixTransportFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagBundleRankDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagBundleFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagBundleFamilyDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagFamilyChernLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagFamilyHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFramesPullbackGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbBBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationPointExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationValuativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationUnfoldingFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeCriterionExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfStalkwiseLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfProperInjectivePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationSeparatedProperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationGenericLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSurjectiveLiftAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationFunctionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalOfGenericFibrePullbackStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.BcRead.classifyingMap : Hypotheses2 → HypothesesH → RegularAlteration →
  ∀ (D : D7) (O : Setup D) (hO : O.Core) (P : Finset ℕ) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp)
    (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB)
    (hG : GlobalTheory.BcRead.LieGen O c q E jB πB u) (hF : GlobalTheory.BcRead.LieFin O P E jB πB u)
    (hI : GlobalTheory.BcRead.LieInf O R c q E h jB πB u)
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀)
    (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (s : G ⟶ Sp D.what₂.LL)
    (_ : IsPullback j s (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    (jG : G ⟶ Bg) (_ : jG ≫ jB = j ≫ π₀) (_ : jG ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom = s),
  ∃ (πG : G ⟶ (O.var c).X) (φ : (O.var c).Fn →+* G.functionField),
    jG ≫ πB = πG ≫ (O.Φ.C c).π ∧ IsFinite πG ∧ Surjective πG ∧
    G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ∧
    ∀ a (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)),
      GlobalTheory.FlagCov.FlagAgree (fun a => (h a).isVB) jB πB u π₀ fl₀ j φ jG a hr := by
  intro P2 PH RA D O hO P R hR c Bs _ q arq nBs E h H Bg jB πB u hG hF hI Y₀ _ π₀ fl₀ hfb ar₀ n₀ G _ j s hpb jG hjG hs
  obtain ⟨_, _, hIa⟩ := hI
  have hr : ∀ a, rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a) := fun a => (hIa a).1
  have hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a) := fun a => (h a).isVB
  have hLF := hG.2.2.2
  have hemb := GlobalTheory.T.bijective_embB D
  obtain ⟨γ, hγ⟩ : ∃ γ : G ⟶ gen O.s.T.Z, γ = jG ≫ πB := ⟨_, rfl⟩
  let Br : ∀ (K : Type) [CommRing K], (Sp K ⟶ G) → ∀ (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X),
      EigFrame O.s.T.Z χ x → Prop := fun K _ z χ x g =>
    Bears O.s.T.Z (embB D) (fun a => !a.2) hr hE jB πB u π₀ fl₀ (z ≫ j) (z ≫ jG) g
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
    exact GlobalTheory.T.toroidal_flag_bundle_family _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ (embB D) (fun a => !a.2) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF hemb K (z ≫ j) (z ≫ jG) χ (hyj z)
      (by simpa only [hγ, Category.assoc] using hz) _ (by simp only [hγ, Category.assoc])
  have P2 : ∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X)
      (g : EigFrame O.s.T.Z χ x) (K' : Type) [CommRing K'] (ψ : K →+* K') (χ' : O.κ.c.F →+* K')
      (x' : Sp K' ⟶ O.s.T.Z.X) (g' : EigFrame O.s.T.Z χ' x') (t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → K'ˣ),
      Br K z χ x g → g.Tri ψ g' t → Br K' (spMap ψ ≫ z) χ' x' g' := by
    intro K _ _ z χ x g K' _ ψ χ' x' g' t hb ht
    have := GlobalTheory.T.toroidal_flag_bundle_family_dual _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ (embB D) (fun a => !a.2) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF K (z ≫ j) (z ≫ jG) χ x g K' ψ χ' x' g' t hb ht
    simpa only [Br, Category.assoc] using this
  have P3 : ∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X)
      (g g' : EigFrame O.s.T.Z χ x), Br K z χ x g → Br K z χ x g' →
      ∃ t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → Kˣ, g.Tri (RingHom.id K) g' t := by
    intro K _ _ z χ x g g' hb hb'
    exact GlobalTheory.T.toroidal_flag_family_chern_limit _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ (embB D) (fun a => !a.2) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF hemb.2 K (z ≫ j) (z ≫ jG) χ x g g' hb hb'

  have hsep : IsSeparated (genStr O.s.T.Z) := by
    haveI : IsProper O.s.T.Z.s := GlobalTheory.CommonModel.isProper_of_isProjOver O.s.T.Z.proj
    infer_instance
  have hnG : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G :=
    GlobalTheory.T.normal_of_generic_fibre_pullback (𝓞 D.what₂.LL) D.what₂.LL Y₀ G (π₀ ≫ q) j s hpb n₀
  have hrng : Set.range γ ⊆ Set.range (O.Φ.C c).π := by
    rintro _ ⟨w, rfl⟩
    rw [← hG.2.2.1, hγ]
    exact ⟨jG w, rfl⟩
  have hL : ∀ (K : Type) [Field K] (χ : O.κ.c.F →+* K) (x : Sp K ⟶ gen O.s.T.Z), x ≫ genStr O.s.T.Z = spMap χ →
      Set.range x ⊆ Set.range (O.Φ.C c).π → ∀ g : EigFrame O.s.T.Z χ (x ≫ genι O.s.T.Z),
      ∃! p : Sp K ⟶ (O.Φ.C c).Y.X, p ≫ (O.Φ.C c).π = x ∧ (O.Φ.C c).Carries p g := fun K _ χ x hx hx' g =>
    GlobalTheory.T.uniformization_unfolding_free _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ _ O.Φ c K χ x hx hx' g

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
  have hq := GlobalTheory.T.flag_compactification_separated_proper _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) hsep (fun K _ χ x hx hx' g => hL K χ x hx hx' g)
    G γ Br P0 P1 P2 P3 hnG hrng pη χη gη hgη hpη hcη
  obtain ⟨πG, hπη, hπG⟩ := GlobalTheory.T.extension_of_stalkwise_lifts G (O.Φ.C c).Y.X (gen O.s.T.Z) γ (O.Φ.C c).π pη hpη hq
  have hcar := GlobalTheory.T.flag_compactification_generic_lift _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) G γ Br P0 P1 P2 P3 πG χη gη hgη hπG (by rw [hπη]; exact hcη)

  have hlift : ∀ {K : Type} [CommRing K] (y : Sp K ⟶ Y₀) (xb : Sp K ⟶ Bg), y ≫ π₀ = xb ≫ jB →
      ∃ z : Sp K ⟶ G, z ≫ j = y ∧ z ≫ jG = xb := by
    intro K _ y xb hy
    have hw : y ≫ π₀ ≫ q = (xb ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) ≫
        spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) := by
      rw [← Category.assoc, hy, Category.assoc, hG.1.w]; simp only [Category.assoc]
    refine ⟨hpb.lift y _ hw, hpb.lift_fst _ _ _, ?_⟩
    apply hG.1.hom_ext
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
    obtain ⟨xb, hxb⟩ := GlobalTheory.T.finite_surjective_lift_alg_closed Bg (gen O.s.T.Z) πB hG.2.1 K (p ≫ (O.Φ.C c).π)
      (by rw [hG.2.2.1]; exact ⟨p (IsLocalRing.closedPoint K), rfl⟩)
    obtain ⟨y', hy', -⟩ := GlobalTheory.T.toroidal_flag_family_height _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ (embB D) (fun a => !a.2) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF hfb K xb χp _ gp (by simp only [← Category.assoc, hxb])
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
  have hfin : IsFinite πG := GlobalTheory.T.finite_of_proper_injective_points G (O.Φ.C c).Y.X Bg (gen O.s.T.Z) πG jG πB (O.Φ.C c).π (by rw [hπG, hγ]) hG.2.1 hπP (by
    intro K _ z z' h1 h2
    obtain ⟨χ, hχ⟩ : ∃ χ : O.κ.c.F →+* K, z ≫ γ ≫ genStr O.s.T.Z = spMap χ := ⟨_, (Spec.map_preimage _).symm⟩
    obtain ⟨g, hg⟩ := P1 K z χ hχ
    have hx' : z ≫ γ ≫ genι O.s.T.Z = (z' ≫ jG) ≫ πB ≫ genι O.s.T.Z := by
      rw [← h2, hγ]; simp only [Category.assoc]
    obtain ⟨g', hg'⟩ := GlobalTheory.T.toroidal_flag_bundle_family _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ (embB D) (fun a => !a.2) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF hemb K (z' ≫ j) (z' ≫ jG) χ (hyj z')
      (by rw [← h2, ← hχ, hγ]; simp only [Category.assoc]) _ hx'
    have c1 := hcar K z χ _ g hg
    have c2 := hcar K z' χ _ g' hg'
    rw [← h1] at c2
    obtain ⟨t, ht⟩ := GlobalTheory.T.flag_compactification_valuative _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) K χ _ g' g (z ≫ πG) c2 c1
    have hb := GlobalTheory.T.toroidal_flag_bundle_family_dual _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ (embB D) (fun a => !a.2) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF K (z' ≫ j) (z' ≫ jG) χ _ g' K (RingHom.id K) χ _ g t hg' ht
    rw [show spMap (RingHom.id K) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.id_comp, ← h2] at hb
    have hyy : z ≫ j = z' ≫ j := by
      obtain ⟨y₀, -, hu⟩ := GlobalTheory.T.toroidal_flag_family_height _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ (embB D) (fun a => !a.2) hr _ _ _ _ hE jB πB u π₀ fl₀ hLF hfb K (z ≫ jG) χ _ g (by rw [hγ]; simp only [Category.assoc])
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
    exact GlobalTheory.T.flag_compactification_function_field _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) G.functionField φ χη _ g0 hχφ
      (by rw [← hπG]; simp only [← Category.assoc]; rw [hφ']) hg0
  have hcη' := hcar G.functionField (GlobalTheory.FlagCov.genPt G) χη _ gη hgη
  obtain ⟨t0, ht0⟩ := GlobalTheory.T.flag_compactification_valuative _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) G.functionField χη _ gη g0 _ hcη' hc0
  have hb0 := P2 G.functionField (GlobalTheory.FlagCov.genPt G) χη _ gη G.functionField (RingHom.id _) χη _ g0 t0 hgη ht0
  rw [show spMap (RingHom.id G.functionField) = 𝟙 _ from Spec.map_id _, Category.id_comp] at hb0
  have hag := GlobalTheory.T.lie_frames_pullback_generic D O c Bs E hE Bg jB πB u hLF hr Y₀ π₀ fl₀ G j jG φ χη _ g0 hg0 hb0
  refine ⟨πG, φ, ?_, hfin, hsurj, hφ, fun a _ => hag a⟩
  rw [hπG, hγ]
