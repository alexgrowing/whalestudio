import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplePoleAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalBoundaryLocalEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCanonicalDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtendMulSimplePoleOfVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsVanishingOfSimplePoleMulExtendsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogCanonicalReflexive

theorem logCanon_refl : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z hF hKS hV ω₀ b s hs m
  have hoff : ∀ z, z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off ↔ z ∈ U₀ TF.X Z := fun z => by
    rw [Modif.off_eq]; rfl
  haveI : IsReduced (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X := isReduced_Y₀ TF.X Z
  have hdense : Dense ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off : Set (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) := by
    rw [Modif.off_eq]; exact (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).dense
  have hpole : SimplePoleAlong (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs) ω₀.ω := by
    intro y hy
    have hy' : y ∉ U₀ TF.X Z := fun h => hy ((hoff y).2 h)
    obtain ⟨V, hyV, t, h1, h2⟩ := GlobalTheory.T.toroidal_boundary_local_equation hP E H Dw l Xo c TF Z hF hV y hy'
    obtain ⟨V', hyV', hle, i, j, u, hi, hj, hu, hpl⟩ :=
      GlobalTheory.T.kodaira_spencer_canonical_divisor hP hG E H Dw l Xo c TF Z hF hKS hV ω₀ y hy' V hyV t h1 h2
    refine ⟨V', hyV', (i, j), fun z hz => ⟨hi hz, (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).mem _ _ _).2 (hj hz)⟩,
      fun z hz => (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).mem _ _ _).2 (hj hz),
      fun z hz => ⟨hi hz, (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).mem _ _ _).2 (hj hz)⟩,
      resG _ hle t, u, fun z hz => ?_, hu, fun W hW f hf z hz => ?_, fun z hz ho => ?_⟩
    · erw [ger_resG, hoff]; exact h1 z (hle hz)
    · erw [ger_resG]
      exact h2 W (hW.trans hle) f (fun z hz hz' => hf z hz fun h => hz' ((hoff z).1 h)) z hz
    · erw [ger_resG]; exact hpl z hz ho _
  refine ⟨fun ⟨g, hg, e⟩ => ?_, fun ⟨G, hG⟩ => ?_⟩
  · obtain ⟨G, hG'⟩ := GlobalTheory.T.exists_extend_mul_simplePole_of_vanishing hdense _ ω₀.ω hpole (H0.pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top g) (fun y hy i hi => by
      have e := H0.germ_pull (p := str₀ TF.X Z) (B := L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top i y (memTop y) hi g
      rw [e]
      have h := hg y (fun h => hy ((hoff y).2 h)) (i PUnit.unit) (mem_pull.1 hi)
      exact map_nonunit ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ.stalkMap y).hom _ h)
    refine ⟨G, hG'.trans ?_⟩
    subst e
    congr 1
    exact (restr_pull (isLB_L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top le_top g).trans (H0.pull_restr (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off_eq.le g).symm
  · obtain ⟨g', hv, hr⟩ := GlobalTheory.T.extends_vanishing_of_simplePole_mul_extends hdense _ ω₀.ω hpole G ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m) hG
    haveI : IsOpenImmersion (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ := inferInstanceAs (IsOpenImmersion (𝟙 _))
    obtain ⟨g, rfl⟩ := ((isoOver_of_isOpenImmersion (O := ⊤) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ (fun x _ => ⟨x, rfl⟩)).bijective_pull
      (p := str₀ TF.X Z) (isLB_L₀ TF.X Z s) (W := ⊤) le_top le_top).2 g'
    refine ⟨g, fun y hy i hi => ?_, ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).bijective_pullOff (isLB_L₀ TF.X Z s)).1 ?_⟩
    · have h := hv y (fun h => hy ((hoff y).1 h)) (pIdx _ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ i) (mem_pIdx.2 hi)
      have e := H0.germ_pull (p := str₀ TF.X Z) (B := L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top (pIdx _ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ i) y (memTop y) (mem_pIdx.2 hi) g
      erw [e] at h
      intro hu
      exact h (hu.map _)
    · rw [← hr]
      exact (H0.pull_restr (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off_eq.le g).trans (restr_pull (isLB_L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top le_top g).symm

end GlobalTheory.LogCanonicalReflexive
