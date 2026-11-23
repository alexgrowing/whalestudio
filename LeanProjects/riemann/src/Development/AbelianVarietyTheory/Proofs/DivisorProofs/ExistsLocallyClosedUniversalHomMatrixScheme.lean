import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineSpaceMorphismOfCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalToUnitTensorIsPullbackIsIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitTensorStructureMapFlatProjectiveUnivClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGeneratingCombinationMatrixLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedLocusHomogeneousEquationsSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearNormalisationClosedSubschemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFormsIffProportionalPullbacksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackSectionsProportionalToCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEmbedOfBaseChangeStableBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZeroSectionValueInPowerFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestHomMatrixGeneratesNormalisedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestHomMatrixOfProportionalGeneratingCombinatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomOfProportionalGeneratingCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedLocusPullbackLineBundlesIsomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImmersedClosedOpenIntersectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixUniv

variable {mA mB : ℕ}

theorem comb_comp {A₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂) (e : p₂ ≫ h = r ≫ p) (z : X₂)
    (q : N.ι) (hq : φ (r z) ∈ N.U q) (j : Fin mB) :
    comb a (r ≫ φ) p₂ (fun i j => h.appTop (c i j)) z q j = (r.stalkMap z).hom (comb a φ p c (r z) q j) := by
  simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e₁ : gs p₂ z ⊤ (h.appTop (c i j)) = gs (r ≫ p) z ⊤ (c i j) := by
    rw [← e]; exact gs_pull p₂ h z ⊤ trivial (c i j)
  rw [e₁, gs_comp r p z ⊤ trivial, gs_comp r φ z _ hq]

theorem Generates.comp {A₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} {a : Fin mA → LB.Sec N} {φ : X ⟶ A₀} {p : X ⟶ T}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} (hg : Generates a φ p c) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂)
    (e : p₂ ≫ h = r ≫ p) : Generates a (r ≫ φ) p₂ (fun i j => h.appTop (c i j)) := by
  intro z q hq
  obtain ⟨j, hj⟩ := hg (r z) q hq
  exact ⟨j, by rw [comb_comp a φ p c r h p₂ e z q hq j]; exact hj.map _⟩

theorem Proport.comp {A₀ B₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} {H : LB B₀} {a : Fin mA → LB.Sec N}
    {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T} {Ψ : X ⟶ B₀} {c : Fin mA → Fin mB → Γ(T, ⊤)}
    (hp : Proport a b φ p Ψ c) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂) (e : p₂ ≫ h = r ≫ p) :
    Proport a b (r ≫ φ) p₂ (r ≫ Ψ) (fun i j => h.appTop (c i j)) := by
  intro z q k hq hk j j'
  rw [comb_comp a φ p c r h p₂ e z q hq, comb_comp a φ p c r h p₂ e z q hq, gs_comp r Ψ z _ hk,
    gs_comp r Ψ z _ hk, ← map_mul, ← map_mul, hp (r z) q k hq hk j j']

theorem matOf_comp {Rg : Type} [CommRing Rg] {X X' : Scheme.{0}} (h : X ⟶ X')
    (g : X' ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) : matOf (h ≫ g) = fun i j => h.appTop (matOf g i j) := by
  funext i j; exact coord_comp h g _

theorem relift {S T' T : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ : Over T} [GrpObj G₁] {G' : Over T'} [GrpObj G']
    {t₁ : T ⟶ S} {u : T' ⟶ T} {φ₁ : G₁.left ⟶ G.left} {φ' : G'.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G t₁ φ₁)
    (h' : IsGrpPullback G' G (u ≫ t₁) φ') : ∃ ψ : G'.left ⟶ G₁.left, IsGrpPullback G' G₁ u ψ ∧ ψ ≫ φ₁ = φ' := by
  refine ⟨h₁.1.lift φ' (G'.hom ≫ u) (by rw [h'.1.w, Category.assoc]), ?_, h₁.1.lift_fst _ _ _⟩
  exact h₁.cancel (by rw [h₁.1.lift_fst]; exact h') (h₁.1.lift_snd _ _ _)

theorem exists_universal_matrix : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∃ (X : Scheme.{0}) (cE : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (H : Scheme.{0}) (i : H ⟶ X) (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH), IsClosedImmersion cE ∧ IsOpenImmersion i ∧ IsTest A B L M (i ≫ cE ≫ affπ Rg (mA * mB)) AH BH φA φB Φ ∧ (∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ h : Sp R ⟶ H, h ≫ i ≫ cE ≫ affπ Rg (mA * mB) = t ∧ matOf (h ≫ i ≫ cE) = c) ∧ ∀ (R : Type) [CommRing R] (h : Sp R ⟶ H) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' → IsPullD φA φB Φ φA' φB' Φ' h → IsMat L M k bA bB eA eB (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' (matOf (h ≫ i ≫ cE)) := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH
  obtain ⟨hAb, hBb, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩ := hH
  obtain ⟨hfl, hpj, huc⟩ := GlobalTheory.T.unitTensorStructureMap_flat_projective_univClosed Rg A L hAb hL hamp
  haveI := huc
  have hEmb := GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis Rg B M k mB bB hBb hM hk hva hbB
  have hcov : (⨆ j, nonzeroLocus (bB j)) = ⊤ := hEmb.1
  have hNA : (LPow A L (k : ℤ) (topS Rg)).IsLB := LB.isLB_linComb hL _ _
  have hNB : (LPow B M (k : ℤ) (topS Rg)).IsLB := LB.isLB_linComb hM _ _
  choose αA hαA using fun i => GlobalTheory.T.exists_zeroSection_value_in_powerFrame Rg A L k eA (bA i) hL heA
  choose βB hβB using fun j => GlobalTheory.T.exists_zeroSection_value_in_powerFrame Rg B M k eB (bB j) hM heB
  obtain ⟨U, hU⟩ := GlobalTheory.T.isOpen_generatingCombinationMatrixLocus Rg _ (fA A) _ mA mB bA hNA
  obtain ⟨ZF, ιF, hιF, hF⟩ := GlobalTheory.T.exists_closed_locus_homogeneous_equations_sections Rg _ _ (fA A) (fA B) _ _ mA mB bA bB hfl hpj hNA
  obtain ⟨ZN, ιN, hιN, hNm⟩ := GlobalTheory.T.linearNormalisation_closed_subscheme Rg mA mB αA βB
  haveI : IsNoetherian (Sp (MvPolynomial (Fin (mA * mB)) Rg)) := isNoetherian_Spec.2 inferInstance
  obtain ⟨W, j₁, hj₁, hj₁q, hWn, hW⟩ := GlobalTheory.T.exists_immersed_closed_open_intersection _ ZF ZN ιF ιN U hιF hιN
  have cond : ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ (topS Rg ⊗ A).left)
      (p : X' ⟶ T), (∃ w, w ≫ j₁ = g) → IsPullback φ p (fA A) (g ≫ affπ Rg (mA * mB)) →
      Generates bA φ p (matOf g) ∧ FormsOK bA (fA B) bB φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ∧
        Normal (g ≫ affπ Rg (mA * mB)) (matOf g) αA βB := by
    intro T X' g φ p hg hP
    obtain ⟨h1, h2, h3⟩ := (hW T g).2 hg
    exact ⟨(hU T X' g φ p hP).2 h3, (hF T X' g φ p hP).2 h1, (hNm T g).2 h2⟩
  have datum : ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (∃ w, w ≫ j₁ = g) →
      ∃ (AT : Over T) (_ : GrpObj AT) (BT : Over T) (_ : GrpObj BT) (φA : AT.left ⟶ A.left) (φB : BT.left ⟶ B.left)
        (Φ : AT ⟶ BT), IsGrpPullback AT A (g ≫ affπ Rg (mA * mB)) φA ∧
        IsGrpPullback BT B (g ≫ affπ Rg (mA * mB)) φB ∧ IsMonHom Φ ∧ Generates bA (φA ≫ θ A) AT.hom (matOf g) ∧
        Proport bA bB (φA ≫ θ A) AT.hom (Φ.left ≫ φB ≫ θ B) (matOf g) := by
    intro T g hg
    letI : GrpObj ((Over.pullback (g ≫ affπ Rg (mA * mB))).obj A) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (g ≫ affπ Rg (mA * mB))).obj B) := Functor.grpObjObj
    have pA := isGrpPullback_pullback A (g ≫ affπ Rg (mA * mB))
    have pB := isGrpPullback_pullback B (g ≫ affπ Rg (mA * mB))
    have hP := (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg A T _ _ _ (g ≫ affπ Rg (mA * mB))).1 pA.1
    obtain ⟨c1, c2, c3⟩ := cond T _ g _ _ hg hP
    obtain ⟨Ψ, hΨ, hpr⟩ := (GlobalTheory.T.vanishingForms_iff_proportional_pullbacks Rg _ _ _ T (fA A) (fA B) _ _ mA mB bA bB _ _ _ (matOf g) hEmb hNB hNA hP.w
      c1).1 c2
    obtain ⟨Φ, hΦ, hΦΨ⟩ := GlobalTheory.T.grpHom_of_proportional_generating_combinations Rg A B L M k mA mB bA bB eA eB αA βB T _ _ _ _ _ Ψ (matOf g)
      ⟨hAb, hBb, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩ hαA hβB pA pB hΨ c1 hpr c3
    exact ⟨_, inferInstance, _, inferInstance, _, _, Φ, pA, pB, hΦ, c1, by rw [hΦΨ]; exact hpr⟩
  have θf : ∀ C : Over (Sp Rg), θ C ≫ fA C = C.hom := fun C => (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg C C.left C.left (𝟙 _) (𝟙 _) C.hom).2.1
  have θi : ∀ C : Over (Sp Rg), IsIso (θ C) := fun C => (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg C C.left C.left (𝟙 _) (𝟙 _) C.hom).2.2
  obtain ⟨A₁, iA₁, B₁, iB₁, φA₁, φB₁, Φ₁, pA₁, pB₁, hΦ₁, hg₁, hp₁⟩ := datum W j₁ ⟨𝟙 _, Category.id_comp _⟩
  haveI := hWn
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.isClosed_locus_pullback_lineBundles_isomorphic Rg A B L M eA eB W (j₁ ≫ affπ Rg (mA * mB)) A₁ B₁ φA₁ φB₁ Φ₁ hAb hBb hL hM heA heB
    hamp pA₁ pB₁ hΦ₁
  have compare : ∀ (T : Scheme.{0}) (u : T ⟶ W) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A ((u ≫ j₁) ≫ affπ Rg (mA * mB)) φA' →
      IsGrpPullback B' B ((u ≫ j₁) ≫ affπ Rg (mA * mB)) φB' →
      Generates bA (φA' ≫ θ A) A'.hom (matOf (u ≫ j₁)) →
      Proport bA bB (φA' ≫ θ A) A'.hom (Φ'.left ≫ φB' ≫ θ B) (matOf (u ≫ j₁)) →
      ∃ (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left), IsGrpPullback A' A₁ u ψA ∧ IsGrpPullback B' B₁ u ψB ∧
        ψA ≫ φA₁ = φA' ∧ ψB ≫ φB₁ = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ₁.left := by
    intro T u A' B' _ _ φA' φB' Φ' hA' hB' hgen hprop
    rw [Category.assoc] at hA' hB'
    obtain ⟨ψA, hψA, eA'⟩ := relift pA₁ hA'
    obtain ⟨ψB, hψB, eB'⟩ := relift pB₁ hB'
    refine ⟨ψA, ψB, hψA, hψB, eA', eB', ?_⟩
    apply pB₁.1.hom_ext
    · rw [Category.assoc, eB', Category.assoc, ← cancel_mono (θ B), Category.assoc, Category.assoc, Category.assoc]
      have hp := hp₁.comp ψA u A'.hom hψA.1.w.symm
      rw [← matOf_comp, ← Category.assoc ψA φA₁, eA'] at hp
      refine GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations Rg _ _ _ T (fA B) _ _ mA mB bA bB (φA' ≫ θ A) A'.hom (matOf (u ≫ j₁)) _ _ hEmb hNB hNA hgen
        hprop hp ?_
      simp only [Category.assoc, θf]
      rw [hB'.1.w, pB₁.1.w, reassoc_of% (Over.w Φ'), reassoc_of% (Over.w Φ₁), reassoc_of% hψA.1.w]
    · rw [Category.assoc, hψB.1.w, reassoc_of% (Over.w Φ'), Category.assoc, Over.w Φ₁, hψA.1.w]
  obtain ⟨AH, iAH, BH, iBH, φAH, φBH, ΦH, pAH, pBH, hΦH, hgH, hpH⟩ := datum Z (i ≫ j₁) ⟨i, rfl⟩
  obtain ⟨ψA, ψB, hψA, hψB, eψA, eψB, eΦ⟩ := compare Z i AH BH φAH φBH ΦH pAH pBH hgH hpH
  have hlb : LBIso (L.pull φAH) ((M.pull φBH).pull ΦH.left) := by
    have := (hZ Z i AH BH ψA ψB ΦH hψA hψB eΦ).2 ⟨𝟙 _, Category.id_comp _⟩
    rwa [eψA, eψB] at this
  refine ⟨(i ≫ j₁).image, (i ≫ j₁).imageι, Z, (i ≫ j₁).toImage, AH, iAH, BH, iBH, φAH, φBH, ΦH, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.toImage_imageι_assoc]
    exact ⟨pAH, pBH, hΦH, hlb⟩
  · intro R _ t A' B' _ _ φA' φB' Φ' c hT hMat
    obtain ⟨g, hgt, hgc⟩ := GlobalTheory.T.exists_affineSpace_morphism_of_coordinates Rg (Sp R) (mA * mB) t
      (fun n => c (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2)
    have hgm : matOf g = c := by funext a b; simp [matOf, hgc]
    obtain ⟨hgen, hprop, hnorm⟩ := GlobalTheory.T.testHom_matrix_generates_normalised Rg A B L M k mA mB bA bB eA eB αA βB R t A' B' φA' φB' Φ' c hL hM
      hcov hαA hβB hT hMat
    rw [← hgm] at hgen hprop
    rw [← hgm, ← hgt] at hnorm
    have hP : IsPullback (φA' ≫ θ A) A'.hom (fA A) (g ≫ affπ Rg (mA * mB)) := by
      rw [hgt]; exact (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg A _ _ _ _ t).1 hT.1.1
    have hbase : (Φ'.left ≫ φB' ≫ θ B) ≫ fA B = A'.hom ≫ g ≫ affπ Rg (mA * mB) := by
      rw [hgt, Category.assoc, Category.assoc, θf, hT.2.1.1.w, reassoc_of% (Over.w Φ')]
    have hforms := (GlobalTheory.T.vanishingForms_iff_proportional_pullbacks Rg _ _ _ _ (fA A) (fA B) _ _ mA mB bA bB (φA' ≫ θ A) A'.hom (g ≫ affπ Rg _) (matOf g)
      hEmb hNB hNA hP.w hgen).2 ⟨_, hbase, hprop⟩
    obtain ⟨w₁, hw₁⟩ := (hW _ g).1 ⟨(hF _ _ g _ _ hP).1 hforms, (hNm _ g).1 hnorm, (hU _ _ g _ _ hP).1 hgen⟩
    have hA' : IsGrpPullback A' A ((w₁ ≫ j₁) ≫ affπ Rg (mA * mB)) φA' := by rw [hw₁, hgt]; exact hT.1
    have hB' : IsGrpPullback B' B ((w₁ ≫ j₁) ≫ affπ Rg (mA * mB)) φB' := by rw [hw₁, hgt]; exact hT.2.1
    obtain ⟨ψA', ψB', hψA', hψB', eψA', eψB', eΦ'⟩ := compare _ w₁ A' B' φA' φB' Φ' hA' hB'
      (by rw [hw₁]; exact hgen) (by rw [hw₁]; exact hprop)
    have hlb' := hT.2.2.2
    rw [← eψA', ← eψB'] at hlb'
    obtain ⟨w₂, hw₂⟩ := (hZ _ w₁ A' B' ψA' ψB' Φ' hψA' hψB' eΦ').1 hlb'
    refine ⟨w₂, ?_, ?_⟩
    · rw [Scheme.Hom.toImage_imageι_assoc, ← Category.assoc, ← Category.assoc, hw₂, hw₁, hgt]
    · rw [Scheme.Hom.toImage_imageι, ← Category.assoc, hw₂, hw₁, hgm]
  · intro R _ h A' B' _ _ φA' φB' Φ' hT hD
    obtain ⟨ψA', ψB', qA, qB, eA', eB', eΦ'⟩ := hD
    simp only [Scheme.Hom.toImage_imageι_assoc, Scheme.Hom.toImage_imageι] at hT ⊢
    have e₀ : A'.hom ≫ h = ψA' ≫ AH.hom := qA.1.w.symm
    have keyA : ψA' ≫ φAH ≫ θ A = φA' ≫ θ A := by rw [← eA', Category.assoc]
    have keyB : ψA' ≫ ΦH.left ≫ φBH ≫ θ B = Φ'.left ≫ φB' ≫ θ B := by
      rw [← eB']; simp only [Category.assoc]; rw [reassoc_of% eΦ']
    have hgen := hgH.comp ψA' h A'.hom e₀
    rw [keyA, ← matOf_comp] at hgen
    have hpr := hpH.comp ψA' h A'.hom e₀
    rw [keyA, keyB, ← matOf_comp] at hpr
    have hnorm : Normal ((h ≫ i ≫ j₁) ≫ affπ Rg (mA * mB)) (matOf (h ≫ i ≫ j₁)) αA βB :=
      (hNm _ _).2 ((hW _ _).2 ⟨h ≫ i, Category.assoc _ _ _⟩).2.1
    simp only [Category.assoc] at hT hnorm hgen hpr ⊢
    exact GlobalTheory.T.isTestHomMatrix_of_proportional_generating_combinations Rg A B L M k mA mB bA bB eA eB αA βB R _ A' B' φA' φB' Φ' _ hL hM heA heB hcov hαA hβB hT
      hgen hpr hnorm

end GlobalTheory.HomFixUniv
