import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionsProductBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismMatrixUniqueFixedPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismsSameMatrixIsomorphicTestDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedUniversalHomMatrixSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestPullbackStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixMat

theorem exists_locClosed_homFix : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ (N : ℕ) (X : Scheme.{0}) (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (H : Scheme.{0}) (i : H ⟶ X)
    (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left)
    (Φ : AH ⟶ BH), IsClosedImmersion c ∧ IsOpenImmersion i ∧
    IsGrpPullback AH A (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φA ∧ IsGrpPullback BH B (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φB ∧ IsMonHom Φ ∧
    LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))) = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  intro Rg _ _ A B _ _ _ _ L M k hA hB hL hM hrA hrB hamp hk hva hbasA hbasB
  obtain ⟨eA, heA⟩ := hrA
  obtain ⟨eB, heB⟩ := hrB
  obtain ⟨mA, bA, hbA⟩ := hbasA
  obtain ⟨mB, bB, hbB⟩ := hbasB
  have hyp : Hyps L M k bA bB eA eB := ⟨hA, hB, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩

  obtain ⟨X, cE, H, i, AH, gA, BH, gB, φA, φB, Φ, hc, hi, htest, hex, hmat⟩ :=
    GlobalTheory.T.exists_locallyClosed_universal_hom_matrix_scheme Rg A B L M k mA mB bA bB eA eB hyp
  refine ⟨mA * mB, X, cE, H, i, AH, gA, BH, gB, φA, φB, Φ, hc, hi, htest.1, htest.2.1, htest.2.2.1,
    htest.2.2.2, ?_⟩
  intro R _ t A' B' _ _ φA' φB' Φ' h1 h2 h3 h4
  have ht : IsTest A B L M t A' B' φA' φB' Φ' := ⟨h1, h2, h3, h4⟩

  obtain ⟨c, hc'⟩ := GlobalTheory.T.line_bundle_sections_product_base_change Rg A B L M k mA mB bA bB eA eB hyp R t A' B' φA' φB' Φ' ht
  obtain ⟨h, hh, hmatc⟩ := hex R t A' B' φA' φB' Φ' c ht hc'

  obtain ⟨A₂, g₂, B₂, g₂', φA₂, φB₂, Φ₂, ht₂, hp₂⟩ :=
    GlobalTheory.T.exists_isTest_comp_isPullD_of_isTest Rg A B L M H (Sp R) (i ≫ cE ≫ affπ Rg (mA * mB)) h AH BH φA φB Φ htest
  have hm₂ := hmat R h A₂ B₂ φA₂ φB₂ Φ₂ ht₂ hp₂
  rw [hh, hmatc] at hm₂
  rw [hh] at ht₂

  have hpd := GlobalTheory.T.homomorphisms_same_matrix_isomorphic_test_data Rg A B L M k mA mB bA bB eA eB hyp R t A₂ B₂ φA₂ φB₂ Φ₂ A' B' φA' φB' Φ' c
    ht₂ ht hm₂ hc'
  have hfin := IsPullD.comp hp₂ hpd
  rw [Category.id_comp] at hfin
  refine ⟨h, ⟨hh, hfin⟩, ?_⟩

  rintro h' ⟨hh', hpd'⟩
  have ht' : IsTest A B L M (h' ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' := by
    rw [hh']; exact ht
  have hm' := hmat R h' A' B' φA' φB' Φ' ht' hpd'
  rw [hh'] at hm'
  have heq : matOf (h' ≫ i ≫ cE) = c :=
    GlobalTheory.T.homomorphism_matrix_unique_fixed_pullback Rg A B L M k mA mB bA bB eA eB hyp R t A' B' φA' φB' Φ' _ _ ht hm' hc'
  have hg : h' ≫ i ≫ cE = h ≫ i ≫ cE := by
    apply hom_ext_affine
    · simp only [Category.assoc]
      rw [hh', hh]
    · intro n
      obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective n
      exact congrFun (congrFun (heq.trans hmatc.symm) p.1) p.2
  have hg' : h' ≫ i = h ≫ i := by
    rw [← cancel_mono cE]
    simpa only [Category.assoc] using hg
  exact (cancel_mono i).1 hg'

end GlobalTheory.HomFixMat
