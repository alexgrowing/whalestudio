import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqOneOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArCalcOfPrincipalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermLineBundlePairPullbackDominantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullbackGenericallyBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogSectionCountChangeOfMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DominantProjArithSurjectiveComplexPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveOfIsometric
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.ChangeSing

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
  {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem up_pull_isometric (L : HermLB p) (u : SmFn p) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q) :
    (up (L.pull ρ hρ) (u.pull ρ hρ)).Isometric ((up L u).pull ρ hρ) := by
  refine HermLB.isometric_of_eqOn ?_
  intro σ a y _
  erw [Weight.pull_φ]
  exact (congrArg (· + u.u σ (Points.PtsOver.map ρ hρ (spMap σ) y)) (Weight.pull_φ (L.φ σ) ρ hρ a y)).symm

theorem ballIn_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (Λ : AddSubgroup X.functionField) (a b : ℤ)
    (hn : ∀ f ∈ Λ, ∀ (σ : k →+* ℂ) (y : CxPts q σ), Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (R : ℝ) : ballIn Q (Λ.map e.toAddMonoidHom) a b R = e '' ballIn P Λ a b R := by
  ext g
  constructor
  · rintro ⟨⟨f, hf, rfl⟩, hR⟩
    refine ⟨f, ⟨hf, fun σ x => ?_⟩, rfl⟩
    obtain ⟨y, rfl⟩ := hs σ x
    rw [← hn f hf σ y]
    exact hR σ y
  · rintro ⟨f, ⟨hf, hR⟩, rfl⟩
    refine ⟨⟨f, hf, rfl⟩, fun σ y => ?_⟩
    rw [hn f hf σ y]
    exact hR σ _

theorem ncard_ballIn_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (Λ : AddSubgroup X.functionField) (a b : ℤ)
    (hn : ∀ f ∈ Λ, ∀ (σ : k →+* ℂ) (y : CxPts q σ), Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (R : ℝ) : (ballIn Q (Λ.map e.toAddMonoidHom) a b R).ncard = (ballIn P Λ a b R).ncard := by
  rw [ballIn_map P Q e ρ hρ hs Λ a b hn R]
  exact Set.ncard_image_of_injective _ e.injective

theorem goodFam_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (he : ∀ (a b : ℤ), ∀ f ∈ P.H a b, e f ∈ Q.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts q σ),
      Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (D : ℕ) (g : ℝ) (Λ : ℕ → AddSubgroup X.functionField) (h : GoodFam P D g Λ) :
    GoodFam Q D g (fun m => (Λ m).map e.toAddMonoidHom) where
  le m := by
    rintro _ ⟨f, hf, rfl⟩
    exact (he m 1 f (h.le m hf)).1
  fg m := by
    classical
    obtain ⟨s, hs'⟩ := h.fg m
    refine ⟨s.image e, ?_⟩
    rw [Finset.coe_image, ← hs', AddMonoidHom.map_closure]
    rfl
  small := by
    obtain ⟨C, hC, hCm⟩ := h.small
    refine ⟨C, hC, fun m hm => ?_⟩
    have hn : ∀ f ∈ Λ m, ∀ (σ : k →+* ℂ) (y : CxPts q σ),
        Q.nu m 1 σ y (e f) = P.nu m 1 σ (Points.PtsOver.map ρ hρ (spMap σ) y) f :=
      fun f hf => (he m 1 f (h.le m hf)).2
    rw [ballIn_map P Q e ρ hρ hs (Λ m) m 1 hn]
    exact (AddSubgroup.map_mono (hCm m hm)).trans
      (AddMonoidHom.map_closure e.toAddMonoidHom (ballIn P (Λ m) m 1 (C ^ m))).le
  rank := by
    have e' : ∀ m, Module.finrank ℤ ((Λ m).map e.toAddMonoidHom) = Module.finrank ℤ (Λ m) := fun m =>
      ((AddSubgroup.equivMapOfInjective (Λ m) e.toAddMonoidHom e.injective).toIntLinearEquiv.finrank_eq).symm
    simp only [e']
    exact h.rank

end GlobalTheory.HSAmp.ChangeSing

namespace GlobalTheory.HSAmp.ChangeSing

theorem count_change_of_principalisation : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → GoodFam P D (gdeg P.L D / D.factorial) (fun m => P.H m 1) → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  intro hPr k _ X _ p D hX P a hsp hsi hgf
  have hC : Published.ArCalc := MixHt.arCalc_of_principalisation hPr
  obtain ⟨Y, hY, ρ, hYa, hYs, hgen, hdeg⟩ := GenRes.exists_birational_genSmooth hPr k X p D hX
  obtain ⟨Q, e, hQL, -, he⟩ := T.exists_hermLineBundlePair_pullback_dominant k X p Y (ρ ≫ p) ρ rfl hgen P
  have hs : ∀ σ : k →+* ℂ, Function.Surjective
      (Points.PtsOver.map ρ rfl (spMap σ) : CxPts (ρ ≫ p) σ → CxPts p σ) :=
    T.dominant_projArith_surjective_complexPoints k X p D hX Y (ρ ≫ p) D hYa ρ rfl hgen
  have hne : ρ.residueDegree (genericPoint Y) ≠ 0 := by rw [hdeg]; exact one_ne_zero
  have hproj := hC.2.2.2.2.1 k X Y p (ρ ≫ p) D hX hYa ρ rfl hgen hne
  have hdeg' : ((ρ.residueDegree (genericPoint Y) : ℕ) : ℝ) = 1 := by rw [hdeg]; simp
  have hQsp : Q.L.SemiPos D := by
    rw [hQL]; exact T.semiPos_pullback_generically_birational k X p D hX Y (ρ ≫ p) hYa ρ rfl hgen hdeg P.L hsp
  have hQsi : Q.L.IsSelfInter a := by
    have h := hproj.1 P.L a hsi
    rw [hdeg', one_mul] at h
    rw [hQL]; exact h
  have hQg : gdeg Q.L D = gdeg P.L D := by
    rw [hQL, CovTest.gdegPull k X Y p (ρ ≫ p) D hX hYa ρ rfl hgen hne, hdeg', one_mul]
  have hgf' := goodFam_map P Q e ρ rfl hs he D _ _ hgf
  rw [← hQg] at hgf'
  obtain ⟨t₀, ht⟩ := T.tendsto_logSectionCount_change_of_metric hC k Y (ρ ≫ p) D hYa hYs Q a hQsp hQsi _ hgf'
  refine ⟨t₀, fun u B a' hB hu husp husi t ht' => ?_⟩
  have hiso : (up Q.L (u.pull ρ rfl)).Isometric ((up P.L u).pull ρ rfl) := by
    rw [hQL]; exact up_pull_isometric P.L u ρ rfl
  have h1 : (up Q.L (u.pull ρ rfl)).SemiPos D :=
    HermLB.Isometric.semiPos _ _ D hiso.symm (T.semiPos_pullback_generically_birational k X p D hX Y (ρ ≫ p) hYa ρ rfl hgen hdeg _ husp)
  have h2 : (up Q.L (u.pull ρ rfl)).IsSelfInter a' := by
    have h := hproj.1 (up P.L u) a' husi
    rw [hdeg', one_mul] at h
    exact hiso.symm.isSelfInter hYa h
  have h3 := ht (u.pull ρ rfl) B a' hB (fun σ y => hu σ _) h1 h2 t ht'
  have hnP : ∀ m : ℕ, ∀ f ∈ P.H (m : ℤ) 1, ∀ (σ : k →+* ℂ) (y : CxPts (ρ ≫ p) σ),
      Q.nu m 1 σ y (e f) = P.nu m 1 σ (Points.PtsOver.map ρ rfl (spMap σ) y) f :=
    fun m f hf => (he m 1 f hf).2
  have hnU : ∀ m : ℕ, ∀ f ∈ P.H (m : ℤ) 1, ∀ (σ : k →+* ℂ) (y : CxPts (ρ ≫ p) σ),
      (upperParabolic Q (u.pull ρ rfl)).nu m 1 σ y (e f) =
        (upperParabolic P u).nu m 1 σ (Points.PtsOver.map ρ rfl (spMap σ) y) f := by
    intro m f hf σ y
    rw [((T.raiseFirstWeight_sections_loci_values_norms k Y (ρ ≫ p) Q (u.pull ρ rfl) m 1).2.2 σ y (e f)).2,
      ((T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).2.2 σ _ f).2, hnP m f hf σ y]
    rfl
  refine h3.congr fun m => ?_
  rw [ncard_ballIn_map (upperParabolic P u) (upperParabolic Q (u.pull ρ rfl)) e ρ rfl hs _ _ _ (hnU m),
    ncard_ballIn_map P Q e ρ rfl hs _ _ _ (hnP m)]

end GlobalTheory.HSAmp.ChangeSing
