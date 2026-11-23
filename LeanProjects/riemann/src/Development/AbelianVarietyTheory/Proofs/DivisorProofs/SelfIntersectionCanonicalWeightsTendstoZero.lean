import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeProjectionFormulaSelfInterPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFunctionFieldQuotientSubfieldEqDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMorphismOfGeneratingSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBasepointFreeSectionsLeOneFubiniStudyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegreStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem selfInter_canWeight_le : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField),
    Gens P D e x → ∃ C : ℝ, ∀ (n : ℕ) (u : SmFn p) (a : ℝ), 1 ≤ n → IsCan P e n x u →
      (up P.L u).IsSelfInter a → |a| ≤ C / n := by
  intro hC k _ X _ p D hX P hA e x hG
  haveI := hX.isDomain
  haveI := hX.finite
  haveI := hX.charZero_base
  have hf : 0 < Module.finrank ℤ k := Module.finrank_pos
  have he : 0 < e := hG.pos
  obtain ⟨hPI, -, -, -, -, -, -⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hA e x hG
  obtain ⟨hPV, -, -⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D

  obtain ⟨Φ₀, hΦ₀⟩ := ((hC.arExists k (PSpace k D) (PSpace.str k D) D hPV).2 Unit
    fun _ => ProjSpace.hermitianTwistingSheaf k D).1
  have hH := ((hC.arIso k (PSpace k D) (PSpace.str k D) D hPV).2 Unit _ Φ₀ hΦ₀).1 ()
  set H := Φ₀ (MvPolynomial.X () ^ (D + 1)) with hHdef
  set g := gdeg P.L D
  refine ⟨|g * H| / ((Module.finrank ℤ k : ℝ) * e), fun n u a hn hu ha => ?_⟩
  obtain ⟨-, -, -, hG', hu'⟩ := GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy k X p D hX P e x hG n u hn hu
  obtain ⟨hPI', π, hπ, hgen, hd, hdf, hiso⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hA (e * n) _ hG'
  have hdeg := GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree hC k X p D hX P hA (e * n) _ hG'
  have hpow := (GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow hC k X p D hX).2 (up P.L u) (e * n) a ha
  have hpull := ((hC.arProj k (PSpace k D) X (PSpace.str k D) p D hPV hX π hπ hgen hd).1 _ H hH)

  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => (up P.L u).pow (e * n)).1
  have hI := hC.arIso k X p D hX
  have h₁ := (hI.2 Unit _ Φ hΦ).1 ()
  have hΦ' := (hI.2 Unit _ Φ hΦ).2.1 (fun _ => (ProjSpace.hermitianTwistingSheaf k D).pull π hπ) fun _ => hiso u hu'
  have h₂ := (hI.2 Unit _ Φ hΦ').1 ()
  have e₁ := HermLB.IsSelfInter.unique hX hpow h₁
  have e₂ := HermLB.IsSelfInter.unique hX hpull h₂

  set d : ℝ := ((π.residueDegree (genericPoint X) : ℕ) : ℝ)
  set f : ℝ := ((Module.finrank ℤ k : ℕ) : ℝ)
  set E : ℝ := ((e * n : ℕ) : ℝ)
  have hE : 0 < E := by positivity
  have hfpos : (0 : ℝ) < f := Nat.cast_pos.mpr hf
  have key1 : E ^ (D + 1) * a = d * H := e₁.trans e₂.symm
  have key2 : d * f = E ^ D * g := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hdf
    simp only [Nat.cast_mul] at this
    rw [← hdeg]; exact this
  have ha' : a = g * H / (f * E) := by
    field_simp
    have : E ^ (D + 1) * a * f = E ^ D * g * H := by rw [key1, ← key2]; ring
    have hED : E ^ D ≠ 0 := pow_ne_zero _ hE.ne'
    apply mul_left_cancel₀ hED
    linear_combination this
  rw [ha', abs_div, abs_of_pos (by positivity : (0:ℝ) < f * E)]
  have : f * E = (f * e) * n := by simp [E, f]; ring
  rw [this, div_div]

end GlobalTheory.HSAmp
