import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonRefinementModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopOfInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelMapSurjectiveBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqJAndIsClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightOfInducedBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeOfInducedBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosIffOfInduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPtHtShift
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar

noncomputable section

namespace GlobalTheory.ReadModel

theorem dominate2 : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M M₁ : TrueGeo.Model Y), ∃ (P : TrueGeo.Model Y) (π : P.X ⟶ M.X) (ρ : P.X ⟶ M₁.X), π ≫ M.p = P.p ∧ P.j ≫ π = M.j ∧ ρ ≫ M₁.p = P.p ∧ P.j ≫ ρ = M₁.j := by
  intro F _ _ Y M M₁
  obtain ⟨P, π, h⟩ := GlobalTheory.Member.DomFin.exists_dominating_fintype F Y M Bool (fun b => bif b then M₁ else M)
  exact ⟨P, π false, π true, (h false).1, (h false).2, (h true).1, (h true).2⟩

theorem nefFib_shift {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) : NefFib (L.shift t ht) ↔ NefFib L := Iff.rfl

theorem gdeg_shift {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (D : ℕ) : gdeg (L.shift t ht) D = gdeg L D := by
  simp only [gdeg, chInt, HermLB.shift, Weight.chernInt, Weight.chernPart_addFn_const]

theorem semiPos_shift_iff {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (D : ℕ) : (L.shift t ht).SemiPos D ↔ L.SemiPos D := by
  refine ⟨fun h σ i c y hy ξ => ?_, fun h => h.shift t ht⟩
  have := (h σ).addFn_const (-(2 * t σ)) i c y hy ξ
  simpa [HermLB.shift, Weight.addFn] using this

theorem readModel : Hypotheses2 → HypothesesH → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ), Y.dim = e →
    ∀ (A' : Adl (cxSt F) Y) (M M' : TrueGeo.Model Y) (L' : HermLB M'.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
    A'.Induced M' L' k cf →
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (q : X' ⟶ Sp (𝓞 F)) (π : X' ⟶ M.X) (_ : π ≫ M.p = q) (H : HermLB q)
      (n d : ℕ), IsArithVar q e ∧ Surjective π ∧ π.residueDegree (genericPoint X') = d ∧ 0 < d ∧ 0 < n ∧
      H.IsSelfInter ((Module.finrank ℤ (𝓞 F) : ℝ) * d * (n : ℝ) ^ (e + 1) * A'.arTop) ∧
      gdeg H e = (Module.finrank ℤ (𝓞 F) : ℝ) * d * (n : ℝ) ^ e * A'.deg ∧
      (A'.SemiPos ↔ H.SemiPos e) ∧ (A'.NefFib ↔ NefFib H) ∧
      ∀ (y : Y.X) (x : X'), IsAlgPt x → π x = M.j y → IsPtHt H x (n * A'.ht y) := by
  intro hP2 hPH F _ _ Y e he A' M M' L' k cf hI
  have hC : GlobalTheory.Published.ArCalc := hP2.p4
  have hD : GlobalTheory.Published.ArDegree := hPH.deg
  subst he
  obtain ⟨M₁, L₁, k₁, cf₁, hI₁, hN₁⟩ : ∃ (M₁ : TrueGeo.Model Y) (L₁ : HermLB M₁.p) (k₁ : ℕ+)
      (cf₁ : HeightOneSpectrum (𝓞 F) → ℝ), A'.Induced M₁ L₁ k₁ cf₁ ∧ (A'.NefFib → NefFib L₁) := by
    by_cases h : A'.NefFib
    · obtain ⟨M₁, L₁, k₁, cf₁, h₁, h₂⟩ := h
      exact ⟨M₁, L₁, k₁, cf₁, h₁, fun _ => h₂⟩
    · exact ⟨M', L', k, cf, hI, fun h' => absurd h' h⟩
  obtain ⟨P, π, ρ, hπp, hπj, hρp, hρj⟩ := dominate2 F Y M M₁
  have hI₂ := GlobalTheory.TrueGeo.InducedPull.induced_pull F _ Y A' M₁ P ρ hρp hρj L₁ k₁ cf₁ hI₁
  haveI := P.ar.isIntegral
  obtain ⟨hsurj, hdeg⟩ := GlobalTheory.T.model_map_surjective_birational F Y P M π hπp hπj
  obtain ⟨a, ha⟩ : ∃ a, (L₁.pull ρ hρp).IsSelfInter a := by
    obtain ⟨h, hh⟩ := (hC.arExists _ P.X P.p _ P.ar).1 (L₁.pull ρ hρp)
    exact ⟨_, h, hh, rfl⟩
  have htop := (GlobalTheory.TrueGeo.arTop_of_induced hC hD F _ Y A' P (L₁.pull ρ hρp) k₁ cf₁ hI₂).2 a ha
  have hg := GlobalTheory.T.geometric_degree_of_induced_bundle hD F _ Y A' P (L₁.pull ρ hρp) k₁ cf₁ hI₂
  have hfr : (Module.finrank ℤ (𝓞 F) : ℝ) = (Module.finrank ℚ F : ℝ) := by
    rw [NumberField.RingOfIntegers.rank]
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hN : (((k₁ : ℕ) * (A'.n : ℕ) : ℕ) : ℝ) ≠ 0 := by positivity
  refine ⟨P.X, P.ar.isIntegral, P.p, π, hπp,
    (L₁.pull ρ hρp).shift (fun _ => ((k₁ : ℕ) * (A'.n : ℕ) : ℕ) * (∑ᶠ v, cf₁ v) / (Module.finrank ℚ F : ℝ))
      (fun _ => rfl), (k₁ : ℕ) * (A'.n : ℕ), 1, P.ar, hsurj, hdeg, one_pos, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · have := hC.arShift _ P.X P.p Y.dim P.ar (L₁.pull ρ hρp) a
      ((((k₁ : ℕ) * (A'.n : ℕ) : ℕ) : ℝ) * (∑ᶠ v, cf₁ v) / (Module.finrank ℚ F : ℝ)) ha
    convert this using 1
    rw [hg, htop, hfr]
    push_cast at hN ⊢
    field_simp
    ring
  · rw [gdeg_shift, hg]
    push_cast
    ring
  · exact (GlobalTheory.TrueGeo.InducedSemiPos.semiPos_iff_of_induced F _ Y A' P (L₁.pull ρ hρp) k₁ cf₁ hI₂).trans (semiPos_shift_iff _ _ _ _).symm
  · rw [nefFib_shift]
    refine ⟨fun h => ?_, fun h => ⟨P, L₁.pull ρ hρp, k₁, cf₁, hI₂, h⟩⟩
    have := M₁.ar.finite
    exact GlobalTheory.ArInt.nefFib_pull _ M₁.X P.X M₁.p P.p M₁.ar.isProjOver P.ar.isProjOver ρ hρp L₁ (hN₁ h)
  · intro y x hx hxy
    obtain ⟨rfl, hy⟩ := GlobalTheory.TrueGeo.ReadPts.eq_j_and_isClosed F Y P M π hπj y x hx hxy
    have h₁ := GlobalTheory.T.point_height_of_induced_bundle hC.arExists F _ Y A' P (L₁.pull ρ hρp) k₁ cf₁ hI₂ y hy
    have h₂ := GlobalTheory.ShiftHt.isPtHt_shift hC.arExists _ P.X P.p Y.dim P.ar (L₁.pull ρ hρp) _ _
      ((((k₁ : ℕ) * (A'.n : ℕ) : ℕ) : ℝ) * (∑ᶠ v, cf₁ v) / (Module.finrank ℚ F : ℝ)) hx h₁
    convert h₂ using 1
    push_cast
    ring

end GlobalTheory.ReadModel

end
