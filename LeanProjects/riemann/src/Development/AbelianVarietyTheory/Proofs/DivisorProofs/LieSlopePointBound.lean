import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHeightBoundedBelowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionDegreeSlopeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedBasePt
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeightParts.BdProof

theorem le_of_surj (K : Type) [Field K] (a b : ℕ) (q : (Fin a → K) →ₗ[K] (Fin b → K))
    (hq : Function.Surjective q) : b ≤ a := by
  have h1 := LinearMap.finrank_range_le q
  rw [LinearMap.range_eq_top.mpr hq, finrank_top] at h1
  simpa using h1

theorem log_bd (u a b X : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hX : 1 ≤ X) (hu : u ≤ a * X + b) :
    Real.log (2 + max u 0) ≤ Real.log (a + b + 2) + Real.log X := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  have : max u 0 ≤ a * X + b := max_le hu (by positivity)
  nlinarith

end GlobalTheory.HeightParts.BdProof

namespace GlobalTheory.HeightParts.BdProof

theorem main : Hypotheses2 → HypothesesH → LieSlope → PtBd → OmCmp → StepBd := by
  intro hP2 hPH hLS hPB hOm D O hcore hN A T H hR
  choose Cc hCc using GlobalTheory.T.abelian_height_bounded_below hP2 hPH D O hcore
  obtain ⟨B, hB⟩ := (Set.finite_range Cc).bddAbove
  set C0 : ℝ := max B 0 with hC0def
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hAlow : ∀ y : GlobalTheory.ShFam.Pad.Pt O.s, -C0 ≤ H.hA y := fun y => by
    rw [hR.ht.hA y]
    have h1 : ∀ c, Cc c ≤ C0 := fun c => (hB ⟨c, rfl⟩).trans (le_max_left _ _)
    exact (neg_le_neg (h1 _)).trans (hCc _ _ (HtTieRead.isClosed_basePt O y))
  obtain ⟨C1, hC1, hPt⟩ := hPB D O hcore hN A T H hR
  obtain ⟨C2, hOm2⟩ := hOm D O hcore hN A T H hR
  obtain ⟨Cs, hCs, hSl⟩ := hLS (D.R.f * O.N)
  obtain ⟨C', hC', hX⟩ := GlobalTheory.T.torus_extension_degree_slope_bound (D.R.f * O.N) C1 hC1
  set M : ℕ := Finset.univ.sup fun τ : D.host.E →+* ℂ => O.S.Dw.mult τ with hMdef
  set a : ℝ := max C2 0 with hadef
  have ha : 0 ≤ a := le_max_right _ _
  set large₂ : ℝ := Real.log (a + (C1 + C') + 2) with hLgdef
  have hLg : 0 ≤ large₂ := Real.log_nonneg (by linarith)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  refine ⟨max (max 1 (2 * C0)) (max (M * Cs) (M * Cs * large₂ + M * C' + C1)), ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  intro y hy
  set C := max (max 1 (2 * C0)) (max (M * Cs) (M * Cs * large₂ + M * C' + C1)) with hCdef
  have hC1' : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : 2 * C0 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC3 : M * Cs ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC4 : M * Cs * large₂ + M * C' + C1 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hy0 := hAlow y
  refine ⟨by linarith, ?_⟩
  intro τ k hk
  obtain ⟨K, _, _, F, h', h, L, r, ε, q, hherm, ⟨hdegL, hsteps⟩, hext⟩ := hPt y hy
  have hg : F.P₀.g ≤ D.R.f * O.N := le_of_surj K _ _ q hext.2.2.2.1
  obtain ⟨-, hmu'⟩ := hSl K F hg h' hherm
  obtain ⟨hfl, hmu⟩ := hX K r F.P₀.g h L ε q h' F.lieLat hext
  set X : ℝ := 2 + C + H.hA y with hXdef
  have hX1 : 1 ≤ X := by linarith

  have hom := hOm2 y
  have hOma : |omHt O (ref0 O) y| ≤ a * (|H.hA y| + 1) :=
    hom.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have habs : |H.hA y| ≤ H.hA y + 2 * C0 := by
    rcases abs_cases (H.hA y) with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> linarith
  have hfalt : F.falt h' ≤ a * X + (C1 + C') := by
    have e1 := (abs_le.1 hdegL).1
    have e2 := (abs_le.1 hOma).2
    have e3 : a * (|H.hA y| + 1) ≤ a * X := mul_le_mul_of_nonneg_left (by linarith) ha
    show -deg h' F.lieLat ≤ _
    linarith
  have hlog := log_bd (F.falt h') a (C1 + C') X ha (by linarith) hX1 hfalt
  set ν : ℝ := Cs * Real.log (2 + max (F.falt h') 0) with hνdef
  have hν0 : 0 ≤ ν := mul_nonneg hCs (Real.log_nonneg (by linarith [le_max_right (F.falt h') 0]))
  have hνle : ν ≤ Cs * large₂ + Cs * Real.log X := by
    have := mul_le_mul_of_nonneg_left hlog hCs
    rw [mul_add] at this
    exact this
  have hmuL := hmu ν hν0 hmu'
  obtain ⟨W, hWL, hWr, hWst⟩ := hsteps τ k hk
  have hdegW := hmuL W hWL
  rw [hWr] at hdegW
  have hkM : (k : ℝ) ≤ M := by
    have : O.S.Dw.mult τ ≤ M := Finset.le_sup (f := fun τ : D.host.E →+* ℂ => O.S.Dw.mult τ) (Finset.mem_univ τ)
    exact_mod_cast hk.trans this
  have hkd : (k : ℝ) * (ν + C') ≤ M * (ν + C') := mul_le_mul_of_nonneg_right hkM (by linarith)
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have e5 := (abs_le.1 hWst).1
  have e6 : (M : ℝ) * ν ≤ M * Cs * large₂ + M * Cs * Real.log X := by
    have := mul_le_mul_of_nonneg_left hνle hM
    linarith
  have e7 : (M : ℝ) * Cs * Real.log X ≤ C * Real.log X := mul_le_mul_of_nonneg_right hC3 hlX
  nlinarith

end GlobalTheory.HeightParts.BdProof

example : Hypotheses2 → HypothesesH → LieSlope → PtBd → OmCmp → StepBd := GlobalTheory.HeightParts.BdProof.main
