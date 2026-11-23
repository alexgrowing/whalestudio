import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarComplexPointsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LineForm.PolarSum

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem evalF_add {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P + Q) = evalF A w P + evalF A w Q := by
  funext x
  simp only [evalF, fld, map_add, Pi.add_apply, Subalgebra.coe_add]

theorem evalF_smul {ι : Type} (w : ι → A.Pt → Ev n) (t : ℝ) (P : MvPolynomial ι ℝ) :
    evalF A w (t • P) = (t : ℂ) • evalF A w P := by
  funext x
  simp only [evalF, fld, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.aeval_C,
    Pi.smul_apply, ← Algebra.smul_def, Subalgebra.coe_smul]
  rfl

theorem re_dens_loc_smul (t : ℝ) (α : A.Fld) (i : A.ι) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    (dens (A.loc ((t : ℂ) • α) i v)).re = t * (dens (A.loc α i v)).re := by
  have h : A.loc ((t : ℂ) • α) i v = (t : ℂ) • A.loc α i v := by
    unfold HolAtlas.loc; split_ifs
    · rfl
    · exact (smul_zero _).symm
  rw [h, ← Complex.re_ofReal_mul]
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

variable [MeasurableSpace M] [BorelSpace M]

theorem part_smul (t : ℝ) (α : A.Fld) (ε ε' : ℤˣ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x : ℝ, ((ε : ℤ) : ℝ) * (t * x) = c * (((ε' : ℤ) : ℝ) * x)) :
    A.part ((t : ℂ) • α) ε = ENNReal.ofReal c • A.part α ε' := by
  have := ChernScale.glueMeas_restrict_eq A.e
    (ρ := fun i y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc ((t : ℂ) • α) i (A.e i y))).re))
    (ρ' := fun i y => ENNReal.ofReal ((ε' : ℤ) * (dens (A.loc α i (A.e i y))).re))
    (c := ENNReal.ofReal c) ENNReal.ofReal_ne_top MeasurableSet.univ
    (fun i y _ _ => by beta_reduce; rw [re_dens_loc_smul, h, ENNReal.ofReal_mul hc])
  rw [Measure.restrict_univ, Measure.restrict_univ] at this
  exact this

theorem integrable_part_smul {g : M → ℝ} (t : ℝ) {α : A.Fld} (h : ∀ ε : ℤˣ, Integrable g (A.part α ε)) (ε : ℤˣ) :
    Integrable g (A.part ((t : ℂ) • α) ε) := by
  rcases le_total 0 t with ht | ht
  · rw [part_smul A t α ε ε t ht fun x => by ring]
    exact (h ε).smul_measure ENNReal.ofReal_ne_top
  · rw [part_smul A t α ε (-ε) (-t) (neg_nonneg.2 ht) fun x => by rw [Units.val_neg, Int.cast_neg]; ring]
    exact (h _).smul_measure ENNReal.ofReal_ne_top

theorem part_zero_smul (α : A.Fld) (ε : ℤˣ) : A.part (((0 : ℝ) : ℂ) • α) ε = 0 := by
  rw [part_smul A 0 α ε ε 0 le_rfl fun x => by ring, ENNReal.ofReal_zero, zero_smul]

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

theorem wInt_evalF_sum {ι κ : Type} (w : ι → A.Pt → Ev n) (hw : ∀ i, A.IsForm (fld A (w i))) (g : M → ℝ)
    (P : κ → MvPolynomial ι ℝ) (c : κ → ℝ) (s : Finset κ)
    (h : ∀ a ∈ s, ∀ ε : ℤˣ, Integrable g (A.part (evalF A w (P a)) ε)) :
    (∀ ε : ℤˣ, Integrable g (A.part (evalF A w (∑ a ∈ s, c a • P a)) ε)) ∧
      wInt A g (evalF A w (∑ a ∈ s, c a • P a)) = ∑ a ∈ s, c a * wInt A g (evalF A w (P a)) := by
  have hF : ∀ Q, A.IsForm (evalF A w Q) := fun Q => ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.1 ι w Q hw).1
  obtain ⟨-, hadd, hsm, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  induction s using Finset.induction_on with
  | empty =>
    have e : evalF A w 0 = ((0 : ℝ) : ℂ) • evalF A w 0 := by rw [← evalF_smul, zero_smul]
    simp only [Finset.sum_empty]
    rw [e]
    refine ⟨fun ε => ?_, ?_⟩
    · rw [part_zero_smul]; exact integrable_zero_measure
    · rw [hsm g 0 _ (hF _), zero_mul]
  | insert a s ha ih =>
    obtain ⟨i₁, i₂⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    have j₁ : ∀ ε : ℤˣ, Integrable g (A.part (evalF A w (c a • P a)) ε) := by
      rw [evalF_smul]
      exact integrable_part_smul A (c a) (h a (Finset.mem_insert_self a s))
    obtain ⟨k₁, k₂⟩ := hadd g _ _ (hF _) (hF _) j₁ i₁
    rw [Finset.sum_insert ha, Finset.sum_insert ha, evalF_add]
    refine ⟨k₁, ?_⟩
    rw [k₂, i₂, evalF_smul, hsm g _ _ (hF _)]

end Manifold

theorem wInt_sum_lin_pow : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (g : CxPts p σ → ℝ) (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
    (∀ n ∈ s, ∀ ε : ℤˣ, Integrable g ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε)) →
    wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) =
      ∑ n ∈ s, c n * wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) := by
  intro k _ X p D hX σ ι _ L g s c h
  haveI := hX.toIsArithVar.isIntegral
  obtain ⟨h₁, h₂, h₃⟩ := (GlobalTheory.IsArithVar.finite_emb_and_topology hX.toIsArithVar).2 σ
  exact (wInt_evalF_sum (hX.atlas σ) (fun i => c1F hX σ (L i))
    (fun i => ((GlobalTheory.T.firstChern_form_properties k X p D hX σ).1 (L i) (L i)).1.1) g
    (fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ D) c s h).2

end GlobalTheory.LineForm.PolarSum
