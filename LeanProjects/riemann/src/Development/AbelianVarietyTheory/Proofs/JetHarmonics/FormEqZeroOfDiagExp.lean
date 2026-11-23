import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GCorCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PsJetTwistedSeriesOfLeOne

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GCorCut Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagExpZero

open GlobalTheory.FrameTwistCompare (lin quad)
open MvPowerSeries (constantCoeff pderiv)

section Flat

variable {S : Type} [CommRing S] {σ : Type}

def Flat (f : MvPowerSeries σ S) : Prop := constantCoeff f = 1 ∧ ∀ v, lin v f = 0

theorem flat_one : Flat (1 : MvPowerSeries σ S) := ⟨map_one _, fun v => by simp [lin]⟩

theorem quad_one (v w : σ) : quad v w (1 : MvPowerSeries σ S) = 0 := by simp [quad]

theorem Flat.mul {f g : MvPowerSeries σ S} (hf : Flat f) (hg : Flat g) : Flat (f * g) := by
  refine ⟨by rw [map_mul, hf.1, hg.1, _root_.mul_one], fun v => ?_⟩
  have h1 := hf.2 v
  have h2 := hg.2 v
  unfold lin at h1 h2 ⊢
  simp [Derivation.leibniz, h1, h2]

theorem Flat.quad_mul {f g : MvPowerSeries σ S} (hf : Flat f) (hg : Flat g) (v w : σ) :
    quad v w (f * g) = quad v w f + quad v w g := by
  have h1 := hf.2 v
  have h2 := hg.2 v
  have h3 := hf.2 w
  have h4 := hg.2 w
  unfold lin at h1 h2 h3 h4
  simp [quad, Derivation.leibniz, h1, h2, h3, h4, hf.1, hg.1, add_comm]

theorem Flat.pow {f : MvPowerSeries σ S} (hf : Flat f) (q : ℕ) :
    Flat (f ^ q) ∧ ∀ v w, quad v w (f ^ q) = q * quad v w f := by
  induction q with
  | zero => exact ⟨by simpa using flat_one, fun v w => by simp [quad_one]⟩
  | succ q ih =>
    refine ⟨by rw [pow_succ]; exact ih.1.mul hf, fun v w => ?_⟩
    rw [pow_succ, ih.1.quad_mul hf, ih.2]
    push_cast
    ring

theorem flat_finprod {J : Type} (s : Finset J) {f : J → MvPowerSeries σ S} (hf : ∀ i, Flat (f i)) :
    Flat (∏ i ∈ s, f i) ∧ ∀ v w, quad v w (∏ i ∈ s, f i) = ∑ i ∈ s, quad v w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using flat_one, fun v w => by simp [quad_one]⟩
  | insert a s ha ih =>
    refine ⟨by rw [Finset.prod_insert ha]; exact (hf a).mul ih.1, fun v w => ?_⟩
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (hf a).quad_mul ih.1, ih.2]

theorem quad_eq_zero {f : MvPowerSeries σ S}
    (h : ∀ e : σ →₀ ℕ, e.degree ≤ 2 → MvPowerSeries.coeff e (f - 1) = 0) (v w : σ) : quad v w f = 0 := by
  have h1 : quad v w (f - 1) = 0 := by
    simp only [quad, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
    rw [h _ (by simp)]
    simp
  simpa [quad] using h1

end Flat

open GlobalTheory.FrameTwistCompare in
theorem flat_ev_twist {S : Type} [CommRing S] [Algebra ℚ S] {n d : ℕ} (G : FGLaw S d) (c : Fin d → Fin d → S)
    {a : Fin 2 → Pt S n d} (ha : TB.LogPf.CZ a) : Flat (ev a (expP (-bilL G c))) := by
  refine ⟨cc_ev_twist G c ha, fun v => ?_⟩
  have h0 := cc_comp1_log G (ha 0)
  have h1 := cc_comp1_log G (ha 1)
  rw [ev_expP G c ha, ev_bilL_eq G c ha, bilLog_eq_bil, lin_exp]
  · have := lin_bil (c := c) h0 h1 v
    unfold lin at this ⊢
    rw [map_neg, map_neg, this, neg_zero]
  · rw [map_neg, cc_bil h0, neg_zero]

theorem form_eq_zero_of_diag_exp : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (d : ℕ) (G : FGLaw S d) (w w' : Pt S 1 d), (∀ i, MvPowerSeries.constantCoeff (w i) = 0) → dLin w + dLin w' = 1 → ∀ c : Fin d → Fin d → S, (∀ i j, c i j = c j i) → Matrix.transpose (dLin w) * Matrix.of c = Matrix.of c * dLin w' → ∀ (n q : ℕ), 1 ≤ n → 1 ≤ q → (∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ 2 → MvPowerSeries.coeff e ((∏ i : Fin n, ev (n := n) ![pt S d i, comp1 w (pt S d i)] (expP (-bilL G c)) ^ q) - 1) = 0) → c = 0 := by
  intro S _ _ d G w w' hw hsum c hsym hbal n q hn hq h
  have hz : ∀ i : Fin n, TB.LogPf.CZ (![pt S d i, comp1 w (pt S d i)] : Fin 2 → Pt S n d) := by
    intro i j k
    fin_cases j
    · exact FrameTwistCompare.cc_pt i k
    · exact TB.WickVanishing.cc_comp1 _ _ hw (FrameTwistCompare.cc_pt i) k
  have hfl := fun i => flat_ev_twist G c (hz i)
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hu : IsUnit (q : S) := by
    have := (IsUnit.mk0 (q : ℚ) (by exact_mod_cast (by omega : q ≠ 0))).map (algebraMap ℚ S)
    rwa [map_natCast] at this
  have key : ∀ a b, (Matrix.of c * dLin w) a b + (Matrix.of c * dLin w) b a = 0 := by
    intro a b
    have h2 := quad_eq_zero h (i₀, a) (i₀, b)
    rw [(flat_finprod _ fun i => ((hfl i).pow q).1).2, Finset.sum_eq_single i₀, ((hfl i₀).pow q).2,
      hu.mul_right_eq_zero, FrameTwistCompare.quad_ev_twist G c (hz i₀), neg_eq_zero] at h2
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        FrameTwistCompare.lin_comp1 _ (FrameTwistCompare.cc_pt _), FrameTwistCompare.lin_pt] at h2
      simp only [Matrix.mul_apply, Matrix.of_apply]
      simpa [mul_add, Finset.sum_add_distrib] using h2
    · intro i _ hi
      rw [((hfl i).pow q).2, FrameTwistCompare.quad_ev_twist G c (hz i)]
      simp [FrameTwistCompare.lin_pt, hi.symm]
    · simp
  have ht : (Matrix.of c).transpose = Matrix.of c := Matrix.ext fun i j => hsym j i
  have h3 : Matrix.of c * dLin w + Matrix.of c * dLin w' = 0 := by
    rw [← hbal]
    have e : (dLin w).transpose * Matrix.of c = (Matrix.of c * dLin w).transpose := by
      rw [Matrix.transpose_mul, ht]
    rw [e]
    exact Matrix.ext fun a b => key a b
  rw [← Matrix.mul_add, hsum, Matrix.mul_one] at h3
  exact h3

end GlobalTheory.DiagExpZero
