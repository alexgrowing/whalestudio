import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnMeasurablePsi

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (dimN Vsph)

def cn_kapBd (Cv : ℝ) {a : ℕ} (j : Fin a → ℕ) (p q n0 f : ℕ) (v res : ℝ) : ℝ :=
  ((Cv ^ dimN j n0 * (Vsph p * Vsph q / (Vsph (p - ∑ x, j x) * Vsph (q - ∑ x, j x) * ∏ x, Vsph (j x)))) ^ f *
      (Cv * v) ^ ((f : ℝ) * (dimN j n0 : ℝ) / 2) * ∏ x, ((Cv * v) ^ (j x ^ 2 * f) * res * Cv ^ f)) *
    (v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * (f : ℝ) / 2) * Cv ^ ((p + q) * f))

theorem cn_kappa_num (Cv Cres : ℝ) (hCv : 1 ≤ Cv) : ∃ n₁ : ℕ, ∀ (a p q n0 f : ℕ) (j : Fin a → ℕ) (rd res : ℝ),
    n₁ ≤ p + q → q ≤ p → q ^ 2 ≤ p + q → (∀ x, 1 ≤ j x) → 1 ≤ a → ∑ x, j x ≤ q → p + q = n0 + 2 * ∑ x, j x → 1 ≤ f →
    1 < rd → Real.log (Real.log rd) ≤ ((p + q : ℕ) : ℝ) → 0 ≤ res → res ≤ (Cres * Real.log rd) ^ (2 * f) →
    cn_kapBd Cv j p q n0 f (rd / 2) res ≤
      Real.exp (-(1 / 8 * ((∑ x, j x : ℕ) : ℝ) * ((p + q : ℕ) : ℝ) * (f : ℝ) * Real.log ((p + q : ℕ) : ℝ))) := by
  obtain ⟨C', hC', hA⟩ := Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.kappaAssembly Cv hCv
  set C : ℝ := max C' (max |Cres| 1) with hC
  have hCC' : C' ≤ C := le_max_left _ _
  have hCres : |Cres| ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC1 : 1 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨n₀, hK⟩ := cn_kappaBoundAbs C hC1
  refine ⟨n₀, fun a p q n0 f j rd res hn hqp hq2 hj ha hJq hpq hf hrd hll hres0 hres => ?_⟩
  have hv : (1 : ℝ) / 2 ≤ rd / 2 := by linarith
  have hv0 : 0 < rd / 2 := by linarith
  have hCv0 : 0 < Cv := by linarith
  have hV : ∀ i, 0 < Vsph i := Formalism.HermitianLatticeCounting.P.vsph_pos
  have hℓ : 0 < Real.log rd := Real.log_pos hrd
  have h1 := hA a p q n0 f j (rd / 2) res
    ((Cv ^ dimN j n0 * (Vsph p * Vsph q / (Vsph (p - ∑ x, j x) * Vsph (q - ∑ x, j x) * ∏ x, Vsph (j x)))) ^ f)
    ((Cv * (rd / 2)) ^ ((f : ℝ) * (dimN j n0 : ℝ) / 2))
    ((rd / 2) ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * (f : ℝ) / 2) * Cv ^ ((p + q) * f))
    (fun x => (Cv * (rd / 2)) ^ (j x ^ 2 * f) * res * Cv ^ f) hj ha hJq hqp hpq hf hv hres0
    (by positivity) le_rfl (fun x => ⟨by positivity, le_rfl⟩) (by positivity) le_rfl
    (by
      have := hV p; have := hV q; have := hV (p - ∑ x, j x); have := hV (q - ∑ x, j x)
      have : 0 < ∏ x, Vsph (j x) := Finset.prod_pos fun x _ => hV _
      positivity) le_rfl
  have haJ : a ≤ ∑ x, j x := by
    calc a = ∑ _x : Fin a, 1 := by simp
      _ ≤ ∑ x, j x := Finset.sum_le_sum fun x _ => hj x
  have hdN : dimN j n0 ≤ 2 * (∑ x, j x) * (p + q) := by
    rw [hpq]
    exact (Formalism.HermitianLatticeCounting.Final.S7.dimIdentity a j n0).2.1
  have hres' : res ≤ (C * Real.log rd) ^ (2 * f) := by
    refine le_trans hres ?_
    rw [← Even.pow_abs ⟨f, two_mul f⟩ (Cres * Real.log rd), abs_mul, abs_of_pos hℓ]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCres hℓ.le) _
  have h2 := hK (p + q) p q (∑ x, j x) a f (dimN j n0) (rd / 2) res (Real.log rd) hn rfl hq2 ha haJ hJq hf hdN hv hℓ hll
    hres0 hres'
  refine le_trans ?_ h2
  unfold cn_kapBd
  refine le_trans h1 ?_
  have hC'0 : 0 < C' := by linarith
  gcongr

def cn_res (X : CData) : ℝ := NumberField.dedekindZeta_residue X.I.E

def cn_ResBound (X : CData) (Cres : ℝ) : Prop := cn_res X ≤ (Cres * Real.log X.I.rd) ^ (2 * X.I.f)

def CSize.KappaVol {X : CData} (S : CSize X) (Cv : ℝ) : Prop :=
  ∀ (J : ℕ) (c : Composition J), 1 ≤ J → J ≤ X.qq →
    S.kap J c ≤ cn_kapBd Cv c.blocksFun (X.I.n - X.qq) X.qq (X.I.n - 2 * J) X.I.f (X.I.rd / 2) (cn_res X)

theorem cn_one_lt_rd (I : AutInst) : 1 < I.rd := by
  have hdeg : 1 < Module.finrank ℚ I.E := by
    have h1 : Module.finrank ℚ I.F * Module.finrank I.F I.E = Module.finrank ℚ I.E := Module.finrank_mul_finrank ℚ I.F I.E
    rw [I.cm.deg2] at h1
    have h2 : 1 ≤ Module.finrank ℚ I.F := Module.finrank_pos
    omega
  have h2 := NumberField.abs_discr_gt_two hdeg
  have h3 : (2 : ℝ) < |(discr I.E : ℝ)| := by exact_mod_cast h2
  unfold AutInst.rd
  have hf : (0 : ℝ) < (I.f : ℝ) := by exact_mod_cast one_le_autInst_f I
  exact Real.one_lt_rpow (by linarith) (by positivity)

theorem cn_kappa_le (Cv Cres : ℝ) (hCv : 1 ≤ Cv) : ∃ n₁ : ℕ, ∀ (X : CData) (S : CSize X) (n₀ : ℕ) (A : ℝ), n₁ ≤ X.I.n →
    X.HypB n₀ A → S.KappaVol Cv → cn_ResBound X Cres → ∀ (J : ℕ) (c : Composition J), 1 ≤ J → J ≤ X.qq →
    S.kap J c ≤ Real.exp (-(1 / 8 * (J : ℝ) * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) := by
  obtain ⟨n₁, h⟩ := cn_kappa_num Cv Cres hCv
  refine ⟨max n₁ 4, fun X S n₀ A hn hX hK hR J c hJ1 hJq => ?_⟩
  obtain ⟨-, hq2⟩ := X.qq_spec hX
  have hn4 : 4 ≤ X.I.n := le_trans (le_max_right _ _) hn
  have h2q : 2 * X.qq ≤ X.I.n := by
    by_cases h : X.qq ≤ 1
    · omega
    · nlinarith
  have hpq : X.I.n - X.qq + X.qq = X.I.n := by omega
  have := h c.length (X.I.n - X.qq) X.qq (X.I.n - 2 * J) X.I.f c.blocksFun X.I.rd (cn_res X)
    (by rw [hpq]; exact le_trans (le_max_left _ _) hn) (by omega) (by rw [hpq]; exact hq2) c.one_le_blocksFun
    (c.length_pos_of_pos hJ1) (by rw [c.sum_blocksFun]; exact hJq) (by rw [c.sum_blocksFun]; omega) (one_le_autInst_f X.I)
    (cn_one_lt_rd X.I) (by rw [hpq]; exact hX.1.2.2.2.1) (NumberField.dedekindZeta_residue_pos _).le hR
  rw [c.sum_blocksFun, hpq] at this
  exact le_trans (hK J c hJ1 hJq) this

end Formalism.MainNotions.LeviCoordinates

end
