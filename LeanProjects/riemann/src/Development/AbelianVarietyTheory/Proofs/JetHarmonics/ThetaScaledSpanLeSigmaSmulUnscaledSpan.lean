import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.ScaledSpan

section General

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def sc (s : R) (N : Submodule R A) : Submodule R A := N.map (s • LinearMap.id)

theorem mem_sc {s : R} {N : Submodule R A} {x : A} : x ∈ sc s N ↔ ∃ y ∈ N, x = s • y := by
  simp [sc, eq_comm]

theorem sc_mul_le {s t : R} {M M' N N' : Submodule R A} (h : M ≤ sc s M') (h' : N ≤ sc t N') :
    M * N ≤ sc (s * t) (M' * N') := by
  refine Submodule.mul_le.2 fun m hm n hn => ?_
  obtain ⟨a, ha, rfl⟩ := mem_sc.1 (h hm)
  obtain ⟨b, hb, rfl⟩ := mem_sc.1 (h' hn)
  exact mem_sc.2 ⟨a * b, Submodule.mul_mem_mul ha hb, smul_mul_smul_comm s a t b⟩

theorem sc_pow_le {s : R} {M M' : Submodule R A} (h : M ≤ sc s M') (n : ℕ) :
    M ^ n ≤ sc (s ^ n) (M' ^ n) := by
  induction n with
  | zero => intro x hx; exact mem_sc.2 ⟨x, by simpa using hx, by simp⟩
  | succ n ih => rw [pow_succ, pow_succ, pow_succ]; exact sc_mul_le ih h

theorem sc_le_of_dvd {s t : R} {M N : Submodule R A} (hd : t ∣ s) (h : M ≤ N) : sc s M ≤ sc t N := by
  obtain ⟨c, rfl⟩ := hd
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_sc.1 hx
  exact mem_sc.2 ⟨c • y, N.smul_mem c (h hy), mul_smul t c y⟩

end General

variable {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem emb_WWc_le (X : WeightAlgebra.PJ D B P6 j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) :
    X.emb w (X.WWc s w) ≤ sc s (X.emb w (X.thAll w)) := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact mem_sc.2 ⟨_, ⟨y, hy, rfl⟩, by simp⟩

theorem emb_Thc_le (X : WeightAlgebra.PJ D B P6 j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) :
    X.emb w (X.Thc s w) ≤
      sc (s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n)) (X.emb w (X.shortTh w)) := by
  rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  refine mem_sc.2 ⟨_, ⟨y, hy, rfl⟩, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, mul_smul]
  exact smul_comm _ _ _

theorem nnW_eq (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {ka wL wF : WeightFamilies.Wt D j} {T n : ℕ} (h : WeightAlgebra.IsF' ka wL wF T n) :
    nnW B hinj EX ka = nnW B hinj EX wL ^ T * nnW B hinj EX wF := by
  obtain ⟨-, hP, hM⟩ := h
  have hP' : ∀ τ i, ka.aP τ i = wL.aP τ i * T + wF.aP τ i := fun τ i => by
    have := hP τ i
    zify
    linarith
  have hM' : ∀ τ i, ka.aM τ i = wL.aM τ i * T + wF.aM τ i := fun τ i => by
    have := hM τ i
    zify
    linarith
  have h1 : Dplus ka = Dplus wL * T + Dplus wF := by
    simp only [Dplus, hP', Finset.sum_add_distrib, Finset.sum_mul]
  have h2 : Dminus ka = Dminus wL * T + Dminus wF := by
    simp only [Dminus, hM', Finset.sum_add_distrib, Finset.sum_mul]
  simp only [nnW, h1, h2, Fin.prod_univ_two]
  ring

theorem nnW_ne_zero (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (w : WeightFamilies.Wt D j) : nnW B hinj EX w ≠ 0 := by
  have hn : ∀ i, EX.piG i * piBarO EX i = (D.host.g i : 𝓞 D.host.E) := fun i => by
    apply Subtype.ext
    exact EX.piG_norm i
  have hn' : ∀ i, iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) ≠ 0 := fun i => by
    rw [← map_mul, hn, map_natCast]
    exact_mod_cast (D.host.g_prime i).ne_zero
  exact Finset.prod_ne_zero_iff.2 fun i _ =>
    mul_ne_zero (pow_ne_zero _ (left_ne_zero_of_mul (hn' i))) (pow_ne_zero _ (right_ne_zero_of_mul (hn' i)))

theorem theta_le_sigma_smul : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ), WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → sigRec B hinj EX ka wL wF T ≠ 0 ∧ ∀ F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T, ∃ G ∈ thetaPlain X ka wL wF T, F = sigRec B hinj EX ka wL wF T • G := by
  intro D B P6 j X hinj EX p ka wL wF T hF hn hT
  refine ⟨?_, fun F hF' => mem_sc.1 (?_ : F ∈ sc _ _)⟩
  · refine mul_ne_zero (nnW_ne_zero B hinj EX ka) (Nat.cast_ne_zero.2 ?_)
    have hq : D.host.q ≠ 0 := (D.host.hyp.1 : D.host.q.Prime).ne_zero
    have hd : D.host.d ≠ 0 := (D.host.hyp.2.1 : D.host.d.Prime).ne_zero
    have h0 := (D.host.g_prime 0).ne_zero
    have h1 := (D.host.g_prime 1).ne_zero
    have hS : D.host.QS ≠ 0 := D.host.QS_pos.ne'
    unfold pPow
    positivity
  · revert F
    change X.Theta _ ka wL wF T ≤ _
    have hnn := nnW_eq B hinj EX hF
    refine sup_le (sup_le ?_ ?_) ?_
    · refine (sc_mul_le (sc_pow_le (emb_WWc_le X _ wL) T) (emb_Thc_le X _ wF)).trans
        (sc_le_of_dvd ⟨(zOwnP D p wF : 𝓞 B.KO), ?_⟩ (le_sup_left.trans le_sup_left))
      simp only [scalOfP, sigRec, hnn, pPow]
      push_cast
      ring
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
      refine (sc_mul_le (sc_pow_le (emb_WWc_le X _ wL) _) (emb_Thc_le X _ _)).trans
        (sc_le_of_dvd ⟨(zOwnP D p (X.wF0 wL wF) : 𝓞 B.KO) *
          ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * (WeightFamilies.dimY D j * wL.n)), ?_⟩
          (le_sup_right.trans le_sup_left))
      have e : (X.wF0 wL wF).n = wF.n + WeightFamilies.dimY D j * wL.n := rfl
      simp only [scalOfP, sigRec, hnn, pPow, e, Nat.add_sub_cancel_left]
      unfold WeightAlgebra.PJ.wF0
      push_cast
      ring
    · refine (emb_Thc_le X _ ka).trans
        (sc_le_of_dvd ⟨(zOwnP D p ka : 𝓞 B.KO) *
          ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * (T * wL.n)), ?_⟩ le_sup_right)
      simp only [scalOfP, sigRec, hnn, pPow, hn]
      push_cast
      ring

end GlobalTheory.ScaledSpan
