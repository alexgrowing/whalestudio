import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsReducedBasisIntegralPartOfLinearIndependen
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortIndependentIntegers

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

namespace GlobalTheory.HarmBasis

open MvPolynomial

theorem mem_HHa_of_mem_span {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    {a : T → ℕ → ℕ} {S : Set (MvPolynomial (Letter T r n) k)} (hS : S ⊆ HHa r n k cc isX a)
    {P : MvPolynomial (Letter T r n) k} (hP : P ∈ Submodule.span k S) : P ∈ HHa r n k cc isX a := by
  classical
  induction hP using Submodule.span_induction with
  | mem y hy => exact hS hy
  | zero => exact ⟨zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩
  | add y z _ _ hy hz =>
    refine ⟨add_mem hy.1 hz.1, fun σ i i' h t => ?_, fun m hm => ?_⟩
    · rw [map_add, hy.2.1 σ i i' h t, hz.2.1 σ i i' h t]
    · rcases Finset.mem_union.1 (support_add hm) with h | h
      exacts [hy.2.2 m h, hz.2.2 m h]
  | smul q y _ hy =>
    refine ⟨Submodule.smul_mem _ _ hy.1, fun σ i i' h t => ?_, fun m hm => hy.2.2 m (support_smul hm)⟩
    rw [map_smul, hy.2.1 σ i i' h t]

theorem totalDegree_le_of_rowDeg {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) :
    P.totalDegree ≤ ∑ σ, ∑ i : Fin (r σ), a σ i := by
  classical
  refine Finset.sup_le fun m hm => le_of_eq ?_
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hP m hm σ i

theorem l1At_eq_l1Norm_map {K ι : Type} [Field K] (σ : K →+* ℂ) (P : MvPolynomial ι K) :
    l1At σ P = MvPoly.l1Norm (map σ P) := by
  rw [MvPoly.l1Norm_eq_sum_of_subset (support_map_subset σ P), l1At]
  simp only [coeff_map]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mult_add_mult_conjugate (Dw : Datum H) (τ : E →+* ℂ) :
    Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ) = Dw.p + Dw.q := by
  have h2 := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hne : H.rt0 ≠ -H.rt0 := fun h => by
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    rw [h0] at h2
    have : (H.d : ℂ) = 0 := by simpa using h2.symm
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  have hc : starRingEnd ℂ H.rt0 = -H.rt0 := by
    have him := congrArg Complex.im h2
    have hre := congrArg Complex.re h2
    simp [pow_two] at him hre
    have h0 : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
    apply Complex.ext <;> simp [h0]
  have hs : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    have h := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    rw [H.sqrt_neg_disc_sq]
    simpa using h
  simp only [Datum.mult, ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hs with h | h
  · rw [if_pos h, if_neg (by rw [h, hc]; exact hne.symm)]
  · rw [if_neg (by rw [h]; exact hne.symm), if_pos (by rw [h, map_neg, hc, neg_neg]), add_comm]

theorem card_LtN (Dw : Datum H) (n : ℕ) :
    Fintype.card (LtN Dw n) = FD.fdeg E * (Dw.p + Dw.q) * n := by
  have h1 := (ComplexEmbedding.involutive_conjugate E).bijective.sum_comp Dw.mult
  have h2 : ∑ τ, (Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ)) =
      Module.finrank ℚ E * (Dw.p + Dw.q) := by
    simp only [mult_add_mult_conjugate]
    rw [Finset.sum_const, Finset.card_univ, Embeddings.card E ℂ, smul_eq_mul]
  rw [Finset.sum_add_distrib, h1] at h2
  have h3 : Module.finrank ℚ E = 2 * FD.fdeg E := by
    rw [FD.fdeg, IsTotallyComplex.finrank E]
    omega
  have h4 : ∑ τ, Dw.mult τ = FD.fdeg E * (Dw.p + Dw.q) := by
    rw [h3, mul_assoc] at h2
    omega
  rw [Fintype.card_sigma, ← h4, Finset.sum_mul]
  simp only [Fintype.card_prod, Fintype.card_fin]

theorem bound_le_exp {R d D N : ℕ} {L x Δ : ℝ} (hR : 1 ≤ R) (hd : 1 ≤ d) (hΔ : 0 < Δ)
    (hle : R ≤ d * (1 + D) ^ N) (hL : Real.log (1 + D) ≤ 2 * L) :
    (1 + D : ℝ) ^ ((N : ℝ) / 2) * (√((R + 3) / 4) * √d * ((d : ℝ) ^ 3 * Δ ^ (1 / (d : ℝ))) * Real.exp x) ≤
      Real.exp (x + 2 * N * L + 4 * Real.log d + Real.log Δ / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (1 + D : ℝ) ^ ((N : ℝ) / 2) ≤ Real.exp (N * L) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_right hL (by positivity : (0 : ℝ) ≤ (N : ℝ) / 2)
    linarith
  have h2 : √((R + 3) / 4) ≤ √d * Real.exp (N * L) := by
    have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hle' : (R : ℝ) ≤ d * (1 + D) ^ N := by exact_mod_cast hle
    refine (Real.sqrt_le_sqrt (show ((R : ℝ) + 3) / 4 ≤ d * (1 + D) ^ N by linarith)).trans ?_
    rw [Real.sqrt_mul hd0.le]
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) h1) (Real.sqrt_nonneg _)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have h3 : Real.exp (4 * Real.log d) = √d * √d * (d : ℝ) ^ 3 := by
    rw [Real.mul_self_sqrt hd0.le, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hd0]
    ring
  have h4 : Real.exp (Real.log Δ / d) = Δ ^ (1 / (d : ℝ)) := by
    rw [Real.rpow_def_of_pos hΔ, mul_one_div]
  rw [Real.exp_add, Real.exp_add, Real.exp_add, h3, h4,
    show 2 * (N : ℝ) * L = N * L + N * L by ring, Real.exp_add]
  calc _ ≤ Real.exp (N * L) * (√d * Real.exp (N * L) * √d * ((d : ℝ) ^ 3 * Δ ^ (1 / (d : ℝ))) * Real.exp x) := by
        gcongr
    _ = _ := by ring

theorem exists_reduced_basis_harmA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ), Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ (R : ℕ) (b : Fin R → MvPolynomial (LtN Dw n) c.F), (∀ i, b i ∈ harmA (Dw := Dw) c a n) ∧ (∀ P ∈ harmA (Dw := Dw) c a n, ∃ z : Fin R → ℤ, P = ∑ i, (z i : c.F) • b i) ∧ R ≤ Module.finrank ℚ c.F * (1 + DF Dw a) ^ (FD.fdeg E * (Dw.p + Dw.q) * n) ∧ ∀ i (σ : c.F →+* ℂ), l1At σ (b i) ≤ Real.exp (140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a + 2 * FD.fdeg E * (Dw.p + Dw.q : ℕ) * n * L + 4 * Real.log (Module.finrank ℚ c.F) + Real.log |((NumberField.discr c.F : ℤ) : ℝ)| / Module.finrank ℚ c.F) := by
  intro E _ _ _ H Dw l c n hn a L hL h1 h2 h3 h4
  classical
  have hsp := (GlobalTheory.StdHarm.harmA_mem_span_short E H Dw l c n).2 hn a L hL h1 h2 h3 h4
  set x : ℝ := 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a with hx
  set S : Set (MvPolynomial (LtN Dw n) c.F) := {Q | Q ∈ harmA c a n ∧
    ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ x} with hS
  have hW : ∀ P ∈ Submodule.span c.F S, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H)
      fun τ i => a (τ, i) := fun P hP => mem_HHa_of_mem_span (fun Q hQ => hQ.1.1) hP
  have hI : ∀ P, P ∈ MvPoly.integralPart (Submodule.span c.F S) ↔ P ∈ harmA (Dw := Dw) c a n := fun P =>
    ⟨fun h => ⟨hW P h.1, h.2⟩, fun h => ⟨hsp P h, h.2⟩⟩
  obtain ⟨ω, hω, hA⟩ := GlobalTheory.exists_short_independent_integers c.F
  obtain ⟨hR, b, -, hb, -⟩ := MvPoly.exists_reduced_basis_integralPart (Submodule.span c.F S) (D := DF Dw a)
    (fun P hP => totalDegree_le_of_rowDeg (hW P hP).2.2) S (fun P hP => (hI P).2 hP.1) rfl
    (B := Real.exp x) (fun P hP s => by
      rw [← l1At_eq_l1Norm_map]
      exact Real.le_exp_of_log_le (hP.2 s))
    ω (hω.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)) hA rfl
  rw [card_LtN] at hR hb
  refine ⟨_, fun i => b i, fun i => (hI _).1 (b i).2, fun P hP => ?_, hR, fun i σ => ?_⟩
  · refine ⟨b.repr ⟨P, (hI P).2 hP⟩, ?_⟩
    have h := congrArg Subtype.val (b.sum_repr ⟨P, (hI P).2 hP⟩)
    simp only [Int.cast_smul_eq_zsmul]
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h
    exact h.symm
  · rw [l1At_eq_l1Norm_map]
    refine (hb i σ).trans ((bound_le_exp (L := L) i.pos Module.finrank_pos
      (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero c.F)) hR h3).trans (le_of_eq ?_))
    congr 1
    push_cast
    ring

end GlobalTheory.HarmBasis
