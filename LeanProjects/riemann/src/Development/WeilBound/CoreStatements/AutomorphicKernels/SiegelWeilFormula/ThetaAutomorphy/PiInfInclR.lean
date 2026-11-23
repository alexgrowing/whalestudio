import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.SiegelWeilFormula.kfour PositivityTheory.SiegelWeilFormula.Place

theorem trace_inclR (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem piInf_inclR' {w : InfinitePlace F} (τ : EmbOver E w) (e : E) : piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  rw [show inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e from rfl, GlobalTheory.RealLift.KLineProof.piInf_tmul, map_one, map_one,
    one_mul]

theorem incM_mul'' {α β γ : Type} [Fintype β] (X : Matrix α β E) (Z : Matrix β γ E) :
    incM F (X * Z) = incM F X * incM F Z := by
  ext i j
  simp [incM, Matrix.mul_apply, map_sum]

theorem incM_map {α β : Type} (X : Matrix α β E) : incM F (X.map σ) = (incM F X).map (cA σ) := by
  ext i j
  simp [incM, cA_inclR']

theorem trace_incM {k : ℕ} (X : Matrix (Fin k) (Fin k) E) : (incM F X).trace = inclR (F := F) (AF F) X.trace := by
  simp [incM, Matrix.trace, map_sum]

theorem frame_sign (d : SD σ) : ∃ ε : ℤˣ, FrameEq σ d.Y d.b ε ∧
    ∀ i j, d.A.J j i = -(((ε : ℤ) : E)) * σ (d.A.J i j) := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have hσ := sigma_sigma_of_good d.ok.good
  refine ⟨ε, hε, ?_⟩
  have key : ∀ e : E, e * e = 1 → (∀ i j, σ (d.Y.J j i) = e * d.Y.J i j) → ((ε : ℤ) : E) = e := by
    intro e he hY
    have hY' : ∀ i j, d.Y.J j i = e * σ (d.Y.J i j) := fun i j => by
      rw [hY j i, ← mul_assoc, he, one_mul]
    have hD : (dbl d.Y.J)ᵀ = e • (dbl d.Y.J).map σ := by
      ext (i | i) (j | j)
      · simp [dbl, hY' i j]
      · simp [dbl]
      · simp [dbl]
      · simp [dbl, hY' i j]
    have hM : (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ)ᵀ = e • (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ).map σ := by
      have e1 : (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ).map σ = (d.b.1.map σ)ᵀ * (dbl d.Y.J).map σ * d.b.1 := by
        have h1 : ∀ {p q r : Type} [Fintype q] (P : Matrix p q E) (Q : Matrix q r E), (P * Q).map σ = P.map σ * Q.map σ :=
          fun P Q => Matrix.map_mul (f := σ.toRingHom)
        have h2 : (d.b.1.map σ).map σ = d.b.1 := by
          rw [Matrix.map_map]
          exact Matrix.ext fun i j => hσ _
        rw [h1, h1, h2, Matrix.transpose_map]
      rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_assoc]
    rw [hε] at hM
    have hn : 0 < d.n := d.ok.hn
    have := congrFun (congrFun hM (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
    simpa [Matrix.fromBlocks] using this
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have e := key (-1) (by ring) fun i j => by rw [hY i j]; ring
    intro i j
    rw [e, neg_neg, one_mul]
    exact (hA.herm j i).symm
  · have e := key 1 (by ring) fun i j => by rw [hY i j, one_mul]
    intro i j
    rw [e, hA.skew j i]
    ring

theorem gram_cond (d : SD σ) (ε : ℤˣ) (hε : ∀ i j, d.A.J j i = -(((ε : ℤ) : E)) * σ (d.A.J i j))
    (X : Matrix (Fin d.m) (Fin d.n) (AE F E)) : d.gram X X ∈ nCond σ d.n ε := by
  have hσ := sigma_sigma_of_good d.ok.good
  have hJ : (incM F d.A.J)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F d.A.J).map (cA σ)) := by
    ext i j
    simp only [Matrix.transpose_apply, incM, Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
      cA_inclR']
    rw [hε i j, map_mul, map_neg, inclR_int, neg_mul]
  show (Xᵀ * incM F d.A.J * X.map (cA σ))ᵀ = -((((ε : ℤ) : AE F E)) • (Xᵀ * incM F d.A.J * X.map (cA σ)).map (cA σ))
  have h1 : ∀ {p q r : Type} [Fintype q] (P : Matrix p q (AE F E)) (Q : Matrix q r (AE F E)),
      (P * Q).map (cA σ) = P.map (cA σ) * Q.map (cA σ) := fun P Q => Matrix.map_mul (f := (cA σ).toRingHom)
  have h2 : (X.map (cA σ)).map (cA σ) = X := by
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => cA_cA' σ hσ _
  rw [h1, h1, h2, Matrix.transpose_map, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hJ,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

theorem smul_cond {n : ℕ} (ε : ℤˣ) (c : AF F) {G : Matrix (Fin n) (Fin n) (AE F E)} (hG : G ∈ nCond σ n ε) :
    c • G ∈ nCond σ n ε := by
  have hG' : Gᵀ = -((((ε : ℤ) : AE F E)) • G.map (cA σ)) := hG
  show (c • G)ᵀ = -((((ε : ℤ) : AE F E)) • (c • G).map (cA σ))
  have e : (c • G).map (cA σ) = c • G.map (cA σ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, map_smul]
  rw [Matrix.transpose_smul, hG', e, smul_neg, smul_comm]

theorem half_eq : inclR (F := F) (AF F) (2⁻¹ : E) = algebraMap (AF F) (AE F E) (⅟(2 : AF F)) := by
  have h1 := half_two (F := F) (E := E)
  have h2 : algebraMap (AF F) (AE F E) (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]
  calc inclR (F := F) (AF F) (2⁻¹ : E) = inclR (F := F) (AF F) (2⁻¹ : E) * (2 * algebraMap (AF F) (AE F E) (⅟(2 : AF F))) := by
        rw [mul_comm 2, h2, mul_one]
    _ = _ := by rw [← mul_assoc, h1, one_mul]

theorem gram_incM (d : SD σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (Xᵀ * d.A.J * X.map σ) := by
  show (incM F X)ᵀ * incM F d.A.J * (incM F X).map (cA σ) = _
  rw [incM_mul'', incM_mul'', incM_map]
  rfl

theorem gram_mem (d : SD σ) (X : Matrix (Fin d.m) (Fin d.n) E) (T : nF σ d.Y d.b) :
    ⅟(2 : AF F) • d.gram (incM F X) (incM F X) + T.1.1 ∈ nA σ d.Y d.b ∧
      ∃ S₀ : Matrix (Fin d.n) (Fin d.n) E, ⅟(2 : AF F) • d.gram (incM F X) (incM F X) + T.1.1 = incM F S₀ := by
  obtain ⟨ε, hb, hε⟩ := frame_sign d
  have hσ := sigma_sigma_of_good d.ok.good
  obtain ⟨T₀, hT₀⟩ := (mem_nF_iff T.1).1 T.2
  refine ⟨(mem_nA_iff hσ hb _).2 (add_mem (smul_cond ε _ (gram_cond d ε hε _)) ((mem_nA_iff hσ hb _).1 T.1.2)),
    (2⁻¹ : E) • (Xᵀ * d.A.J * X.map σ) + T₀, ?_⟩
  rw [gram_incM, hT₀]
  ext i j
  simp only [incM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_add, map_mul]
  rw [Algebra.smul_def, ← half_eq]

theorem exists_twist (d : SD σ) (ε : ℤˣ) (S₀ : Matrix (Fin d.n) (Fin d.n) E) (hS : incM F S₀ ∈ nCond σ d.n ε)
    (h0 : S₀ ≠ 0) : ∃ β₀ ∈ nCond σ d.n ε, d.B.ψ (-(d.tt (incM F S₀ * β₀))) ≠ 1 := by
  have hcm := d.cm
  have hS' : (incM F S₀)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F S₀).map (cA σ)) := hS
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, S₀ i j ≠ 0 := by
    by_contra h
    exact h0 (Matrix.ext fun i j => by_contra fun hne => h ⟨i, j, hne⟩)
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ := d.B.emb
  set Sw : Matrix (Fin d.n) (Fin d.n) ℂ := (incM F S₀).map (piInf (τ w)) with hSw
  have hSwT : ∀ i j, Sw j i = -(((ε : ℤ) : ℂ)) * star (Sw i j) := fun i j => by
    have := congrArg (fun M => (M.map (piInf (τ w))) i j) hS'
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg,
      map_mul, map_intCast, piInf_cA hcm] at this
    simpa [hSw] using this
  set q : ℂ := piInf (τ w) ((incM F S₀ * incM F S₀).trace) with hq
  have hqe : q = -(((ε : ℤ) : ℂ)) * ∑ i, ∑ j, ((Complex.normSq (Sw i j) : ℝ) : ℂ) := by
    rw [hq, Matrix.trace, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    change Sw i j * Sw j i = _
    rw [hSwT i j, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  have hN : 0 < ∑ i, ∑ j, Complex.normSq (Sw i j) := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (Sw i j))
      (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i₀))
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => Complex.normSq (Sw i₀ j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j₀))
    refine Complex.normSq_pos.2 ?_
    simp only [hSw, Matrix.map_apply, incM, piInf_inclR']
    exact (map_ne_zero _).2 hij
  have hε1 : (((ε : ℤ) : ℝ)) ≠ 0 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hqre : q.re = -(((ε : ℤ) : ℝ)) * ∑ i, ∑ j, Complex.normSq (Sw i j) := by
    rw [hqe]
    simp [Complex.mul_re, ← Complex.ofReal_sum]
  have hqre0 : q.re ≠ 0 := by
    rw [hqre]
    exact mul_ne_zero (neg_ne_zero.2 hε1) hN.ne'
  set r : ℝ := -1 / (4 * q.re) with hr
  obtain ⟨s, -, hs1, hs2, -, hs4⟩ := exists_sec hcm τ
  set x : InfinitePlace F → ℂ := fun u => if u = w then (r : ℂ) else 0 with hx
  set c : AE F E := s x with hc
  have hcc : cA σ c = c := by
    refine ad_ext hcm τ (fun u => ?_) ?_
    · rw [piInf_cA hcm, hc, hs1]
      by_cases hu : u = w <;> simp [hx, hu]
    · rw [← map_smul, hc, hs2, map_zero]
  refine ⟨c • incM F S₀, ?_, ?_⟩
  · show (c • incM F S₀)ᵀ = -((((ε : ℤ) : AE F E)) • (c • incM F S₀).map (cA σ))
    have e : (c • incM F S₀).map (cA σ) = c • (incM F S₀).map (cA σ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hcc]
    rw [Matrix.transpose_smul, hS', e, smul_neg, smul_comm]
  · set z : AE F E := -(c * (incM F S₀ * incM F S₀).trace) with hz
    have e1 : -(d.tt (incM F S₀ * (c • incM F S₀))) = Algebra.trace (AF F) (AE F E) z := by
      rw [hz, map_neg, SD.tt, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hf : finOne F • z = 0 := by
      rw [hz, smul_neg, ← smul_mul_assoc, hc, hs2, zero_mul, neg_zero]
    have hw : ∀ u, u ≠ w → piInf (τ u) z = 0 := fun u hu => by
      rw [hz, map_neg, map_mul, hc, hs1]
      simp [hx, hu]
    rw [e1, psi_trace_at d.std hcm τ w z hf hw]
    have hzw : (piInf (τ w) z).re = 1 / 4 := by
      rw [hz, map_neg, map_mul, hc, hs1, ← hq]
      simp only [hx, if_pos rfl, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [hr]
      field_simp
    rw [hzw]
    intro h
    have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (((2 * (1 / 4 : ℝ)) : ℝ) : ℂ)) = -1 := by
      rw [show (2 * (1 / 4 : ℝ)) = 1 / 2 by norm_num]
      rw [show -(2 * Real.pi * Complex.I) * (((1 / 2 : ℝ)) : ℂ) = -(Real.pi * Complex.I) by push_cast; ring]
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [h2] at h
    norm_num at h

theorem orth (d : SD σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (S : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (hS : S ∈ nA σ d.Y d.b) (hr : ∃ S₀ : Matrix (Fin d.n) (Fin d.n) E, S = incM F S₀) :
    ∫ β in 𝓖, d.B.ψ (-(d.tt (S * β.1))) ∂lam = if S = 0 then 1 else 0 := by
  classical
  obtain ⟨ε, hb, -⟩ := frame_sign d
  have hσ := sigma_sigma_of_good d.ok.good
  obtain ⟨-, hH, hfd, h1⟩ := hc
  haveI := hH
  haveI : BorelSpace (nA σ d.Y d.b) := (nA_top hσ d.ok.frame).2.2.2
  obtain ⟨S₀, rfl⟩ := hr
  split_ifs with h0
  · have hone : ∀ β : nA σ d.Y d.b, d.B.ψ (-(d.tt (incM F S₀ * β.1))) = 1 := fun β => by
      rw [h0, Matrix.zero_mul, SD.tt, Matrix.trace_zero, map_zero, neg_zero, AddChar.map_zero_eq_one]
    simp_rw [hone]
    rw [setIntegral_const]
    simp [Measure.real, h1]
  · have hS0 : S₀ ≠ 0 := fun h => h0 (by rw [h]; ext i j; simp [incM])
    obtain ⟨β₀, hβ₀, hne⟩ := exists_twist d ε S₀ ((mem_nA_iff hσ hb _).1 hS) hS0
    let h : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(d.tt (incM F S₀ * β.1)))
    have hadd : ∀ β β' : nA σ d.Y d.b, h (β + β') = h β * h β' := fun β β' => by
      simp only [h, AddSubgroup.coe_add, Matrix.mul_add, SD.tt, Matrix.trace_add, map_add, neg_add,
        AddChar.map_add_eq_mul]
    have hper : ∀ g ∈ nF σ d.Y d.b, ∀ y, h (g + y) = h y := fun g hg y => by
      obtain ⟨T₀, hT₀⟩ := (mem_nF_iff g).1 hg
      rw [hadd]
      have hg1 : h g = 1 := by
        simp only [h, hT₀, ← incM_mul'', SD.tt, trace_incM, trace_inclR, ← map_neg]
        exact d.std.2.1 _
      rw [hg1, one_mul]
    exact GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist lam (nF σ d.Y d.b) hfd hper
      (c := ⟨β₀, (mem_nA_iff hσ hb _).2 hβ₀⟩) (fun y => hadd _ y) hne

end PositivityTheory.SiegelWeilFormula.Tauto

end
