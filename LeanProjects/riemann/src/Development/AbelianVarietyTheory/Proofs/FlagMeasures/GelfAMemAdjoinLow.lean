import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PermutationWordGelfandPolynomialModShorter
import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
open GlobalTheory.SmoothForms

noncomputable section

open GlobalTheory.SmoothForms.PermWord

namespace GlobalTheory.SmoothForms.GelfGen

theorem exists_eig {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (Y : Matrix (Fin n) (Fin n) K) :
    ∃ l : Fin n → K, ∀ j : ℕ, (Y ^ j).trace = ∑ i, l i ^ j := by
  classical
  set f : Module.End K (Fin n → K) := Matrix.toLin' Y
  have htr : ∀ j, (Y ^ j).trace = ∑ μ ∈ (Formalism.SA.P.finite_eig f).toFinset,
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
    intro j
    rw [← Formalism.SA.P.trace_pow_eq_sum, ← Matrix.toLin'_pow, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin n)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  set S := (Formalism.SA.P.finite_eig f).toFinset
  let d : K → ℕ := fun μ => Module.finrank K (f.maxGenEigenspace μ)
  let σ := Σ μ : S, Fin (d μ)
  have hsum : ∀ j, ∑ x : σ, (x.1 : K) ^ j = (Y ^ j).trace := by
    intro j
    rw [htr, Fintype.sum_sigma, ← Finset.sum_coe_sort S]
    simp [d]
  have hcard : Fintype.card σ = n := by
    have := hsum 0
    simp at this
    exact_mod_cast this
  let e := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨fun i => ((e i).1 : K), fun j => by rw [← hsum, ← e.sum_comp]⟩

theorem newton_closure {K : Type} [Field K] [Algebra ℂ K] {n : ℕ} (l : Fin n → K) (P : ℕ → K → Prop)
    (h1 : P 0 1) (h0 : ∀ j, P j 0) (hadd : ∀ j x y, P j x → P j y → P j (x + y))
    (hsmul : ∀ j (c : ℂ) x, P j x → P j (c • x)) (hmul : ∀ i j x y, P i x → P j y → P (i + j) (x * y))
    (hbase : ∀ j, 1 ≤ j → j ≤ n → P j (∑ i, l i ^ j)) : ∀ j, 1 ≤ j → P j (∑ i, l i ^ j) := by
  classical
  let Q : ℕ → MvPolynomial (Fin n) ℂ → Prop := fun j p => P j (MvPolynomial.aeval l p)
  have hps : ∀ j, MvPolynomial.aeval l (MvPolynomial.psum (Fin n) ℂ j) = ∑ i, l i ^ j := by
    intro j; simp [MvPolynomial.psum]
  have qadd : ∀ j x y, Q j x → Q j y → Q j (x + y) := fun j x y hx hy => by
    simpa [Q] using hadd j _ _ hx hy
  have qC : ∀ j (c : ℂ) x, Q j x → Q j (MvPolynomial.C c * x) := fun j c x hx => by
    rw [MvPolynomial.C_mul']; simpa [Q] using hsmul j c _ hx
  have qmul : ∀ i j x y, Q i x → Q j y → Q (i + j) (x * y) := fun i j x y hx hy => by
    simpa [Q] using hmul i j _ _ hx hy
  have qsign : ∀ j m x, Q j x → Q j ((-1) ^ m * x) := fun j m x hx => by
    have : ((-1 : MvPolynomial (Fin n) ℂ)) ^ m = MvPolynomial.C ((-1) ^ m) := by simp
    rw [this]; exact qC j _ x hx
  have qsub : ∀ j x y, Q j x → Q j y → Q j (x - y) := fun j x y hx hy => by
    rw [sub_eq_add_neg, neg_eq_neg_one_mul, ← pow_one (-1 : MvPolynomial (Fin n) ℂ)]
    exact qadd j _ _ hx (qsign j 1 y hy)
  have qsum : ∀ j (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → MvPolynomial (Fin n) ℂ), (∀ a ∈ s, Q j (g a)) →
      Q j (∑ a ∈ s, g a) := fun j s g hg =>
    Finset.sum_induction _ (Q j) (qadd j) (by simpa [Q] using h0 j) hg
  have qbase : ∀ j, 1 ≤ j → j ≤ n → Q j (MvPolynomial.psum (Fin n) ℂ j) := fun j h1 h2 => by
    simpa [Q, hps] using hbase j h1 h2
  have hesymm : ∀ k, Q k (MvPolynomial.esymm (Fin n) ℂ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa [Q] using h1
      by_cases hkn : n < k
      · have : MvPolynomial.esymm (Fin n) ℂ k = 0 := by
          simp only [MvPolynomial.esymm]
          rw [Finset.powersetCard_eq_empty.2 (by rw [Finset.card_univ, Fintype.card_fin]; exact hkn), Finset.sum_empty]
        rw [this]; simpa [Q] using h0 k
      have hm := MvPolynomial.mul_esymm_eq_sum (Fin n) ℂ k
      have hQ : Q k ((k : MvPolynomial (Fin n) ℂ) * MvPolynomial.esymm (Fin n) ℂ k) := by
        rw [hm]
        refine qsign _ _ _ (qsum _ _ _ fun a ha => ?_)
        rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        rw [mul_assoc]
        refine qsign _ _ _ ?_
        have := qmul _ _ _ _ (ih a.1 ha.2) (qbase a.2 (by omega) (by omega))
        rwa [ha.1] at this
      have := qC k ((k : ℂ)⁻¹) _ hQ
      rwa [← mul_assoc, ← map_natCast MvPolynomial.C k, ← map_mul,
        inv_mul_cancel₀ (by exact_mod_cast hk.ne'), map_one, one_mul] at this
  have hpsum : ∀ k, 1 ≤ k → Q k (MvPolynomial.psum (Fin n) ℂ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hkn : k ≤ n
      · exact qbase k hk hkn
      rw [MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) ℂ k (by omega)]
      refine qsub _ _ _ ?_ (qsum _ _ _ fun a ha => ?_)
      · rw [mul_assoc, ← map_natCast MvPolynomial.C k]
        exact qsign _ _ _ (qC _ _ _ (hesymm k))
      · rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_Ioo] at ha
        rw [mul_assoc]
        refine qsign _ _ _ ?_
        have := qmul _ _ _ _ (hesymm a.1) (ih a.2 (by omega) (by omega))
        rwa [ha.1] at this
  intro j hj
  simpa [Q, hps] using hpsum j hj

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem trace_symb (E : Fin n → Fin n → A) (k : ℕ) :
    ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      (((Matrix.of (gen n)) ^ (k + 1)).trace, c) ∈ symb E (k + 1) := by
  set C := Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val)
  let R := MvPolynomial (Fin n × Fin n) ℂ
  let K := AlgebraicClosure (FractionRing R)
  have hinj : Function.Injective (algebraMap R K) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) K]
    exact (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective _ _)
  obtain ⟨l, hl⟩ := exists_eig ((Matrix.of (gen n)).map (algebraMap R K))
  have htr : ∀ j, algebraMap R K ((Matrix.of (gen n)) ^ j).trace = ∑ i, l i ^ j := by
    intro j
    rw [← hl, ← Matrix.map_pow]
    simp [Matrix.trace, map_sum]
  let P : ℕ → K → Prop := fun j p => ∃ q : R, ∃ c ∈ C, algebraMap R K q = p ∧ (q, c) ∈ symb E j
  have key := newton_closure l P
    ⟨1, 1, one_mem _, map_one _, Submodule.subset_span ⟨[], rfl, by simp [wd]⟩⟩
    (fun j => ⟨0, 0, zero_mem _, map_zero _, zero_mem _⟩)
    (by
      rintro j _ _ ⟨q, c, hc, rfl, h⟩ ⟨q', c', hc', rfl, h'⟩
      exact ⟨q + q', c + c', add_mem hc hc', map_add _ _ _, by simpa using add_mem h h'⟩)
    (by
      rintro j a _ ⟨q, c, hc, rfl, h⟩
      refine ⟨a • q, a • c, Subalgebra.smul_mem _ hc a, ?_, by simpa using Submodule.smul_mem _ a h⟩
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def])
    (by
      rintro i j _ _ ⟨q, c, hc, rfl, h⟩ ⟨q', c', hc', rfl, h'⟩
      exact ⟨q * q', c * c', mul_mem hc hc', map_mul _ _ _, by simpa using symb_mul E h h'⟩)
    (by
      intro j hj1 hjn
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      refine ⟨_, gelfA E k, Algebra.subset_adjoin ⟨⟨k, by omega⟩, rfl⟩, htr _, ?_⟩
      rw [trace_pow_eq]
      unfold gelfA
      exact sum_mem_symb E (fun idx : Fin (k + 1) → Fin n => idx) fun idx a => idx (a + 1))
    (k + 1) (by omega)
  obtain ⟨q, c, hc, hq, h⟩ := key
  rw [← htr] at hq
  rw [hinj hq] at h
  exact ⟨c, hc, h⟩

theorem exists_symb_low (E : Fin n → Fin n → A) (d : ℕ)
    (π : Equiv.Perm (Fin d)) : ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      (∑ K : Fin d → Fin n, (List.ofFn fun a => gen n (K (π a)) (K a)).prod, c) ∈ symb E d := by
  have key := perm_sum_mem (Matrix.of (gen n))
    (fun j p => ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val), (p, c) ∈ symb E j)
    ⟨1, one_mem _, Submodule.subset_span ⟨[], rfl, by simp [wd]⟩⟩
    (by
      rintro k j p ⟨c, hc, h⟩
      obtain ⟨c', hc', h'⟩ := trace_symb E k
      exact ⟨c' * c, mul_mem hc' hc, by rw [← Prod.mk_mul_mk]; exact symb_mul E h' h⟩)
    d π (fun _ => 0)
  simp only [zero_add, pow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    Matrix.of_apply] at key
  simp only [List.prod_ofFn]
  exact key

theorem permWord_low {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) (d : ℕ) (π : Equiv.Perm (Fin d)) :
    ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      wordMap E d (permMat n d π) - c ∈ filt E d := by
  obtain ⟨c, hc, h⟩ := exists_symb_low E d π
  refine ⟨c, hc, shorter_le_filt E d ?_⟩
  have h2 := symb_sub hE (sum_mem_symb E (fun (K : Fin d → Fin n) a => K (π a)) fun K => K)
  have h1 := symb_sub hE h
  have h3 := sub_mem h2 h1
  rw [sub_sub_sub_cancel_right] at h3
  rw [wordMap_permMat]
  exact h3

theorem low_le (E : Fin n → Fin n → A) :
    Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) ≤ Algebra.adjoin ℂ (Set.range (gelfA E)) :=
  Algebra.adjoin_mono (by rintro _ ⟨k, rfl⟩; exact ⟨k.val, rfl⟩)

theorem central_of_filt_low {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) (d : ℕ) :
    ∀ z ∈ filt E d, (∀ a b, E a b * z = z * E a b) →
      z ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) := by
  induction d with
  | zero =>
    intro z hz _
    have : filt E 0 ≤ ⊥ := iSup₂_le fun k hk => absurd hk (Nat.not_lt_zero k)
    rw [(Submodule.mem_bot ℂ).1 (this hz)]
    exact zero_mem _
  | succ d ih =>
    intro z hz hc
    obtain ⟨_, ⟨M, rfl⟩, y, hy, rfl⟩ := Submodule.mem_sup.1 (filt_succ d hz)
    obtain ⟨M₀, h1, h2⟩ := GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint _ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
      ((filt E d).comap (wordMap E d))
      (by rintro _ ⟨p, rfl⟩; exact ⟨(p.2, p.1), (polar_conjTranspose d p.1 p.2).symm⟩)
      (by
        rintro _ ⟨p, rfl⟩ N hN
        rw [Submodule.mem_comap, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
        exact filt_ad hE d _ _ hN) M
      (by
        rintro _ ⟨p, rfl⟩
        rw [Submodule.mem_comap, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
        have h3 := neg_mem (filt_ad hE d p.1 p.2 hy)
        have h4 := hc p.1 p.2
        rw [mul_add, add_mul] at h4
        convert h3 using 1
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, h4, add_comm])
    have h3 : M₀ ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
      refine GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span n d M₀ fun T hT => ?_
      have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) ≤
          Subalgebra.centralizer ℂ {M₀} := by
        refine Algebra.adjoin_le ?_
        rintro x hx _ rfl
        exact (h2 x hx).symm
      exact this (GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm n d T hT) _ rfl
    have h4 : Submodule.span ℂ (Set.range (permMat n d)) ≤
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val)) ⊔
          filt E d).comap (wordMap E d) := by
      rw [Submodule.span_le]
      rintro _ ⟨π, rfl⟩
      obtain ⟨c, hc1, hc2⟩ := permWord_low hE d π
      exact Submodule.mem_sup.2 ⟨c, hc1, _, hc2, by abel⟩
    obtain ⟨c, hc1, u, hu, hcu⟩ := Submodule.mem_sup.1 (h4 h3)
    have h5 : wordMap E d M + y - c ∈ filt E d := by
      have h6 : wordMap E d (M - M₀) ∈ filt E d := h1
      have := add_mem (add_mem h6 hu) hy
      convert this using 1
      rw [map_sub, ← hcu]; abel
    have h7 := ih _ h5 fun a b => by
      rw [mul_sub, sub_mul, hc, gelf_adjoin_comm hE (low_le E hc1)]
    simpa using add_mem h7 hc1

theorem gelfA_mem_filt (E : Fin n → Fin n → A) (m : ℕ) : gelfA E m ∈ filt E (m + 2) := by
  refine shorter_le_filt E _ (Submodule.sum_mem _ fun idx _ => ?_)
  rw [← wd_ofFn E (fun a : Fin (m + 1) => idx a) fun a => idx (a + 1)]
  exact wd_mem_shorter E (by simp)

end GlobalTheory.SmoothForms.GelfGen

theorem GlobalTheory.SmoothForms.gelfA_mem_adjoin_low : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A),
    Formalism.REAL.GlRel E → ∀ m : ℕ, gelfA E m ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) := by
  intro A _ _ n E hE m
  exact GlobalTheory.SmoothForms.GelfGen.central_of_filt_low hE (m + 2) _ (GlobalTheory.SmoothForms.GelfGen.gelfA_mem_filt E m)
    (GlobalTheory.T.commute_gelfandInvariantMatrixUnits_of_glRel A n E hE m)

end
