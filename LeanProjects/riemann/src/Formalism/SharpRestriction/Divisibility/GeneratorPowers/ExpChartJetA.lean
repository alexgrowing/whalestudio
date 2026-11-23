import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA

open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

variable {R : Type} [CommRing R]

theorem ker_fst_sq : RingHom.ker (TrivSqZeroExt.fstHom R R R) ^ (0 + 1 + 1) = ⊥ := by
  show RingHom.ker (TrivSqZeroExt.fstHom R R R) ^ 2 = ⊥
  rw [sq, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  have hx' : x.fst = 0 := by simpa using hx
  have hy' : y.fst = 0 := by simpa using hy
  rw [Ideal.mem_bot]
  ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, hx', hy']

def tp {κ : Type} (g : κ → R) : Jet R κ (0 + 1) →ₐ[R] DualNumber R :=
  liftJet (MvPolynomial.aeval fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) (by
    apply le_bot_iff.1
    refine (Ideal.pow_right_mono (Ideal.span_le.2 ?_) _).trans (le_of_eq ker_fst_sq)
    rintro _ ⟨q, rfl⟩
    simp)

theorem tp_mk {κ : Type} (g : κ → R) (q : κ) :
    tp g (Ideal.Quotient.mk _ (MvPolynomial.X q)) = TrivSqZeroExt.inr (g q) := by
  show MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) (MvPolynomial.X q) = _
  rw [MvPolynomial.aeval_X]

theorem zero_ne_single {κ : Type} (q : κ) : (0 : κ →₀ ℕ) ≠ Finsupp.single q 1 :=
  (Finsupp.single_ne_zero.mpr one_ne_zero).symm

theorem aeval_inr {κ : Type} [Fintype κ] [DecidableEq κ] (g : κ → R) (P : MvPolynomial κ R) :
    MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) P =
      TrivSqZeroExt.inl (MvPolynomial.coeff 0 P) +
        TrivSqZeroExt.inr (∑ q, g q * MvPolynomial.coeff (Finsupp.single q 1) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.coeff_C, zero_ne_single, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
    rw [map_add, hp, hq]
    simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib, TrivSqZeroExt.inl_add,
      TrivSqZeroExt.inr_add]
    abel
  | mul_X p n hp =>
    have hc : ∀ q, MvPolynomial.coeff (Finsupp.single q 1) (p * MvPolynomial.X n) =
        if q = n then MvPolynomial.coeff 0 p else 0 := by
      intro q
      rw [MvPolynomial.coeff_mul_X']
      by_cases h : q = n
      · subst h
        simp
      · rw [if_neg h, if_neg]
        rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]
        exact fun h' => h h'.symm
    have h0 : MvPolynomial.coeff 0 (p * MvPolynomial.X n) = 0 := by
      rw [MvPolynomial.coeff_mul_X']
      simp
    rw [map_mul, hp, MvPolynomial.aeval_X, h0]
    ext <;> simp [hc, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, mul_comm]

private lemma coeff_psTrunc_lemma {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R)
    (e : κ →₀ ℕ) (he : e.degree < 0 + 1 + 1) :
    MvPolynomial.coeff e (psTrunc (0 + 1) f) = MvPowerSeries.coeff e f := by
  rw [psTrunc_eq, MvPowerSeries.coeff_truncTotal _ he]

theorem tp_psJet {κ : Type} [Fintype κ] [DecidableEq κ] (g : κ → R) (f : MvPowerSeries κ R) :
    tp g (psJet (0 + 1) f) = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff f) +
      TrivSqZeroExt.inr (∑ q, g q * MvPowerSeries.coeff (Finsupp.single q 1) f) := by
  have h1 : tp g (psJet (0 + 1) f) =
      MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) (psTrunc (0 + 1) f) := rfl
  rw [h1, aeval_inr, coeff_psTrunc_lemma f 0 (by simp [Finsupp.degree]),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  congr 2
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coeff_psTrunc_lemma f _ (by simp [Finsupp.degree_single])]

theorem jetTan_eq_tp {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) = tp (fun q => if q = ℓ then 1 else 0) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0)
      (MvPolynomial.X i) =
    MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (if q = ℓ then 1 else 0) : DualNumber R))
      (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  by_cases h : i = ℓ
  · (simp only [if_pos h]) <;> rfl
  · simp only [if_neg h, TrivSqZeroExt.inr_zero]

theorem tp_comp_jetMap {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (h : κ' → R) (a : κ → MvPowerSeries κ' R)
    (ha : ∀ p, MvPowerSeries.constantCoeff (a p) = 0) :
    (tp h).comp (jetMap (m := 0 + 1) (fun p => psTrunc (0 + 1) (a p)) (fun p => psTrunc_mem_orig (0 + 1) (a p) (ha p))) =
      tp (fun p => ∑ q, h q * MvPowerSeries.coeff (Finsupp.single q 1) (a p)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  have h1 : (jetMap (m := 0 + 1) (fun p => psTrunc (0 + 1) (a p))
      (fun p => psTrunc_mem_orig (0 + 1) (a p) (ha p))) (Ideal.Quotient.mk _ (MvPolynomial.X p)) =
        psJet (0 + 1) (a p) := by
    show (Ideal.Quotient.mk (orig R κ' ^ (0 + 1 + 1)))
      (MvPolynomial.aeval (fun p => psTrunc (0 + 1) (a p)) (MvPolynomial.X p)) = _
    rw [MvPolynomial.aeval_X] <;> rfl
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [h1, tp_psJet, ha p, tp_mk]
  simp

theorem snd_tp_psJet_subst {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (h : κ' → R)
    (a : κ → MvPowerSeries κ' R) (ha : ∀ p, MvPowerSeries.constantCoeff (a p) = 0) (f : MvPowerSeries κ R) :
    (tp h (psJet (0 + 1) (MvPowerSeries.subst a f))).snd =
      ∑ p, (∑ q, h q * MvPowerSeries.coeff (Finsupp.single q 1) (a p)) *
        MvPowerSeries.coeff (Finsupp.single p 1) f := by
  rw [psJet_subst (0 + 1) a ha f, ← AlgHom.comp_apply, tp_comp_jetMap h a ha, tp_psJet]
  simp

theorem sum_coeff_X {κ : Type} [Fintype κ] [DecidableEq κ] (h : κ → R) (s : κ) :
    ∑ q, h q * MvPowerSeries.coeff (Finsupp.single q 1) (MvPowerSeries.X s : MvPowerSeries κ R) = h s := by
  simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj]

theorem sum_coeff_variable_pair {κ₁ κ₂ : Type} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂] (h : κ₁ → κ₂ → R)
    (s : κ₁ × κ₂) :
    ∑ i, ∑ j, h i j * MvPowerSeries.coeff (Finsupp.single (i, j) 1) (MvPowerSeries.X s : MvPowerSeries (κ₁ × κ₂) R) =
      h s.1 s.2 := by
  obtain ⟨s1, s2⟩ := s
  rw [Finset.sum_eq_single s1, Finset.sum_eq_single s2]
  · simp [MvPowerSeries.coeff_X]
  · intro j _ hj
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hj]
  · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hi]
  · simp

theorem sum_coeff_X_fst {κ₁ κ₂ : Type} [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂] (u : κ₂ → R) (i : κ₁)
    (s : κ₁ × κ₂) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single (i, j) 1) (MvPowerSeries.X s : MvPowerSeries (κ₁ × κ₂) R) =
      if i = s.1 then u s.2 else 0 := by
  obtain ⟨s1, s2⟩ := s
  dsimp only
  by_cases hi : i = s1
  · subst hi
    rw [if_pos rfl, Finset.sum_eq_single s2]
    · simp [MvPowerSeries.coeff_X]
    · intro j _ hj
      simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hj]
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hi]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem lin_unit {d : ℕ} (G : FGLaw R d) (u : Fin d → R) (k : Fin d) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (G.F k) = u k := by
  classical
  have ha : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]
  have key := snd_tp_psJet_subst (fun q : Fin 1 × Fin d => u q.2)
    (fun p : Fin 2 × Fin d => (![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2) ha (G.F k)
  have hu : MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2)
      (G.F k) = MvPowerSeries.X ((0 : Fin 1), k) := G.unit k
  have inner0 : ∀ i : Fin d, ∑ q : Fin 1 × Fin d, u q.2 *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![0, pt R d 0] : Fin 2 → Pt R 1 d) 0 i) = 0 := by
    intro i
    simp
  have inner1 : ∀ i : Fin d, ∑ q : Fin 1 × Fin d, u q.2 *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![0, pt R d 0] : Fin 2 → Pt R 1 d) 1 i) = u i :=
    fun i => sum_coeff_X (fun q : Fin 1 × Fin d => u q.2) ((0 : Fin 1), i)
  rw [hu, Fintype.sum_prod_type, Fin.sum_univ_two] at key
  simp only [inner0, inner1, zero_mul, Finset.sum_const_zero, zero_add] at key
  rw [← key, tp_psJet]
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact sum_coeff_X (fun q : Fin 1 × Fin d => u q.2) ((0 : Fin 1), k)

theorem lin_comm {d : ℕ} (G : FGLaw R d) (u : Fin d → R) (k : Fin d) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (G.F k) = u k := by
  classical
  set h : Fin 2 × Fin d → R := fun q => if q.1 = 0 then u q.2 else 0 with hh
  have h_0 : ∀ j, h ((0 : Fin 2), j) = u j := fun j => by simp [hh]
  have h_1 : ∀ j, h ((1 : Fin 2), j) = 0 := fun j => by simp [hh]
  have ha : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]
  have key := snd_tp_psJet_subst h
    (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) ha (G.F k)
  have hc : MvPowerSeries.subst
      (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) (G.F k) = G.F k :=
    G.comm k
  have inner0 : ∀ i : Fin d, ∑ q : Fin 2 × Fin d, h q *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) 0 i) = 0 :=
    fun i => (sum_coeff_X h ((1 : Fin 2), i)).trans (h_1 i)
  have inner1 : ∀ i : Fin d, ∑ q : Fin 2 × Fin d, h q *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) 1 i) = u i :=
    fun i => (sum_coeff_X h ((0 : Fin 2), i)).trans (h_0 i)
  rw [hc, tp_psJet] at key
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at key
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_prod_type, Fin.sum_univ_two] at key
  simp only [inner0, inner1, h_0, h_1, zero_mul, Finset.sum_const_zero, zero_add, add_zero] at key
  rw [key]
  exact lin_unit G u k

theorem lin_F {d : ℕ} (G : FGLaw R d) (v w : Fin d → R) (k : Fin d) :
    ∑ p : Fin 2 × Fin d, (![v, w] : Fin 2 → Fin d → R) p.1 p.2 *
      MvPowerSeries.coeff (Finsupp.single p 1) (G.F k) = v k + w k := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [lin_comm G v k, lin_unit G w k]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
