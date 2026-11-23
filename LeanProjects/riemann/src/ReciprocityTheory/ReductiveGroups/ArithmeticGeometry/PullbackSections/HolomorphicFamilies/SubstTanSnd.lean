import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SingleMemDegLE

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD

open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G

attribute [local instance] Over.cartesianMonoidalCategory

variable {V : Type} [CommRing V] {d : ℕ}

abbrev zk (k : Fin d) : Jet V (Fin 1 × Fin d) 1 := Ideal.Quotient.mk _ (X ((0 : Fin 1), k))

theorem fst_jetTan (k : Fin d) (w : Jet V (Fin 1 × Fin d) 1) :
    (jetTan (R := V) (m := 0) ((0 : Fin 1), k) w).fst = jetAug w :=
  DFunLike.congr_fun (Formalism.L2.Pj.SaturatedCharts.fst_comp_jetTan (V := V) ((0 : Fin 1), k)) w

theorem jetTan_mk {ι : Type} [DecidableEq ι] (ℓ : ι) (q : MvPolynomial ι V) :
    jetTan (R := V) (m := 0) ℓ (Ideal.Quotient.mk _ q) =
      aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber V) else 0) q := rfl

theorem jetAug_mk {ι : Type} (q : MvPolynomial ι V) :
    jetAug (R := V) (m := 1) (Ideal.Quotient.mk _ q) = constantCoeff q := by
  show aeval (fun _ => (0 : V)) q = constantCoeff q
  exact RingHom.congr_fun MvPolynomial.eval_zero' q

private lemma snd_tan_lemma (c x : V) : (algebraMap V (DualNumber V) c + x • DualNumber.eps).snd = x := by
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_smul, DualNumber.snd_eps, smul_eq_mul, mul_one]
  have h0 : (algebraMap V (DualNumber V) c).snd = 0 := by
    first | rfl | simp [TrivSqZeroExt.algebraMap_eq_inl] | exact TrivSqZeroExt.snd_inl _ _
  rw [h0, zero_add]

theorem snd_lin (φ : Jet V (Fin 1 × Fin d) 1 →ₐ[V] DualNumber V) (hφ : ∀ w, (φ w).fst = jetAug w)
    (w : Jet V (Fin 1 × Fin d) 1) :
    (φ w).snd = ∑ k, (φ (zk k)).snd * (jetTan (R := V) (m := 0) ((0 : Fin 1), k) w).snd := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective w
  induction q using MvPolynomial.induction_on
  next a =>
    have h1 : (Ideal.Quotient.mk _ (C a) : Jet V (Fin 1 × Fin d) 1) = algebraMap V _ a := rfl
    have h2 : (φ (Ideal.Quotient.mk _ (C a))).snd = 0 := by
      rw [h1, AlgHom.commutes]
      first | rfl | simp [TrivSqZeroExt.algebraMap_eq_inl] | exact TrivSqZeroExt.snd_inl _ _
    rw [h2]
    have hne : ∀ c : Fin d, (0 : Fin 1 × Fin d →₀ ℕ) ≠ Finsupp.single ((0 : Fin 1), c) 1 :=
      fun c => (Finsupp.single_ne_zero.2 one_ne_zero).symm
    symm
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [jetTan_mk, aeval_tan, snd_tan_lemma, MvPolynomial.coeff_C, if_neg (hne c), mul_zero]
  next p q hp hq =>
    simp only [map_add, TrivSqZeroExt.snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  next p n _ =>
    obtain ⟨a, b⟩ := n
    obtain rfl : a = 0 := Subsingleton.elim _ _
    have hz : ∀ c : Fin d, (φ (zk c)).fst = 0 := fun c => by
      rw [hφ, zk, jetAug_mk, MvPolynomial.constantCoeff_X]
    have hp : (φ (Ideal.Quotient.mk _ p)).fst = constantCoeff p := by rw [hφ, jetAug_mk]
    have hT : ∀ c : Fin d, (jetTan (R := V) (m := 0) ((0 : Fin 1), c)
        (Ideal.Quotient.mk _ (p * X ((0 : Fin 1), b)))).snd = if b = c then constantCoeff p else 0 := by
      intro c
      have hf : (jetTan (R := V) (m := 0) ((0 : Fin 1), c) (Ideal.Quotient.mk _ p)).fst = constantCoeff p := by
        rw [fst_jetTan, jetAug_mk]
      rw [map_mul, map_mul, TrivSqZeroExt.snd_mul, hf, jetTan_mk (ℓ := ((0 : Fin 1), c)) (X _), aeval_X]
      by_cases h : b = c
      · subst h; simp
      · have h' : ((0 : Fin 1), b) ≠ ((0 : Fin 1), c) := fun e => h (congrArg Prod.snd e)
        simp [h, h']
    have hm : (Ideal.Quotient.mk _ (p * X ((0 : Fin 1), b)) : Jet V (Fin 1 × Fin d) 1) =
        Ideal.Quotient.mk _ p * zk b := map_mul _ _ _
    rw [hm, map_mul, TrivSqZeroExt.snd_mul, hp, hz, ← hm]
    simp only [hT, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [smul_eq_mul, mul_comm]

theorem substTan_fst (f : Fin d → MvPowerSeries (Fin 1 × Fin d) V) (j : Fin d) (w : Jet V (Fin 1 × Fin d) 1) :
    ((jetTan (R := V) (m := 0) ((0 : Fin 1), j)).comp
      (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (f p.2)) w).fst = jetAug w := by
  rw [AlgHom.comp_apply, fst_jetTan]
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective w
  have h : (jetAug : Jet V (Fin 1 × Fin d) 1 →ₐ[V] V).comp
      (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (f p.2)) = jetAug := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    show jetAug (Ideal.Quotient.mk _ (aeval _ (X i))) = _
    rw [aeval_X, jetAug_mk, jetAug_mk]
    simp
  exact (AlgHom.comp_apply _ _ _).symm.trans (DFunLike.congr_fun h _)

theorem substTan_snd (f : Fin d → MvPowerSeries (Fin 1 × Fin d) V) (j m : Fin d) :
    ((jetTan (R := V) (m := 0) ((0 : Fin 1), j)).comp
      (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (f p.2)) (zk m)).snd =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (f m) := by
  rw [AlgHom.comp_apply]
  show (jetTan (R := V) (m := 0) ((0 : Fin 1), j) (Ideal.Quotient.mk _ (aeval _ (X ((0 : Fin 1), m))))).snd = _
  rw [aeval_X, jetTan_mk, aeval_tan]
  have hne : Finsupp.single ((0 : Fin 1), j) 1 ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
  simp [MvPolynomial.coeff_C, hne.symm, coeff_psTrunc 1 _ _ (single_mem_degLE _)]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
