import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingProdEqFactorialSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingProdEqZeroOfLongStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMultisetWordsMulFactorialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingReprMulPowerSeriesStatement

set_option autoImplicit false
noncomputable section
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical

namespace GlobalTheory.JetCalcPf

theorem prod_t_list {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I)
    (hc : ∑ i, l.count i ≤ n + 1) :
    (l.map J.t).prod = ((∏ i, (l.count i).factorial : ℕ) : R) • J.b ⟨fun i => l.count i, hc⟩ :=
  GlobalTheory.T.jet_ring_prod_eq_factorial_smul J l hc

theorem prod_t_list_eq_zero {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I)
    (hl : n + 1 < l.length) : (l.map J.t).prod = 0 :=
  GlobalTheory.T.jet_ring_prod_eq_zero_of_long J l hl

theorem card_count_mul {I : Type} [Fintype I] (k : ℕ) (ν : I → ℕ) (hν : ∑ i, ν i = k) :
    (Finset.univ.filter (fun s : Fin k → I => ∀ i, (List.ofFn s).count i = ν i)).card * ∏ i, (ν i).factorial
      = k.factorial :=
  GlobalTheory.T.card_multiset_words_mul_factorial k ν hν

theorem repr_mul_of_coeff {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (F G : MvPowerSeries I ℂ) (x y : J.B)
    (hx : ∀ ν : Idx I n, J.b.repr x ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F)
    (hy : ∀ ν : Idx I n, J.b.repr y ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) G)
    (ν : Idx I n) : J.b.repr (x * y) ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) (F * G) :=
  GlobalTheory.T.jet_ring_repr_mul_power_series J F G x y hx hy ν

theorem iterD_eq {I : Type} [Fintype I] (l : List I) (g : (I → ℂ) → ℂ) :
    iterD l g = GlobalTheory.lineDerivList ℂ (l.map fun i => (Pi.single i 1 : I → ℂ)) g := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [iterD, List.foldr_cons, List.map_cons, GlobalTheory.lineDerivList_cons] at ih ⊢; rw [← ih]; rfl

end GlobalTheory.JetCalcPf

namespace GlobalTheory.JetCalcPf

variable {I : Type} [Fintype I] {n : ℕ}

theorem sum_count (l : List I) : ∑ i, l.count i = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, ih, List.length_cons, beq_iff_eq]
    simp

theorem repr_prod_t_eq_ite_factorial (J : JetRing ℂ I n) (ν : Idx I n) {k : ℕ} (s : Fin k → I) :
    J.b.repr (∏ a, J.t (s a)) ν =
      if (∀ i, (List.ofFn s).count i = ν.1 i) then ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) else 0 := by
  have e : ∏ a, J.t (s a) = ((List.ofFn s).map J.t).prod := by
    rw [List.map_ofFn, List.prod_ofFn]; rfl
  rw [e]
  by_cases hk : k ≤ n + 1
  · have hc : ∑ i, (List.ofFn s).count i ≤ n + 1 := by rw [sum_count, List.length_ofFn]; exact hk
    rw [prod_t_list J _ hc, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hP : ∀ i, (List.ofFn s).count i = ν.1 i
    · have hν : (⟨fun i => (List.ofFn s).count i, hc⟩ : Idx I n) = ν := Subtype.ext (funext hP)
      rw [if_pos hν, if_pos hP, smul_eq_mul, mul_one]
      simp only [hP]
    · rw [if_neg hP, if_neg]
      · simp
      · intro h; exact hP fun i => congrFun (congrArg Subtype.val h) i
  · rw [prod_t_list_eq_zero J _ (by rw [List.length_ofFn]; omega), map_zero, Finsupp.zero_apply, if_neg]
    intro hP
    have h1 := ν.2
    have h2 : ∑ i, ν.1 i = k := by simp only [← hP]; rw [sum_count, List.length_ofFn]
    omega

theorem iFD_eq_iterD {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) {k : ℕ} (s : Fin k → I) (u : List I)
    (h : ∀ i, (List.ofFn s).count i = u.count i) :
    iteratedFDeriv ℂ k f 0 (fun a => (Pi.single (s a) 1 : I → ℂ)) = iterD u f 0 := by
  rw [iterD_eq, ← GlobalTheory.lineDerivList_ofFn hf]
  have hp : (List.ofFn s).Perm u := List.perm_iff_count.2 fun i => h i
  have e : List.ofFn (fun a => (Pi.single (s a) 1 : I → ℂ)) = (List.ofFn s).map fun i => (Pi.single i 1 : I → ℂ) := by
    rw [List.map_ofFn]; rfl
  rw [e]
  exact GlobalTheory.lineDerivList_perm hf (hp.map _)

theorem coeff_jet (J : JetRing ℂ I n) {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (ν : Idx I n) (u : List I)
    (hu : ∀ i, u.count i = ν.1 i) : J.b.repr (jet J f) ν = iterD u f 0 := by
  set K := ∑ i, ν.1 i with hK
  have hKn : K ≤ n + 1 := ν.2
  simp only [jet, GlobalTheory.PeriodFamily.taylor, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, repr_prod_t_eq_ite_factorial]
  rw [Finset.sum_eq_single_of_mem K (Finset.mem_range.2 (by omega))]
  · have step : ∀ s : Fin K → I, ((K.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ K f 0 (fun a => (Pi.single (s a) 1 : I → ℂ))) *
        (if (∀ i, (List.ofFn s).count i = ν.1 i) then ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) else 0) =
        if (∀ i, (List.ofFn s).count i = ν.1 i) then
          (K.factorial : ℂ)⁻¹ * iterD u f 0 * ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) else 0 := by
      intro s
      split_ifs with hP
      · rw [iFD_eq_iterD hf s u fun i => (hP i).trans (hu i).symm]
      · rw [mul_zero]
    simp only [step]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hc := card_count_mul K ν.1 rfl
    have hc' : ((Finset.univ.filter (fun s : Fin K → I => ∀ i, (List.ofFn s).count i = ν.1 i)).card : ℂ) *
        ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) = (K.factorial : ℂ) := by exact_mod_cast hc
    have hK0 : (K.factorial : ℂ) ≠ 0 := by exact_mod_cast K.factorial_ne_zero
    calc _ = ((Finset.univ.filter (fun s : Fin K → I => ∀ i, (List.ofFn s).count i = ν.1 i)).card : ℂ) *
        ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * (K.factorial : ℂ)⁻¹ * iterD u f 0 := by ring
      _ = _ := by rw [hc', mul_inv_cancel₀ hK0, one_mul]
  · intro k _ hk
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [if_neg, mul_zero]
    intro hP
    apply hk
    have := sum_count (List.ofFn s)
    rw [List.length_ofFn] at this
    rw [← this, hK]; simp only [hP]

theorem repr_jet_eq_coeff (J : JetRing ℂ I n) {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (ν : Idx I n) :
    J.b.repr (jet J f) ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) (GlobalTheory.taylor f) := by
  set m : I →₀ ℕ := Finsupp.equivFunOnFinite.symm ν.1 with hm
  have hmi : ∀ i, m i = ν.1 i := fun i => by simp [hm]
  set l := (Finsupp.toMultiset m).toList
  have hl : (l : Multiset I) = Finsupp.toMultiset m := Multiset.coe_toList _
  have hcount : ∀ i, l.count i = ν.1 i := fun i => by
    rw [← hmi, ← Finsupp.count_toMultiset, ← hl, Multiset.coe_count]
  rw [GlobalTheory.taylor_eq_taylorDir, GlobalTheory.coeff_taylorDir_eq_lineDerivList _ hf hl, ← iterD_eq, ← coeff_jet J hf ν l hcount]
  have h0 : ((∏ i, (m i).factorial : ℕ) : ℂ) ≠ 0 := GlobalTheory.cast_prod_factorial_ne_zero m
  simp only [hmi] at h0 ⊢
  rw [mul_inv_cancel_left₀ h0]

theorem jetCalc : JetCalc := by
  intro I _ n J
  refine ⟨fun f hf ν u hu => coeff_jet J hf ν u hu, fun f g hf hg => ⟨?_, ?_⟩, fun f g h => ?_, fun a => ?_,
    fun i => ?_, fun i => ?_, fun s => ?_⟩
  · refine J.b.ext_elem fun ν => ?_
    rw [repr_mul_of_coeff J _ _ _ _ (repr_jet_eq_coeff J hf) (repr_jet_eq_coeff J hg) ν,
      repr_jet_eq_coeff J (hf.mul hg), GlobalTheory.taylor_mul hf hg]
  · refine J.b.ext_elem fun ν => ?_
    rw [map_add, Finsupp.add_apply, repr_jet_eq_coeff J hf, repr_jet_eq_coeff J hg,
      repr_jet_eq_coeff J (hf.add hg), GlobalTheory.taylor_add hf hg, map_add, mul_add]
  · have e : ∀ k, iteratedFDeriv ℂ k f 0 = iteratedFDeriv ℂ k g 0 := fun k => (h.iteratedFDeriv ℂ k).eq_of_nhds
    simp only [jet, GlobalTheory.PeriodFamily.taylor, e]
  · refine J.b.ext_elem fun ν => ?_
    rw [repr_jet_eq_coeff J analyticAt_const, GlobalTheory.taylor_const, MvPowerSeries.coeff_C,
      Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hν : ν = ⟨0, by simp⟩
    · subst hν
      have h0 : Finsupp.equivFunOnFinite.symm (0 : I → ℕ) = 0 := by ext; simp
      simp [h0]
    · rw [if_neg (Ne.symm hν), if_neg, mul_zero, smul_zero]
      intro h; apply hν; apply Subtype.ext; funext i
      have := congrArg (fun m : I →₀ ℕ => m i) h
      simpa using this
  · have ha : AnalyticAt ℂ (fun z : I → ℂ => z i) 0 :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt 0
    refine J.b.ext_elem fun ν => ?_
    rw [repr_jet_eq_coeff J ha, GlobalTheory.taylor_coord, MvPowerSeries.coeff_X, JetRing.t, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases hν : ν.1 = Pi.single i 1
    · have h1 : (⟨Pi.single i 1, by simp⟩ : Idx I n) = ν := Subtype.ext hν.symm
      have h2 : Finsupp.equivFunOnFinite.symm ν.1 = Finsupp.single i 1 := by
        ext j; simp [hν, Pi.single_apply, Finsupp.single_apply, eq_comm]
      rw [if_pos h1, if_pos h2, hν, mul_one]
      have : ∀ j, (Pi.single i 1 : I → ℕ) j = 0 ∨ (Pi.single i 1 : I → ℕ) j = 1 := fun j => by
        by_cases hj : j = i <;> simp [hj]
      simp only [Nat.cast_eq_one]
      exact Finset.prod_eq_one fun j _ => by rcases this j with h | h <;> rw [h] <;> rfl
    · have h1 : (⟨Pi.single i 1, by simp⟩ : Idx I n) ≠ ν := fun h => hν (congrArg Subtype.val h).symm
      have h2 : Finsupp.equivFunOnFinite.symm ν.1 ≠ Finsupp.single i 1 := fun h => hν (by
        funext j; have := congrArg (fun m : I →₀ ℕ => m j) h; simpa [Pi.single_apply, Finsupp.single_apply, eq_comm] using this)
      rw [if_neg h1, if_neg h2, mul_zero]
  · rw [J.π_eq, JetRing.t, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
    intro h
    have := congrFun (congrArg Subtype.val h) i
    simp at this
  · have e : ∏ a, J.t (s a) = ((List.ofFn s).map J.t).prod := by
      rw [List.map_ofFn, List.prod_ofFn]; rfl
    rw [e, prod_t_list_eq_zero J _ (by rw [List.length_ofFn]; omega)]

end GlobalTheory.JetCalcPf
