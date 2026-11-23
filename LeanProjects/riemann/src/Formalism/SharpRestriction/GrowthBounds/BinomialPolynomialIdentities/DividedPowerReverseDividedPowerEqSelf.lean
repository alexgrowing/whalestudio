import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ContragredientIrreducibleGeneratedByHighestWeigh
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightEntriesBetweenExtremeHighest
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DeltaIntegralEnvelopingStable

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section ext

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def reflectedWeight (mu : Fin n → ℤ) (t : ℕ) : Fin n → ℤ :=
  fun c => if c.val < t ∨ (Fin.rev c).val < t then mu (Fin.rev c) else mu c

theorem reflectedWeight_zero (mu : Fin n → ℤ) : reflectedWeight mu 0 = mu := by
  funext c
  simp [reflectedWeight]

theorem reflectedWeight_half_eq_lowestWeight (mu : Fin n → ℤ) : reflectedWeight mu (n / 2) = lowWt mu := by
  funext c
  unfold reflectedWeight lowWt
  split_ifs with h
  · rfl
  · have h1 := Fin.val_rev c
    have h2 := c.2
    have : Fin.rev c = c := by
      apply Fin.ext
      omega
    rw [this]

theorem commute_pow_apply_of_commute {A : Type*} [AddCommGroup A] [Module (KK O) A] (X Y : Module.End (KK O) A)
    (h : ∀ x, X (Y x) = Y (X x)) (k : ℕ) (x : A) : X ((Y ^ k) x) = (Y ^ k) (X x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem dividedPower_zero_apply (E : GLOps n (KK O) V) (a b : Fin n) (x : V) : divPowE E a b 0 x = x := by
  simp [divPowE]

theorem dividedPower_eq_zero_of_annihilated (E : GLOps n (KK O) V) (a b : Fin n) {x : V} (h : E a b x = 0) {k : ℕ} (hk : 1 ≤ k) :
    divPowE E a b k x = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [divPowE, LinearMap.smul_apply]
  rw [pow_succ, Module.End.mul_apply, h, map_zero, smul_zero]

theorem dividedPower_reverse_dividedPower_eq_self [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b)
    {nu : Fin n → ℤ} {y : V} (hy : y ∈ weightSp E nu) (h0 : E a b y = 0) (k : ℕ) (hk : nu a - nu b = (k : ℤ)) :
    divPowE E a b k (divPowE E b a k y) = y := by
  rw [raise_lower_dividedPower_binomial hE hab hy k k, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, if_pos le_rfl]
  · rw [Nat.sub_self, dividedPower_zero_apply, dividedPower_zero_apply]
    have : nu a - nu b + (k : ℤ) - (k : ℤ) = (k : ℤ) := by rw [hk]; ring
    rw [this]
    have h1 : Ring.choose (k : ℤ) k = 1 := by
      rw [Ring.choose_natCast, Nat.choose_self, Nat.cast_one]
    rw [h1, Int.cast_one, one_smul]
  · intro j hj
    have hj' : j < k := Finset.mem_range.1 hj
    rw [if_pos hj'.le, dividedPower_eq_zero_of_annihilated E a b h0 (by omega), map_zero, smul_zero]

theorem reflectedWeight_succ_eq_add_root {mu : Fin n → ℤ} {t : ℕ} (a : Fin n) (ha : a.val = t) (ht : 2 * (t + 1) ≤ n) (k : ℕ)
    (hk : mu a - mu (Fin.rev a) = (k : ℤ)) :
    reflectedWeight mu t + (k : ℤ) • rootW (Fin.rev a) a = reflectedWeight mu (t + 1) := by
  funext c
  have hr := Fin.val_rev c
  have hc := c.2
  have hra := Fin.val_rev a
  simp only [Pi.add_apply, Pi.smul_apply, rootW, Pi.sub_apply, Pi.single_apply, smul_eq_mul, reflectedWeight]
  by_cases h1 : c = a
  · subst h1
    have e1 : ¬ (c = Fin.rev c) := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [if_neg e1, if_pos rfl, if_neg (by omega), if_pos (by omega)]
    linarith
  · by_cases h2 : c = Fin.rev a
    · subst h2
      rw [if_pos rfl, if_neg h1, Fin.rev_rev, if_neg (by rw [Fin.rev_rev] at hr; omega),
        if_pos (by rw [Fin.rev_rev] at hr; omega)]
      linarith
    · have h1' : c.val ≠ t := fun h => h1 (Fin.ext (h.trans ha.symm))
      have h2' : (Fin.rev c).val ≠ t := by
        intro h
        apply h2
        apply Fin.ext
        omega
      rw [if_neg h2, if_neg h1]
      have e : (c.val < t ∨ (Fin.rev c).val < t) ↔ (c.val < t + 1 ∨ (Fin.rev c).val < t + 1) := by omega
      simp only [e]
      ring

theorem exists_integral_reflected_weight_vector [CharZero (KK O)] {E : GLOps n (KK O) V} {mu : Fin n → ℤ} {v : V} (hI : IsIrrHW E mu v) (t : ℕ)
    (ht : 2 * t ≤ n) :
    ∃ y ∈ Delta (O := O) E v, y ∈ weightSp E (reflectedWeight mu t) ∧
      (∀ a : Fin n, t ≤ a.val → a < Fin.rev a → E a (Fin.rev a) y = 0) ∧ ∃ u ∈ UZmon E, u y = v := by
  induction t with
  | zero =>
    refine ⟨v, Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩, ?_, ?_, 1, Submonoid.one_mem _, rfl⟩
    · rw [reflectedWeight_zero]; exact hI.2.2.1.2.1
    · intro a _ h
      exact hI.2.2.1.2.2 a _ h
  | succ t ih =>
    obtain ⟨y, hyD, hyw, hyk, u, hu, huy⟩ := ih (by omega)
    have hE := hI.1
    let a : Fin n := ⟨t, by omega⟩
    have hra := Fin.val_rev a
    have hat : a.val = t := rfl
    have hlt : a < Fin.rev a := by
      rw [Fin.lt_def]; omega
    have hab : a ≠ Fin.rev a := ne_of_lt hlt
    have hdom : mu (Fin.rev a) ≤ mu a := hI.2.1 hlt.le
    obtain ⟨k, hk⟩ : ∃ k : ℕ, mu a - mu (Fin.rev a) = (k : ℤ) := ⟨(mu a - mu (Fin.rev a)).toNat, by omega⟩
    have hna : reflectedWeight mu t a = mu a := by
      unfold reflectedWeight
      rw [if_neg (by omega)]
    have hnb : reflectedWeight mu t (Fin.rev a) = mu (Fin.rev a) := by
      unfold reflectedWeight
      rw [if_neg (by rw [Fin.rev_rev]; omega)]
    refine ⟨divPowE E (Fin.rev a) a k y, ?_, ?_, ?_, u * divPowE E a (Fin.rev a) k, ?_, ?_⟩
    · exact delta_integral_enveloping_stable E v _ (Or.inl ⟨_, _, k, hab.symm, rfl⟩) y hyD
    · rw [← reflectedWeight_succ_eq_add_root a hat ht k hk]
      simp only [divPowE, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (integral_operator_pow_shifts_weight hE hyw _ _ k)
    · intro c hc hcr
      simp only [divPowE, LinearMap.smul_apply, map_smul]
      have hrc := Fin.val_rev c
      have hcomm : ∀ x, E c (Fin.rev c) (E (Fin.rev a) a x) = E (Fin.rev a) a (E c (Fin.rev c) x) := by
        intro x
        rw [gl_rep_commutation_apply hE c (Fin.rev c) (Fin.rev a) a x, if_neg, if_neg, add_zero, sub_zero]
        · intro h
          have := congrArg Fin.val h
          omega
        · intro h
          have := congrArg Fin.val h
          omega
      rw [commute_pow_apply_of_commute _ _ hcomm, hyk c (by omega) hcr, map_zero, smul_zero]
    · exact Submonoid.mul_mem _ hu (Submonoid.subset_closure (Or.inl ⟨_, _, k, hab, rfl⟩))
    · rw [Module.End.mul_apply, dividedPower_reverse_dividedPower_eq_self hE hab hyw (hyk a le_rfl hlt) k (by rw [hna, hnb]; exact hk), huy]

end ext

theorem lowest_weight_extremal_vector : LowestWeightExtremalVector := by
  intro p _ O _ _ _ _ _S n V _ _ _ _ E mu v hI
  have : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨y, hyD, hyw, _, u, hu, huy⟩ := exists_integral_reflected_weight_vector (O := O) hI (n / 2) (by omega)
  rw [reflectedWeight_half_eq_lowestWeight] at hyw
  exact ⟨y, hyD, hyw, u, hu, huy⟩

theorem deltaGenerated_of_extremalVector_of_dualInjective (hExt : LowestWeightExtremalVector) (hLow : DualFunctionalInjectiveOnLowestWeightSpace) : DeltaGeneratedByLowestWeightVector := by
  intro p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hv' hnorm
  have : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨hL1, hL2⟩ := hLow p O S n V E mu v v' hI hv'
  obtain ⟨w, hwD, hww, u, hu, huw⟩ := hExt p O S n V E mu v hI
  have hst := delta_integral_enveloping_stable (O := O) E v
  have h1 : (1 : KK O) ∈ v' '' (Delta (O := O) E v : Set V) := by
    rw [hnorm]; exact ⟨1, map_one _⟩
  obtain ⟨y, hyD, hy1⟩ := h1
  obtain ⟨y0, F, f, hlF, hy0, hf, he⟩ := weight_component_decomposition E hI.1.2.2 (lowWt mu) y
  have hy0D : y0 ∈ Delta (O := O) E v := lattice_weight_components_mem E _ hst (lowWt mu) F hlF y0 f hy0 hf (he ▸ hyD)
  have hv0 : v' y0 = 1 := by
    rw [he, map_add, map_sum, Finset.sum_eq_zero, add_zero] at hy1
    · exact hy1
    · intro nu hnu
      exact hL2 nu (fun e => hlF (e ▸ hnu)) (f nu) (hf nu hnu)
  have hwc : v' w ∈ Set.range (algebraMap O (KK O)) := by
    rw [← hnorm]; exact ⟨w, hwD, rfl⟩
  obtain ⟨c, hc⟩ := hwc
  have hw : w = c • y0 := by
    have h0 : w - (v' w) • y0 = 0 := by
      apply hL1 _ (Submodule.sub_mem _ hww (Submodule.smul_mem _ _ hy0))
      rw [map_sub, map_smul, hv0, smul_eq_mul, mul_one, sub_self]
    rw [← algebraMap_smul (KK O) c y0, hc]
    exact sub_eq_zero.1 h0
  refine ⟨y0, hy0D, hy0, hv0, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro x ⟨u', hu', rfl⟩
    have : u' v = c • (u' * u) y0 := by
      rw [← huw, hw, ← algebraMap_smul (KK O) c y0, map_smul, map_smul, algebraMap_smul, Module.End.mul_apply]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u' * u, Submonoid.mul_mem _ hu' hu, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro x ⟨u', hu', rfl⟩
    exact integral_enveloping_preserves_submodule hst hu' y0 hy0D

theorem integral_lattice_bidual : LatticeBiduality := by
  classical
  intro O _ _ _ V _ _ _ _ M hfg hspan
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  ext x
  constructor
  · intro hx φ hφ
    exact hφ x hx
  · intro hx
    have : Module.Finite O M := Module.Finite.iff_fg.2 hfg
    have htf : Module.IsTorsionFree O V := by
      refine Module.IsTorsionFree.of_smul_eq_zero fun c y h => ?_
      rw [← algebraMap_smul (KK O) c y, smul_eq_zero] at h
      rcases h with h | h
      · exact Or.inl (hinj (by rw [h, map_zero]))
      · exact Or.inr h
    have htfM : Module.IsTorsionFree O M :=
      Function.Injective.moduleIsTorsionFree (M.subtype) (Submodule.injective_subtype M) (fun _ _ => rfl)
    obtain ⟨d, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := M)
    set bV : Fin d → V := fun i => (b i : V) with hbV
    have hMspan : Submodule.span O (Set.range bV) = M := by
      have h1 : Set.range bV = M.subtype '' Set.range b := by
        rw [← Set.range_comp]; rfl
      rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
    have hLIO : LinearIndependent O bV :=
      b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
    have hLIK : LinearIndependent (KK O) bV := (LinearIndependent.iff_fractionRing O (KK O)).1 hLIO
    have hsp : ⊤ ≤ Submodule.span (KK O) (Set.range bV) := by
      rw [← hspan]
      refine Submodule.span_le.2 ?_
      intro y hy
      rw [SetLike.mem_coe, ← hMspan] at hy
      exact Submodule.span_le_restrictScalars O (KK O) _ hy
    let Bs : Module.Basis (Fin d) (KK O) V := Module.Basis.mk hLIK hsp
    have hBs : ∀ i, Bs i = bV i := fun i => Module.Basis.mk_apply hLIK hsp i
    have hcoord : ∀ i, ∀ y ∈ M, Bs.coord i y ∈ Set.range (algebraMap O (KK O)) := by
      intro i y hy
      rw [← hMspan] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        rw [← hBs j, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
        split_ifs
        · exact ⟨1, map_one _⟩
        · exact ⟨0, map_zero _⟩
      | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, ha⟩ := hy
        obtain ⟨c, hc⟩ := hz
        exact ⟨a + c, by rw [map_add, map_add, ha, hc]⟩
      | smul a y _ hy =>
        obtain ⟨c, hc⟩ := hy
        exact ⟨a * c, by rw [← algebraMap_smul (KK O) a y, map_smul, map_mul, hc, smul_eq_mul]⟩
    have hxs : x = ∑ i, Bs.coord i x • Bs i := (Bs.sum_repr x).symm
    rw [SetLike.mem_coe, hxs]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hx (Bs.coord i) (hcoord i)
    rw [← hc, algebraMap_smul, hBs]
    exact Submodule.smul_mem _ _ (b i).2

end Formalism.MainNotions.G.ColumnFamilies
