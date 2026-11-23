import Formalism.PadicSubsetSums.CentralIdempotents.GL2UnipotentBruhatDecomposition

namespace Formalism.IrreducibleCountingLemmas.WindowSums

namespace ConcreteDictionaryLemmas
open PowerSeries

section ode
variable {R : Type*} [CommRing R] [IsAddTorsionFree R]

theorem ode_coeff (c : R) (f : R⟦X⟧) (hf : (1 + X) * d⁄dX R f = C c * f) (n : ℕ) :
    ((n : R) + 1) * coeff (n + 1) f = (c - n) * coeff n f := by
  have h := congrArg (coeff n) hf
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul] at h
  cases n with
  | zero =>
    simp only [coeff_zero_X_mul, add_zero] at h
    simp only [Nat.cast_zero, zero_add, sub_zero, one_mul] at h ⊢
    simpa using h
  | succ m =>
    rw [coeff_succ_X_mul, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h

theorem ode_unique (c : R) (f g : R⟦X⟧) (hf : (1 + X) * d⁄dX R f = C c * f)
    (hg : (1 + X) * d⁄dX R g = C c * g) (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have h1 := ode_coeff c f hf n
    have h2 := ode_coeff c g hg n
    rw [ih, ← h2] at h1
    have h3 : (n + 1) • coeff (n + 1) f = (n + 1) • coeff (n + 1) g := by
      simpa [nsmul_eq_mul] using h1
    exact nsmul_right_injective (Nat.succ_ne_zero n) h3

end ode

variable {l : ℕ} [Fact l.Prime]

theorem bin_ode (c : ℤ_[l]) :
    (1 + X) * d⁄dX ℤ_[l] (binomialSeries ℤ_[l] c) = C c * binomialSeries ℤ_[l] c := by
  ext n
  have key : ∀ n : ℕ, ((n : ℤ_[l]) + 1) * Ring.choose c (n + 1) = Ring.choose c n * (c - n) := by
    intro n
    have := Ring.choose_smul_choose c (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one, Nat.choose_succ_self_right, add_tsub_cancel_left,
      Ring.choose_one_right, nsmul_eq_mul] at this
    push_cast at this
    exact this
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul]
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
  cases n with
  | zero =>
    have := key 0
    simp only [coeff_zero_X_mul, add_zero]
    simp only [Nat.cast_zero, zero_add, sub_zero, one_mul] at this ⊢
    rw [mul_one, this, mul_comm]
  | succ m =>
    rw [coeff_succ_X_mul, coeff_derivative]
    simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
    have := key (m + 1)
    push_cast at this ⊢
    linear_combination this

theorem brk_const (a : ℤ_[l]) : constantCoeff (brk l a) = 0 := by
  simp [brk]

theorem brk_hasSubst (a : ℤ_[l]) : HasSubst (brk l a) :=
  HasSubst.of_constantCoeff_zero' (brk_const a)

theorem const_subst (h f : PowerSeries ℤ_[l]) (hh : constantCoeff h = 0) :
    constantCoeff (subst h f) = constantCoeff f := by
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh
  have h1 : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add]
  have h2 : constantCoeff (subst h (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero hh _ (by simp)
  rw [h2, add_zero, subst_C]
  exact constantCoeff_C _

theorem bin_comp (a b : ℤ_[l]) :
    subst (brk l b) (binomialSeries ℤ_[l] a) = binomialSeries ℤ_[l] (a * b) := by
  have hs := brk_hasSubst b
  apply ode_unique (a * b) _ _ _ (bin_ode _)
  · rw [const_subst _ _ (brk_const b)]; simp
  · rw [derivative_subst hs]
    have h1 : d⁄dX ℤ_[l] (brk l b) = d⁄dX ℤ_[l] (binomialSeries ℤ_[l] b) := by
      simp [brk]
    have h2 : (1 + X : PowerSeries ℤ_[l]).subst (brk l b) = binomialSeries ℤ_[l] b := by
      rw [subst_add hs, subst_X hs, ← map_one C, subst_C]
      simp [brk]
    have h3 := congrArg (subst (brk l b)) (bin_ode a)
    rw [subst_mul hs, subst_mul hs, h2, subst_C] at h3
    have h4 := bin_ode b
    rw [h1]
    calc (1 + X) * (subst (brk l b) (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] a)) *
            d⁄dX ℤ_[l] (binomialSeries ℤ_[l] b))
        = subst (brk l b) (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] a)) *
            ((1 + X) * d⁄dX ℤ_[l] (binomialSeries ℤ_[l] b)) := by ring
      _ = C b * (binomialSeries ℤ_[l] b *
            subst (brk l b) (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] a))) := by rw [h4]; ring
      _ = _ := by
        rw [h3, map_mul]
        have : (MvPowerSeries.C a : MvPowerSeries Unit ℤ_[l]) = (C a : PowerSeries ℤ_[l]) := rfl
        rw [this]; ring

theorem brk_comp (a b : ℤ_[l]) : subst (brk l b) (brk l a) = brk l (a * b) := by
  have hs := brk_hasSubst b
  change subst (brk l b) (binomialSeries ℤ_[l] a - 1) = _
  rw [subst_sub hs, bin_comp, ← map_one C, subst_C]
  simp [brk]

theorem brk_factor (a : ℤ_[l]) :
    ∃ g : PowerSeries ℤ_[l], brk l a = X * g ∧ constantCoeff g = a := by
  refine ⟨PowerSeries.mk fun n => coeff (n + 1) (brk l a), ?_, ?_⟩
  · ext n
    cases n with
    | zero => simp [brk_const]
    | succ m => rw [coeff_succ_X_mul, coeff_mk]
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp [brk, binomialSeries_coeff, coeff_one]

theorem exists_prim (e s : ℕ) (h : e * s = l - 1) : ∃ ω : ℤ_[l], IsPrimitiveRoot ω s := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ZMod l) (l - 1)
  have inj : Function.Injective (WittVector.teichmuller l : ZMod l →* WittVector l (ZMod l)) := by
    intro x y hxy
    have := congrArg (fun w => WittVector.coeff w 0) hxy
    simpa [WittVector.teichmuller_coeff_zero] using this
  have h1 := hζ.map_of_injective inj
  have h2 := h1.map_of_injective (f := WittVector.equiv l) (WittVector.equiv l).injective
  exact ⟨_, h2.pow (by omega) h.symm⟩

theorem inv_lemma (s : ℕ) (ω : ℤ_[l]) (hω : IsPrimitiveRoot ω s) (T : PowerSeries ℤ_[l])
    (hT : subst (brk l ω) T = T) : X ^ s ∣ T - C (constantCoeff T) := by
  have hs := brk_hasSubst ω
  obtain ⟨Dd, hDd⟩ : ∃ Dd, Dd = T - C (constantCoeff T) := ⟨_, rfl⟩
  have hD : subst (brk l ω) Dd = Dd := by
    rw [hDd, subst_sub hs, hT, subst_C]; rfl
  rw [← hDd, X_pow_dvd_iff]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hdiv : X ^ k ∣ Dd := X_pow_dvd_iff.mpr (fun m hm => ih m hm (hm.trans hk))
    obtain ⟨D', hD'⟩ := hdiv
    have hck : coeff k Dd = constantCoeff D' := by
      have := coeff_X_pow_mul D' k 0
      rw [hD']; simpa using this
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp [hDd]
    obtain ⟨g, hg, hg0⟩ := brk_factor ω
    have e1 : X ^ k * D' = X ^ k * (g ^ k * subst (brk l ω) D') := by
      calc X ^ k * D' = Dd := hD'.symm
        _ = subst (brk l ω) Dd := hD.symm
        _ = subst (brk l ω) (X ^ k * D') := congrArg _ hD'
        _ = (brk l ω) ^ k * subst (brk l ω) D' := by rw [subst_mul hs, subst_pow hs, subst_X hs]
        _ = _ := by rw [hg]; ring
    have e2 : D' = g ^ k * subst (brk l ω) D' := mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) e1
    have e3 := congrArg constantCoeff e2
    rw [map_mul, map_pow, hg0, const_subst _ _ (brk_const ω)] at e3
    have e4 : (ω ^ k - 1) * constantCoeff D' = 0 := by linear_combination -e3
    rcases mul_eq_zero.mp e4 with h | h
    · exact absurd (sub_eq_zero.mp h) (hω.pow_ne_one_of_pos_of_lt hkpos.ne' hk)
    · rw [hck, h]

theorem subst_prod {ι : Type*} (h : PowerSeries ℤ_[l]) (hs : HasSubst h) (t : Finset ι)
    (f : ι → PowerSeries ℤ_[l]) : subst h (∏ i ∈ t, f i) = ∏ i ∈ t, subst h (f i) := by
  rw [← coe_substAlgHom hs, map_prod]

end ConcreteDictionaryLemmas

open PowerSeries ConcreteDictionaryLemmas

theorem concrete_dictionary_holds : DictConcrete := by
  intro l _ e s hes u q hq
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hs1 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · omega
    · exact h
  obtain ⟨ω₀, hω₀⟩ := exists_prim (l := l) e s hes
  have hcard := hω₀.card_nthRootsFinset
  have hμ : ∀ ω, ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]) ↔ ω ^ s = 1 :=
    fun ω => Polynomial.mem_nthRootsFinset hs1 1
  choose g hg hg0 using (brk_factor (l := l))

  have hb : ∃ ε : (PowerSeries ℤ_[l])ˣ, piP l s = (ε : PowerSeries ℤ_[l]) * X ^ s := by
    have hu : IsUnit (∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]), g ω) := by
      rw [isUnit_iff_constantCoeff, map_prod]
      refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one ?_
      intro ω hω
      rw [hg0]
      exact IsUnit.of_pow_eq_one ((hμ ω).mp hω) hs1.ne'
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec, piP, Finset.prod_congr rfl (fun ω _ => hg ω), Finset.prod_mul_distrib,
      Finset.prod_const, hcard, mul_comm]
  obtain ⟨ε, hε⟩ := hb
  have hXs : X ^ s = ((ε⁻¹ : (PowerSeries ℤ_[l])ˣ) : PowerSeries ℤ_[l]) * piP l s := by
    rw [hε, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨hcard, ⟨ε, hε⟩, ?_, ?_⟩
  ·
    have hs := brk_hasSubst (l : ℤ_[l])
    have hu1 : IsUnit (subst (brk l (l : ℤ_[l])) (ε : PowerSeries ℤ_[l])) := by
      rw [isUnit_iff_constantCoeff, const_subst _ _ (brk_const _), ← isUnit_iff_constantCoeff]
      exact ε.isUnit
    have hu : IsUnit (subst (brk l (l : ℤ_[l])) (ε : PowerSeries ℤ_[l]) *
        ((ε⁻¹ : (PowerSeries ℤ_[l])ˣ) : PowerSeries ℤ_[l])) := hu1.mul (ε⁻¹).isUnit
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec]
    conv_lhs => rw [hε]
    rw [subst_mul hs, subst_pow hs, subst_X hs, ← hq, mul_pow, hXs]
    ring
  ·
    have hsu := brk_hasSubst u
    obtain ⟨T, hTdef⟩ : ∃ T, T = ∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]),
      subst (brk l ω) (g u) := ⟨_, rfl⟩
    have h1 : subst (brk l u) (piP l s) = piP l s * T := by
      rw [piP, subst_prod _ hsu, hTdef, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun ω _ => ?_
      have hsω := brk_hasSubst ω
      rw [brk_comp, mul_comm ω u, ← brk_comp u ω]
      conv_lhs => rw [hg u]
      rw [subst_mul hsω, subst_X hsω]
    have hT0 : constantCoeff T = u ^ s := by
      rw [hTdef, map_prod, Finset.prod_congr rfl
        (fun ω _ => (const_subst _ _ (brk_const ω)).trans (hg0 u)), Finset.prod_const, hcard]
    have hTinv : subst (brk l ω₀) T = T := by
      have hs0 := brk_hasSubst ω₀
      rw [hTdef, subst_prod _ hs0]
      have hstep : ∀ ω, subst (brk l ω₀) (subst (brk l ω) (g u)) =
          subst (brk l (ω * ω₀)) (g u) := by
        intro ω
        rw [subst_comp_subst_apply (brk_hasSubst ω) hs0, brk_comp]
      rw [Finset.prod_congr rfl (fun ω _ => hstep ω)]
      have h01 : ω₀ ^ s = 1 := hω₀.pow_eq_one
      have h02 : ω₀ * ω₀ ^ (s - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hs1, h01]
      refine Finset.prod_nbij' (fun ω => ω * ω₀) (fun ω => ω * ω₀ ^ (s - 1)) ?_ ?_ ?_ ?_ ?_
      · intro ω hω
        rw [hμ] at hω ⊢
        rw [mul_pow, hω, h01, one_mul]
      · intro ω hω
        rw [hμ] at hω ⊢
        rw [mul_pow, hω, ← pow_mul, mul_comm (s - 1) s, pow_mul, h01, one_pow, one_mul]
      · intro ω _
        simp only [mul_assoc, h02, mul_one]
      · intro ω _
        simp only [mul_assoc, mul_comm (ω₀ ^ (s - 1)) ω₀, h02, mul_one]
      · intro ω _
        rfl
    obtain ⟨w, hw⟩ := inv_lemma s ω₀ hω₀ T hTinv
    rw [hT0] at hw
    refine ⟨((ε⁻¹ : (PowerSeries ℤ_[l])ˣ) : PowerSeries ℤ_[l]) * w, ?_⟩
    rw [h1]
    calc piP l s * T - C (u ^ s) * piP l s = piP l s * (T - C (u ^ s)) := by ring
      _ = piP l s * (X ^ s * w) := by rw [hw]
      _ = _ := by rw [hXs]; ring

end Formalism.IrreducibleCountingLemmas.WindowSums
