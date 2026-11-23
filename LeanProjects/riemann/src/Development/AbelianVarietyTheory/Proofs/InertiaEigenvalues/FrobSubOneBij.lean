import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubIdBijOfContracting

noncomputable section
namespace GlobalTheory.PhiGam.TrivCocycle
open scoped LaurentSeries PowerSeries

theorem frob_sub_one_bij {k : Type} [Field k] {l : ℕ} [hl : Fact l.Prime] (R : RingPG k l) {n : ℕ} [NeZero n] :
    (∀ s : ZMod n → k⟦X⟧, ∃ m : ZMod n → k⟦X⟧,
      ∀ i, R.φ (vv k * (m (i - 1) : k⸨X⸩)) - vv k * (m i : k⸨X⸩) = vv k * (s i : k⸨X⸩)) ∧
    ∀ m : ZMod n → k⟦X⟧, (∀ i, R.φ (vv k * (m (i - 1) : k⸨X⸩)) = vv k * (m i : k⸨X⸩)) → m = 0 := by
  have inj : Function.Injective (fun a : k⟦X⟧ => (a : k⸨X⸩)) := HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  have hX := vv_eq_coe_X k
  have hv := vv_ne_zero k
  choose f hf using R.φ_int
  obtain ⟨u, hu⟩ := R.φ_v
  obtain ⟨l', hl'⟩ := Nat.exists_eq_add_of_le hl.out.two_le
  let T : (ZMod n → k⟦X⟧) →+ (ZMod n → k⟦X⟧) :=
    { toFun := fun m i => (u : k⟦X⟧) * PowerSeries.X ^ (l' + 1) * f (m (i - 1))
      map_zero' := by
        funext i
        apply inj
        simp [← hf]
      map_add' := by
        intro a b
        funext i
        apply inj
        simp only [Pi.add_apply, map_add, map_mul, ← hf, mul_add] }
  have hT : ∀ m i, T m i = (u : k⟦X⟧) * PowerSeries.X ^ (l' + 1) * f (m (i - 1)) := fun _ _ => rfl
  have hT' : ∀ m i, vv k * (T m i : k⸨X⸩) = R.φ (vv k * (m (i - 1) : k⸨X⸩)) := by
    intro m i
    rw [hT, map_mul R.φ, hu, hf, map_mul, map_mul, map_pow, ← hX, hl']
    ring
  haveI : IsPrecomplete (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (ZMod n → k⟦X⟧) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module _ _
  haveI : IsHausdorff (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (ZMod n → k⟦X⟧) := by
    rw [← PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have key := sub_id_bij_of_contracting (Ideal.span {(PowerSeries.X : k⟦X⟧)}) T
    (contracting_of_semi PowerSeries.X ((u : k⟦X⟧) * PowerSeries.X ^ (l' + 1)) T ?_ ?_)
  · constructor
    · intro s
      obtain ⟨m, hm⟩ := key.1 s
      refine ⟨m, fun i => ?_⟩
      rw [← hT', ← hm, Pi.sub_apply, map_sub, mul_sub]
    · intro m h
      refine key.2 m ?_
      funext i
      apply inj
      apply mul_left_cancel₀ hv
      rw [hT', h]
  · intro m
    funext i
    apply inj
    simp only [hT, Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hf, ← hX, hu, hl']
    ring
  · intro m
    refine ⟨fun i => (u : k⟦X⟧) * PowerSeries.X ^ l' * f (m (i - 1)), ?_⟩
    funext i
    simp only [hT, Pi.smul_apply, smul_eq_mul]
    ring

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] (b g : ZMod n → k⟦X⟧), (∀ i, PowerSeries.constantCoeff (g i) = 0) → (∀ i, R.γ (b i : k⸨X⸩) - (b i : k⸨X⸩) = R.φ (g (i - 1) : k⸨X⸩) - (g i : k⸨X⸩)) → ∃ (m : ZMod n → k⟦X⟧) (c : ZMod n → k), ∀ i, (b i : k⸨X⸩) = R.φ (m (i - 1) : k⸨X⸩) - (m i : k⸨X⸩) + algebraMap k k⸨X⸩ (c i) ∧ (g i : k⸨X⸩) = R.γ (m i : k⸨X⸩) - (m i : k⸨X⸩) := by
  intro k _ l _ _ R n _ b g hg hc
  have hX := vv_eq_coe_X k
  obtain ⟨h1, h2⟩ := frob_sub_one_bij R (n := n)
  choose g' hg' using fun i => PowerSeries.X_dvd_iff.2 (hg i)
  let s : ZMod n → k⟦X⟧ := fun i => PowerSeries.mk fun j => PowerSeries.coeff (j + 1) (b i)
  have hb : ∀ i, (b i : k⸨X⸩) =
      vv k * (s i : k⸨X⸩) + algebraMap k k⸨X⸩ (PowerSeries.constantCoeff (b i)) := by
    intro i
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (b i), map_add, map_mul, ← vv_eq_coe_X]
    rfl
  obtain ⟨m, hm⟩ := h1 s
  obtain ⟨κ, -, hκ⟩ := R.γ_v
  choose t ht using R.γ_int
  have hd : ∀ i, vv k * ((g' i - ((1 - κ * PowerSeries.X) * t (m i) - m i) : k⟦X⟧) : k⸨X⸩) =
      (g i : k⸨X⸩) - (R.γ (vv k * (m i : k⸨X⸩)) - vv k * (m i : k⸨X⸩)) := by
    intro i
    rw [hg' i, map_mul R.γ, hκ, ht]
    simp only [map_sub, map_mul, map_one, ← hX]
    ring
  have h0 := h2 (fun i => g' i - ((1 - κ * PowerSeries.X) * t (m i) - m i)) (by
    intro i
    rw [hd, hd, map_sub, map_sub, R.comm]
    have e := hc i
    rw [hb i, ← hm i, map_add R.γ, map_sub R.γ, AlgHom.commutes] at e
    linear_combination -e)
  refine ⟨fun i => PowerSeries.X * m i, fun i => PowerSeries.constantCoeff (b i), fun i => ?_⟩
  have e1 : ∀ j, ((PowerSeries.X * m j : k⟦X⟧) : k⸨X⸩) = vv k * (m j : k⸨X⸩) := fun j => by
    rw [map_mul, ← hX]
  simp only [e1]
  refine ⟨by rw [hm, ← hb], ?_⟩
  have e := hd i
  rw [congrFun h0 i, Pi.zero_apply, map_zero, mul_zero] at e
  exact sub_eq_zero.1 e.symm

end GlobalTheory.PhiGam.TrivCocycle
