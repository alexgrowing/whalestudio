import ReciprocityTheory.Chebotarev.EulerFin

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem exists_smooth {E : Type} [Field E] [NumberField E] (a : NZIdeal E) : ∃ S : Finset (Prm E), Smooth S a.1 := by
  have hfin := Ideal.finite_factors (R := 𝓞 E) (I := a.1) a.2
  exact ⟨hfin.toFinset, fun q hq => hfin.mem_toFinset.mpr hq⟩

theorem Smooth.mono {E : Type} [Field E] [NumberField E] {S T : Finset (Prm E)} {a : Ideal (𝓞 E)}
    (h : Smooth S a) (hST : S ⊆ T) : Smooth T a := fun q hq => hST (h q hq)

theorem euler_hasProd {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1) :
    HasProd (fun q : Prm E => (1 - f q.asIdeal)⁻¹) (∑' a : NZIdeal E, f a.1) := by
  unfold HasProd
  simp only [SummationFilter.unconditional_filter]
  have key : (fun S : Finset (Prm E) => ∏ q ∈ S, (1 - f q.asIdeal)⁻¹) =
      fun S => ∑' a : NZIdeal E, Set.indicator {a : NZIdeal E | Smooth S a.1} (fun a => f a.1) a := by
    funext S
    exact (euler_finite f hf1 hmul hsum hlt S).tsum_eq.symm
  rw [key]
  refine tendsto_tsum_of_dominated_convergence (bound := fun a : NZIdeal E => ‖f a.1‖) hsum ?_ ?_
  · intro a
    obtain ⟨S0, hS0⟩ := exists_smooth a
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop S0] with S hS
    have : a ∈ {a : NZIdeal E | Smooth S a.1} := Smooth.mono hS0 hS
    rw [Set.indicator_of_mem this]
  · exact Eventually.of_forall fun S a => norm_indicator_le_norm_self _ _

theorem euler_exp_log {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1) :
    Complex.exp (∑' q : Prm E, -Complex.log (1 - f q.asIdeal)) = ∑' a : NZIdeal E, f a.1 := by
  have hinj : Function.Injective (fun q : Prm E => (⟨q.asIdeal, q.ne_bot⟩ : NZIdeal E)) := by
    intro q q' h
    exact IsDedekindDomain.HeightOneSpectrum.ext (congrArg Subtype.val h)
  have hs1 : Summable (fun q : Prm E => ‖f q.asIdeal‖) := by
    have h := hsum.comp_injective hinj
    exact h
  have hs2 : Summable (fun q : Prm E => -f q.asIdeal) := (Summable.of_norm hs1).neg
  have hs3 : Summable (fun q : Prm E => -Complex.log (1 - f q.asIdeal)) := by
    have := (Complex.summable_log_one_add_of_summable hs2).neg
    simp only [← sub_eq_add_neg] at this
    exact this
  have hP := hs3.hasSum.cexp
  have hne : ∀ q : Prm E, 1 - f q.asIdeal ≠ 0 := by
    intro q h
    have h1 : f q.asIdeal = 1 := (sub_eq_zero.mp h).symm
    have := hlt q
    rw [h1, norm_one] at this
    exact lt_irrefl _ this
  have hP' : HasProd (fun q : Prm E => (1 - f q.asIdeal)⁻¹)
      (Complex.exp (∑' q : Prm E, -Complex.log (1 - f q.asIdeal))) := by
    have e : (Complex.exp ∘ fun q : Prm E => -Complex.log (1 - f q.asIdeal)) =
        fun q : Prm E => (1 - f q.asIdeal)⁻¹ := by
      funext q
      rw [Function.comp_apply, Complex.exp_neg, Complex.exp_log (hne q)]
    rw [e] at hP
    exact hP
  exact hP'.unique (euler_hasProd f hf1 hmul hsum hlt)

end ReciprocityTheory.Cheb
