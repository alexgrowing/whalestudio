import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CRes

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cUnit :
    UpperTheory.V.ZK.Cl.CUnit := by
  intro L F _ _ _ _ _ k _ r b hb q v
  obtain ⟨_, hmul, hone, hmem, hinv, hadd, hpow⟩ := cAct L F
  have hres := (cRes L F k r).2.2.2 b hb |>.2
  have h1 : ∀ P : HeightOneSpectrum (𝓞 F), ordP P 1 = 0 := fun P => by
    simpa using hpow P 1 0
  let U : Subgroup Fˣ :=
    { carrier := {x | IsBU b x}
      mul_mem' := fun {x y} hx hy P hP => by rw [hadd, hx P hP, hy P hP, add_zero]
      one_mem' := fun P _ => h1 P
      inv_mem' := fun {x} hx P hP => by
        have := hpow P x (-1)
        rw [zpow_neg_one] at this
        rw [this, hx P hP, mul_zero] }
  have uniq : ∀ (x : Fˣ) (u u' : kˣ), Res r x u → Res r x u' → u = u' := by
    rintro x u u' ⟨a, c, hc, hxc, hac⟩ ⟨a', c', hc', hxc', hac'⟩
    have e0 : ((a * c' : 𝓞 F) : F) = ((a' * c : 𝓞 F) : F) := by
      push_cast
      linear_combination (-(c' : F)) * hxc + (c : F) * hxc'
    have e : a * c' = a' * c := by exact_mod_cast e0
    have e2 := congrArg r e
    rw [map_mul, map_mul, hac, hac'] at e2
    have : (u : k) = u' := by
      have hcc : r c * r c' ≠ 0 := mul_ne_zero hc hc'
      apply mul_right_cancel₀ hcc
      linear_combination e2
    exact Units.ext this
  classical
  let f : Fˣ → ZMod q := fun x =>
    if h : ∃ u, Res r x u then Multiplicative.toAdd (v h.choose) else 0
  have fspec : ∀ (x : Fˣ) (u : kˣ), Res r x u → f x = Multiplicative.toAdd (v u) := by
    intro x u hu
    have h : ∃ u, Res r x u := ⟨u, hu⟩
    simp only [f, dif_pos h]
    rw [uniq x _ _ h.choose_spec hu]
  have resmul : ∀ (x y : Fˣ) (u w : kˣ), Res r x u → Res r y w → Res r (x * y) (u * w) := by
    rintro x y u w ⟨a, c, hc, hxc, hac⟩ ⟨a', c', hc', hxc', hac'⟩
    refine ⟨a * a', c * c', by rw [map_mul]; exact mul_ne_zero hc hc', ?_, ?_⟩
    · push_cast
      linear_combination (y * (c' : F)) * hxc + (a : F) * hxc'
    · rw [map_mul, map_mul, hac, hac', Units.val_mul]
      ring
  refine ⟨U, f, fun x => Iff.rfl, ?_, ?_, ?_, fspec, fun x hx => hres x hx⟩
  · intro σ x hx P hP
    have hQ : actP σ (actP σ⁻¹ P) = P := by rw [← hmul, mul_inv_cancel, hone]
    have hb' : (algebraMap (𝓞 L) (𝓞 F)) b ∉ (actP σ⁻¹ P).asIdeal := by
      rw [← hmem σ (actP σ⁻¹ P) b, hQ]
      exact hP
    have := hinv σ (actP σ⁻¹ P) x
    rw [hQ] at this
    rw [this]
    exact hx _ hb'
  · intro x hx y hy
    obtain ⟨u, hu⟩ := hres x hx
    obtain ⟨w, hw⟩ := hres y hy
    rw [fspec _ _ (resmul x y u w hu hw), fspec _ _ hu, fspec _ _ hw, map_mul, toAdd_mul]
  · have h11 : Res r 1 1 := ⟨1, 1, by simp, by simp, by simp⟩
    rw [fspec _ _ h11, map_one, toAdd_one]
