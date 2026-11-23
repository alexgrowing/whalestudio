import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TactVanish

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem origin_part {O X B : Type} [CommRing O] [AddCommGroup X] [CommRing B] [Algebra O B]
    (W : WPres O X B) (h : W.HasOrigin) {j : X} (hj : j ≠ 0) {x : B} (hx : x ∈ W.part j) :
    W.origin h x = 0 := by
  obtain ⟨F, hF, rfl⟩ := hx
  refine (W.origin_π h F).trans ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hF 0 (by rw [map_zero]; exact hj.symm)

private theorem sep_char {O : Type} [CommRing O] (u : Oˣ) (hu : ¬ IsOfFinOrder u) {i j : ℤ × ℤ} (h : i ≠ j) :
    ∃ t : Multiplicative (ℤ × ℤ) →* Oˣ, t (Multiplicative.ofAdd i) ≠ t (Multiplicative.ofAdd j) := by
  have hinj := injective_zpow_iff_not_isOfFinOrder.2 hu
  by_cases h1 : i.1 = j.1
  · refine ⟨(zpowersHom Oˣ u).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd ℤ ℤ)), fun e => h ?_⟩
    exact Prod.ext h1 (hinj e)
  · exact ⟨(zpowersHom Oˣ u).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst ℤ ℤ)), fun e => h1 (hinj e)⟩

private theorem core {O B ι : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [CommRing B] [Algebra O B] [IsCO O B]
    [IsCO O (DualNumber O)] (u : Oˣ) (hu : ¬ IsOfFinOrder u)
    (W : WPres O (ℤ × ℤ) B) (h : W.HasOrigin) (e : ι → B) (w : ι → ℤ × ℤ) (he : ∀ a, e a ∈ W.part (w a))
    (huniq : ∀ f f' : B →ₐ[O] DualNumber O, (∀ a, f (e a) = f' (e a)) → f = f')
    (y : B →ₐ[O] DualNumber O) (j : ℤ × ℤ)
    (h1 : ∀ a, (y (e a)).fst = W.origin h (e a)) (h2 : ∀ a, w a ≠ j → (y (e a)).snd = 0) :
    (∀ x, (y x).fst = W.origin h x) ∧ ∀ i, i ≠ j → ∀ x ∈ W.part i, (y x).snd = 0 := by
  classical
  have hz : ∀ s, W.z s ∈ maximalIdeal B := by
    intro s
    by_contra hs
    have hu' : IsUnit (W.z s) := by
      rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hs
      exact hs
    have h0 : W.origin h (W.z s) = 0 := by
      rw [WPres.z, WPres.origin_π, MvPowerSeries.constantCoeff_X]
    have h3 := hu'.map (W.origin h)
    rw [h0] at h3
    exact not_isUnit_zero h3
  have hmul : ∀ (c : O) (d : DualNumber O), (algebraMap O (DualNumber O) c * d).fst = c * d.fst ∧
      (algebraMap O (DualNumber O) c * d).snd = c * d.snd := by
    intro c d
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact ⟨rfl, rfl⟩
  have hfst : ∀ x, (y x).fst = W.origin h x := by
    have key := huniq ((Algebra.ofId O (DualNumber O)).comp ((TrivSqZeroExt.fstHom O O O).comp y))
      ((Algebra.ofId O (DualNumber O)).comp (W.origin h)) (by
        intro a
        simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, h1 a])
    intro x
    have h4 := congrArg TrivSqZeroExt.fst (AlgHom.congr_fun key x)
    simpa [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl] using h4
  refine ⟨hfst, ?_⟩
  intro i hij x hx
  obtain ⟨s, hs⟩ := sep_char u hu hij
  obtain ⟨y1, hy1, -⟩ := tact O (ℤ × ℤ) B W hz (DualNumber O) y
    ((Units.map (algebraMap O (DualNumber O)).toMonoidHom).comp s)
  have hy1' : ∀ k, ∀ z ∈ W.part k, (y1 z).fst = ↑(s (Multiplicative.ofAdd k)) * (y z).fst ∧
      (y1 z).snd = ↑(s (Multiplicative.ofAdd k)) * (y z).snd := by
    intro k z hz'
    rw [hy1 k z hz']
    exact hmul _ _
  set c : O := ↑(s (Multiplicative.ofAdd j))⁻¹ with hc
  let φ : DualNumber O →ₐ[O] DualNumber O := TrivSqZeroExt.map (c • LinearMap.id)
  have hφ : ∀ d : DualNumber O, (φ d).fst = d.fst ∧ (φ d).snd = c * d.snd := by
    intro d
    exact ⟨TrivSqZeroExt.fst_map _ _, TrivSqZeroExt.snd_map _ _⟩
  have hcj : c * ↑(s (Multiplicative.ofAdd j)) = 1 := Units.inv_mul _
  have heq : φ.comp y1 = y := by
    apply huniq
    intro a
    obtain ⟨ha1, ha2⟩ := hy1' (w a) (e a) (he a)
    obtain ⟨hb1, hb2⟩ := hφ (y1 (e a))
    rw [AlgHom.comp_apply]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [hb1, ha1, hfst]
      by_cases hw : w a = 0
      · rw [hw, ofAdd_zero, map_one, Units.val_one, one_mul]
      · rw [origin_part W h hw (he a), mul_zero]
    · rw [hb2, ha2]
      by_cases hw : w a = j
      · rw [hw, ← mul_assoc, hcj, one_mul]
      · rw [h2 a hw, mul_zero, mul_zero]
  have hx1 := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun heq x)
  rw [AlgHom.comp_apply, (hφ _).2, (hy1' i x hx).2, ← mul_assoc] at hx1
  have hne : c * ↑(s (Multiplicative.ofAdd i)) - 1 ≠ 0 := by
    intro h0
    apply hs
    apply Units.ext
    have h5 : c * ↑(s (Multiplicative.ofAdd i)) = c * ↑(s (Multiplicative.ofAdd j)) := by
      rw [hcj]
      exact sub_eq_zero.mp h0
    exact (Units.isUnit _).mul_left_cancel h5
  have h6 : (c * ↑(s (Multiplicative.ofAdd i)) - 1) * (y x).snd = 0 := by
    rw [sub_mul, one_mul, hx1, sub_self]
  exact (mul_eq_zero.mp h6).resolve_left hne

private theorem ex_unit (l : ℕ) [hl : Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : ∃ u : Oˣ, ¬ IsOfFinOrder u := by
  obtain ⟨hinj, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l O
  have hnd : ¬ l ∣ (l + 1) := by
    intro h
    have h' := (Nat.dvd_add_right (dvd_refl l)).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h')
  obtain ⟨u, hu⟩ := hunit (l + 1) hnd
  refine ⟨u, ?_⟩
  intro hfin
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  haveI : CharZero O := charZero_of_injective_algebraMap hinj
  have h1 : ((l + 1 : ℕ) : O) ^ n = 1 := by
    rw [← hu, ← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  have h2 : (((l + 1) ^ n : ℕ) : O) = ((1 : ℕ) : O) := by
    push_cast at h1 ⊢
    exact h1
  rcases Nat.pow_eq_one.mp (Nat.cast_injective h2) with h3 | h3
  · exact hl.out.ne_zero (by omega)
  · exact hn.ne' h3

theorem UpperTheory.smoothPt_weightedPresentation_of_pointDerivations :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (L : LocBase D) (y : L.B →ₐ[c.O] DualNumber c.O) (j : ℤ × ℤ), (∀ (v : D.T) (g : D.Gp v) (a b : Fin 4), (y ((L.ρ v).hom g a b)).fst = D.r0 g a b ∧ (wt a b ≠ j → (y ((L.ρ v).hom g a b)).snd = 0)) → (∀ x, (y x).fst = L.W.origin L.org x) ∧ ∀ i, i ≠ j → ∀ x ∈ L.W.part i, (y x).snd = 0 := by
  intro Ω _ _ _ l _ c D _ L y j H
  haveI := c.dvr
  obtain ⟨u, hu⟩ := ex_unit l c.O
  refine core u hu L.W L.org (ι := (v : D.T) × D.Gp v × Fin 4 × Fin 4)
    (fun a => (L.ρ a.1).hom a.2.1 a.2.2.1 a.2.2.2) (fun a => wt a.2.2.1 a.2.2.2) (fun a => L.hom _ _ _ _) ?_ y j
    (fun a => (H _ _ _ _).1.trans (L.at0 _ _ _ _).symm) (fun a => (H _ _ _ _).2)
  intro f f' hff
  obtain ⟨f0, -, hf0⟩ := L.univ (DualNumber c.O) (fun v => (L.ρ v).map f) (L.eqs.map f)
  refine (hf0 f fun _ => rfl).trans (hf0 f' fun v => ?_).symm
  exact Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => (hff ⟨v, g, a, b⟩).symm)
