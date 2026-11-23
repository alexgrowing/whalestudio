import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private lemma dim_succ_le {A : Type} [CommRing A] {P Q : Ideal A} [P.IsPrime] (h : P < Q) :
    ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ P) := by
  obtain ⟨r, hrQ, hrP⟩ := SetLike.exists_of_lt h
  have hne : Ideal.Quotient.mk P r ≠ 0 := fun h0 => hrP (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hnzd : Ideal.Quotient.mk P r ∈ nonZeroDivisors (A ⧸ P) := mem_nonZeroDivisors_of_ne_zero hne
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have hker : ∀ a ∈ Ideal.span {Ideal.Quotient.mk P r}, Ideal.Quotient.factor h.le a = 0 := by
    intro a ha
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have : Ideal.Quotient.factor h.le (Ideal.Quotient.mk P r) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hrQ
    rw [map_mul, this, mul_zero]
  have hs : Function.Surjective
      (Ideal.Quotient.lift (Ideal.span {Ideal.Quotient.mk P r}) (Ideal.Quotient.factor h.le) hker) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective h.le)
  have h2 := ringKrullDim_le_of_surjective _ hs
  exact (add_le_add_left h2 1).trans h1

private lemma exists_sep {A : Type} [CommRing A] [IsNoetherianRing A] {J Z₀ : Ideal A}
    (h₀ : Z₀ ∈ J.minimalPrimes) :
    ∃ e, e ∉ Z₀ ∧ ∀ Z₁ ∈ J.minimalPrimes, Z₁ ≠ Z₀ → e ∈ Z₁ := by
  classical
  have hfin := J.finite_minimalPrimes_of_isNoetherianRing A
  set s := hfin.toFinset.erase Z₀ with hs
  have hp : Z₀.IsPrime := h₀.1.1
  have hnot : ¬ s.inf id ≤ Z₀ := by
    intro hle
    obtain ⟨W, hW, hWle⟩ := (Ideal.IsPrime.inf_le' hp).mp hle
    have hW' := Finset.mem_erase.mp hW
    have hWm : W ∈ J.minimalPrimes := hfin.mem_toFinset.mp hW'.2
    exact hW'.1 (le_antisymm hWle (h₀.2 hWm.1 hWle) |>.symm ▸ rfl)
  obtain ⟨e, he, heZ⟩ := SetLike.not_le_iff_exists.mp hnot
  refine ⟨e, heZ, fun Z₁ h₁ hne => ?_⟩
  have : Z₁ ∈ s := Finset.mem_erase.mpr ⟨hne, hfin.mem_toFinset.mpr h₁⟩
  exact (Finset.inf_le (f := id) this) he

theorem UpperTheory.V.J.denseOf :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (B₀ B : Type) [CommRing B₀] [IsNoetherianRing B₀] [Algebra c.O B₀] [CommRing B] [Algebra c.O B]
        (φ : B₀ →ₐ[c.O] B) (J : Ideal B₀) (D : ℕ) (Gd : (B₀ →ₐ[c.O] Qbar l) → Prop), Function.Surjective φ →
        (∀ Z ∈ J.minimalPrimes, ringKrullDim (B₀ ⧸ Z) = (D : WithBot ℕ∞)) →
        (∀ b : B₀, (∀ x : B₀ →ₐ[c.O] Qbar l, J ≤ RingHom.ker x → Gd x → x b = 0) → b ∈ J) →
        ∀ Z : Ideal B, Z.IsPrime → J.map φ ≤ Z → ringKrullDim (B ⧸ Z) ≤ (D : WithBot ℕ∞) ∧
          (ringKrullDim (B ⧸ Z) = (D : WithBot ℕ∞) → ∀ b ∉ Z, ∃ y : B →ₐ[c.O] Qbar l, Z ≤ RingHom.ker y ∧ Gd (y.comp φ) ∧ y b ≠ 0) := by
  intro l _ c B₀ B _ _ _ _ _ φ J D Gd hφ hdim hdense Z hZ hJZ
  have hJZ' : J ≤ Z.comap φ := Ideal.map_le_iff_le_comap.mp hJZ
  haveI hZ' : (Z.comap φ).IsPrime := Ideal.comap_isPrime φ Z
  obtain ⟨Z₀, hZ₀, hZ₀le⟩ := Ideal.exists_minimalPrimes_le hJZ'
  haveI hp₀ : Z₀.IsPrime := hZ₀.1.1
  have hψ : Function.Surjective ((Ideal.Quotient.mk Z).comp (φ : B₀ →+* B)) :=
    Ideal.Quotient.mk_surjective.comp hφ
  have hker : RingHom.ker ((Ideal.Quotient.mk Z).comp (φ : B₀ →+* B)) = Z.comap φ := by
    ext a
    exact RingHom.mem_ker.trans Ideal.Quotient.eq_zero_iff_mem
  have hde : ringKrullDim (B ⧸ Z) = ringKrullDim (B₀ ⧸ Z.comap φ) := by
    rw [← hker]
    exact (ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hψ)).symm
  have hle : ringKrullDim (B ⧸ Z) ≤ (D : WithBot ℕ∞) := by
    rw [hde, ← hdim Z₀ hZ₀]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hZ₀le) (Ideal.Quotient.factor_surjective hZ₀le)
  refine ⟨hle, fun hD b hb => ?_⟩
  have hZeq : Z₀ = Z.comap φ := by
    by_contra hne
    have hlt : Z₀ < Z.comap φ := lt_of_le_of_ne hZ₀le hne
    have h1 := dim_succ_le hlt
    rw [← hde, hD, hdim Z₀ hZ₀] at h1
    have h2 : ((D : WithBot ℕ∞) + 1) = ((D + 1 : ℕ) : WithBot ℕ∞) := by push_cast; rfl
    rw [h2] at h1
    have h3 : ((D + 1 : ℕ) : WithBot ℕ∞) ≤ (D : WithBot ℕ∞) := h1
    have h4 : D + 1 ≤ D := by exact_mod_cast h3
    omega
  obtain ⟨b', rfl⟩ := hφ b
  have hb' : b' ∉ Z₀ := by rw [hZeq]; exact hb
  obtain ⟨e, he, hesep⟩ := exists_sep hZ₀
  have hbe : b' * e ∉ J := fun hm =>
    (hp₀.mem_or_mem (hZ₀.1.2 hm)).elim hb' he
  have hx : ∃ x : B₀ →ₐ[c.O] Qbar l, J ≤ RingHom.ker x ∧ Gd x ∧ x (b' * e) ≠ 0 := by
    by_contra hno
    refine hbe (hdense _ fun x h1 h2 => ?_)
    by_contra h3
    exact hno ⟨x, h1, h2, h3⟩
  obtain ⟨x, hJx, hGx, hxbe⟩ := hx
  have hxb : x b' ≠ 0 := fun h0 => hxbe (by rw [map_mul, h0, zero_mul])
  have hxe : x e ≠ 0 := fun h0 => hxbe (by rw [map_mul, h0, mul_zero])
  haveI hkp : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Z₁, hZ₁, hZ₁le⟩ := Ideal.exists_minimalPrimes_le hJx
  have hZ₁eq : Z₁ = Z₀ := by
    by_contra hne
    exact hxe (hZ₁le (hesep Z₁ hZ₁ hne))
  have hZx : Z.comap φ ≤ RingHom.ker x := by rw [← hZeq, ← hZ₁eq]; exact hZ₁le
  have hkφ : RingHom.ker φ ≤ RingHom.ker x := fun a ha =>
    hZx (by
      have : φ a = 0 := ha
      show φ a ∈ Z
      rw [this]; exact Z.zero_mem)
  let y : B →ₐ[c.O] Qbar l := (Ideal.Quotient.liftₐ (RingHom.ker φ) x (fun a ha => hkφ ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom
  have hy : ∀ a, y (φ a) = x a := by
    intro a
    have e1 : (Ideal.quotientKerAlgEquivOfSurjective hφ).symm (φ a) = Ideal.Quotient.mk _ a :=
      (AlgEquiv.symm_apply_eq _).2 (Ideal.quotientKerAlgEquivOfSurjective_mk hφ a).symm
    show Ideal.Quotient.liftₐ (RingHom.ker φ) x (fun a ha => hkφ ha) ((Ideal.quotientKerAlgEquivOfSurjective hφ).symm (φ a)) = x a
    rw [e1]
    rfl
  refine ⟨y, fun z hz => ?_, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := hφ z
    show y (φ a) = 0
    rw [hy]
    exact hZx hz
  · have : y.comp φ = x := AlgHom.ext hy
    rwa [this]
  · rw [hy]; exact hxb
