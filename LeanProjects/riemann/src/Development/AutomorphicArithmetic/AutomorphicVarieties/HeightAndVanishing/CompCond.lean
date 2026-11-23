import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ProjFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem cond_dvd_iff {O : Type} [CommRing O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) {M : ℕ} (h : M ∣ N) :
    ψ.conductor ∣ M ↔ ∀ u, ZMod.unitsMap h u = 1 → ψ.toUnitHom u = 1 := by
  rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ h, DirichletCharacter.mem_conductorSet_iff,
    DirichletCharacter.factorsThrough_iff_ker_unitsMap h]
  rfl

private theorem comp_hom {O : Type} [CommRing O] {N : ℕ} (r : ℕ) (χ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (comp r χ).toUnitHom u = χ.toUnitHom (proj r N u) := by
  unfold comp
  rw [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]
  rfl

private theorem mul_hom {O : Type} [CommRing O] {N : ℕ} (χ ψ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (χ * ψ).toUnitHom u = χ.toUnitHom u * ψ.toUnitHom u := by
  ext
  simp

private theorem rest_hom {O : Type} [CommRing O] {N : ℕ} (χ ψ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (χ * ψ⁻¹).toUnitHom u * ψ.toUnitHom u = χ.toUnitHom u := by
  rw [← mul_hom, inv_mul_cancel_right]

private theorem split_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {r : ℕ} (hr : r.Prime) :
    (comp r χ).conductor = ordProj[r] χ.conductor ∧ (χ * (comp r χ)⁻¹).conductor = ordCompl[r] χ.conductor := by
  obtain ⟨-, -, hid, -, -, hra, hke, -, hnat⟩ := projFacts N r hr
  have hc := (cond_dvd_iff χ χ.conductor_dvd_level).1 dvd_rfl
  have hc' : ∀ u, ZMod.unitsMap χ.conductor_dvd_level u = 1 → (comp r χ).toUnitHom u = 1 := by
    intro u hu
    rw [comp_hom]
    apply hc
    rw [hnat, hu, map_one]
  have ha1 : (comp r χ).conductor ∣ χ.conductor := (cond_dvd_iff _ χ.conductor_dvd_level).2 hc'
  have hb1 : (χ * (comp r χ)⁻¹).conductor ∣ χ.conductor := by
    refine (cond_dvd_iff _ χ.conductor_dvd_level).2 fun u hu => ?_
    have := rest_hom χ (comp r χ) u
    rwa [hc u hu, hc' u hu, mul_one] at this
  have ha2 : (comp r χ).conductor ∣ ordProj[r] N := by
    refine (cond_dvd_iff _ (Nat.ordProj_dvd N r)).2 fun u hu => ?_
    have : u ∈ (proj r N).ker := by rw [hke]; exact hu
    rw [comp_hom, MonoidHom.mem_ker.1 this, map_one]
  have hb2 : (χ * (comp r χ)⁻¹).conductor ∣ ordCompl[r] N := by
    refine (cond_dvd_iff _ (Nat.ordCompl_dvd N r)).2 fun u hu => ?_
    have : u ∈ (proj r N).range := by rw [hra]; exact hu
    obtain ⟨v, rfl⟩ := this
    have := rest_hom χ (comp r χ) (proj r N v)
    rw [comp_hom, hid] at this
    exact mul_eq_right.1 this
  have hcop : (comp r χ).conductor.Coprime (χ * (comp r χ)⁻¹).conductor :=
    ((coprime_ordProj_ordCompl r N).coprime_dvd_left ha2).coprime_dvd_right hb2
  have h1 := hcop.mul_dvd_of_dvd_of_dvd ha1 hb1
  have h2 : χ.conductor ∣ (comp r χ).conductor * (χ * (comp r χ)⁻¹).conductor := by
    have hN := h1.trans χ.conductor_dvd_level
    refine (cond_dvd_iff _ hN).2 fun u hu => ?_
    have e1 := (cond_dvd_iff _ hN).1 (dvd_mul_right _ _) u hu
    have e2 := (cond_dvd_iff _ hN).1 (dvd_mul_left _ _) u hu
    rw [← rest_hom χ (comp r χ) u, e1, e2, mul_one]
  have he := h2.antisymm h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr).1 ha2
  have hb3 : ¬ r ∣ (χ * (comp r χ)⁻¹).conductor := fun h =>
    Nat.not_dvd_ordCompl hr (NeZero.ne N) (h.trans hb2)
  have hb0 := (χ * (comp r χ)⁻¹).conductor_ne_zero
  have hf : χ.conductor.factorization r = k := by
    rw [he, hk, Nat.factorization_mul (pow_ne_zero _ hr.ne_zero) hb0]
    simp [hr.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hb3]
  rw [hf]
  refine ⟨hk, ?_⟩
  rw [hk] at he
  exact (Nat.div_eq_of_eq_mul_right (pow_pos hr.pos k) he).symm

theorem UpperTheory.V.HV.compCond :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (r : ℕ), r.Prime →
      (comp r χ).conductor = ordProj[r] χ.conductor ∧ (comp r χ = 1 ↔ ¬ r ∣ χ.conductor) ∧
      (χ * (comp r χ)⁻¹).conductor = ordCompl[r] χ.conductor ∧ 2 ^ c2 χ = (psi2 χ).conductor ∧ 2 ^ c2 χ ∣ N ∧
      ∀ (M : ℕ), M ∣ N → (χ.conductor ∣ M ↔ ∀ p ∈ N.primeFactors, (comp p χ).conductor ∣ M) := by
  intro O _ _ N _ χ r hr
  have h2 : 2 ^ c2 χ = (psi2 χ).conductor := by
    unfold c2 psi2
    rw [(split_cond χ Nat.prime_two).1, Nat.prime_two.factorization_pow]
    simp
  refine ⟨(split_cond χ hr).1, ?_, (split_cond χ hr).2, h2, h2 ▸ (psi2 χ).conductor_dvd_level, fun M _ => ⟨fun h p hp => ?_, fun h => ?_⟩⟩
  · rw [DirichletCharacter.eq_one_iff_conductor_eq_one, (split_cond χ hr).1,
      hr.dvd_iff_one_le_factorization χ.conductor_ne_zero, Nat.pow_eq_one]
    have := hr.one_lt
    omega
  · rw [(split_cond χ (Nat.prime_of_mem_primeFactors hp)).1]
    exact (Nat.ordProj_dvd _ _).trans h
  · rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · have hpN : p ∈ N.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hp, ((dvd_pow_self p hk0.ne').trans hk).trans χ.conductor_dvd_level, NeZero.ne N⟩
      have := h p hpN
      rw [(split_cond χ hp).1] at this
      exact (pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization χ.conductor_ne_zero).1 hk)).trans this
