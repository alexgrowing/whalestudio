import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ProjFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem pow_eq_one_of {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (m : ℕ)
    (H : ∀ u : (ZMod N)ˣ, χ.toUnitHom u ^ m = 1) : χ ^ m = 1 := by
  refine MulChar.ext fun u => ?_
  have hu := congrArg Units.val (H u)
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one] at hu
  rw [MulChar.pow_apply_coe, hu, MulChar.one_apply_coe]

private theorem unitHom_pow_orderOf {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    χ.toUnitHom u ^ orderOf χ = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
    MulChar.one_apply_coe, Units.val_one]

theorem UpperTheory.V.HV.hostComp :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ →
      orderOf ψ ∣ 2 ^ (h.ex + 1) * h.o ∧ 0 < orderOf ψ ∧ ∀ r, r.Prime → r ≠ 2 →
        orderOf (comp r ψ) ∣ 2 * h.o ∧ (r ∣ h.q → orderOf (comp r ψ) ∣ h.o) ∧ (¬ r ∣ h.q → comp r ψ ^ 2 = 1) ∧ (¬ r ∣ h.N → comp r ψ = 1) := by
  intro h O _ _ ψ hψ
  have hI := hostIndex h
  have ho : 0 < h.o := hI.2.2.2.1
  have hmemK : ∀ x ∈ h.H, ψ.toUnitHom x = 1 := fun x hx => MonoidHom.mem_ker.mp (hψ hx)
  have hA : ψ ^ (2 ^ (h.ex + 1) * h.o) = 1 :=
    pow_eq_one_of ψ _ (fun u => by
      rw [← map_pow]
      exact hmemK _ (hI.2.2.2.2.2.2.2.2.2 u))
  refine ⟨orderOf_dvd_of_pow_eq_one hA,
    Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hA) (Nat.mul_pos (pow_pos two_pos _) ho), ?_⟩
  intro r hr hr2
  have facts := projFacts h.N r hr
  have hca := compAlg O h.N r hr
  have cu : ∀ u, (comp r ψ).toUnitHom u = ψ.toUnitHom (proj r h.N u) := hca.1 ψ
  have off : ∀ (M : ℕ) (hM : M ∣ h.N), ¬ r ∣ M → ∀ u, ZMod.unitsMap hM (proj r h.N u) = 1 :=
    facts.2.2.2.2.2.2.2.1
  have n2 : ¬ r ∣ 2 ^ (h.ex + 2) := fun hd =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
  have sq : ¬ r ∣ h.q → comp r ψ ^ 2 = 1 := by
    intro hq
    refine pow_eq_one_of _ 2 (fun u => ?_)
    rw [cu, ← map_pow]
    apply hmemK
    simp only [Host.H, Subgroup.mem_inf]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.two_pow_dvd h) n2 u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.q_dvd h) hq u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, map_pow]
      exact ⟨_, rfl⟩
    · rw [Subgroup.mem_comap, map_pow]
      exact ⟨_, rfl⟩
  have hcop := h.pair.2.2.2.2
  have dq : r ∣ h.q → comp r ψ ^ h.o = 1 := by
    intro hq
    have nq1 : ¬ r ∣ h.q1 := fun hd =>
      hr.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_of_dvd_left hd _) hcop) hq)
    have nd : ¬ r ∣ h.d := fun hd =>
      hr.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_of_dvd_right hd _) hcop) hq)
    refine pow_eq_one_of _ h.o (fun u => ?_)
    rw [cu, ← map_pow]
    apply hmemK
    simp only [Host.H, Subgroup.mem_inf]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.two_pow_dvd h) n2 u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, MonoidHom.mem_ker, map_pow, map_pow]
      exact unitHom_pow_orderOf _ _
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.host_q1_dvd_N h) nq1 u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.d_dvd h) nd u, one_pow]
      exact Subgroup.one_mem _
  refine ⟨?_, fun hq => orderOf_dvd_of_pow_eq_one (dq hq), sq, (hca.2.2.2.2.2.1 ψ).2.2.1⟩
  by_cases hq : r ∣ h.q
  · exact (orderOf_dvd_of_pow_eq_one (dq hq)).trans (dvd_mul_left _ _)
  · exact (orderOf_dvd_of_pow_eq_one (sq hq)).trans (dvd_mul_right _ _)
