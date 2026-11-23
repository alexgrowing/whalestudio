import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Mathlib.NumberTheory.Multiplicity

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem kill {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommGroup M] (f : Γ →* M)
    (hf : IsClosed (f.ker : Set Γ)) {g : Γ} {n : ℕ} (hg : g ^ n ∈ (commutator Γ).topologicalClosure) : f g ^ n = 1 := by
  rw [← map_pow]
  have hle : (commutator Γ).topologicalClosure ≤ f.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker f) hf
  exact hle hg

private theorem padic_pow_l {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2) (x : ℤ_[l]) (hx : x ^ l = 1) : x = 1 := by
  have hp := PadicInt.prime_p (p := l)
  have hodd : Odd l := hl.out.odd_of_ne_two h2
  have hc : PadicInt.toZMod x = 1 := by
    have h1 : PadicInt.toZMod x ^ l = 1 := by rw [← map_pow, hx, map_one]
    rw [ZMod.pow_card] at h1
    exact h1
  have hdvd : (l : ℤ_[l]) ∣ x - 1 := by
    have hs := PadicInt.toZMod_spec x
    rw [hc, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton, ZMod.cast_eq_val, ZMod.val_one,
      Nat.cast_one] at hs
    exact hs
  have hnd : ¬ (l : ℤ_[l]) ∣ x := by
    intro h
    have h1 : (l : ℤ_[l]) ∣ x ^ l := dvd_pow h hl.out.ne_zero
    rw [hx] at h1
    exact hp.not_dvd_one h1
  have key := emultiplicity_pow_prime_sub_pow_prime hp hodd hdvd hnd
  rw [hx, one_pow, sub_self, emultiplicity_zero] at key
  by_contra hne
  have hfin : FiniteMultiplicity (l : ℤ_[l]) (x - 1) :=
    FiniteMultiplicity.of_not_isUnit hp.not_unit (sub_ne_zero.2 hne)
  rw [hfin.emultiplicity_eq_multiplicity] at key
  exact ENat.coe_ne_top (multiplicity (l : ℤ_[l]) (x - 1) + 1) (by push_cast; exact key.symm)

private theorem padic_pow {l : ℕ} [Fact l.Prime] (h2 : l ≠ 2) (a : ℕ) (x : ℤ_[l]) (hx : x ^ l ^ a = 1) : x = 1 := by
  induction a generalizing x with
  | zero => simpa using hx
  | succ a ih =>
    apply ih
    apply padic_pow_l h2
    rw [← pow_mul, ← pow_succ]
    exact hx

theorem UpperTheory.V.Ws.Lk.kapMu :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → ∀ (g : G T.L Ω) (a : ℕ), g ^ l ^ a ∈ (commutator (G T.L Ω)).topologicalClosure → P.κ g = 1 ∧ P.tL g = 1 := by
  intro Ω _ _ _ l _ c D T P hD g a hg
  have h2 : l ≠ 2 := Raw.Good.l_odd hD
  have hl := (Fact.out : l.Prime)
  have hcLe : Continuous (resLe (K_le T)) := by
    letI : Algebra T.K T.L := (IntermediateField.inclusion (K_le T)).toAlgebra
    haveI : IsScalarTower T.K T.L Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    exact Af.continuous_restrictScalarsHom T.K T.L Ω
  have ht : P.tL g = 1 := by
    have hk : IsClosed ((P.t.comp (resLe (K_le T))).ker : Set (G T.L Ω)) :=
      isClosed_singleton.preimage (P.t_cont.comp hcLe)
    have hp := kill (P.t.comp (resLe (K_le T))) hk hg
    change (P.t.comp (resLe (K_le T))) g = 1
    have hz : (l ^ a) • Multiplicative.toAdd ((P.t.comp (resLe (K_le T))) g) = 0 := by
      rw [← toAdd_pow, hp, toAdd_one]
    have hz' := (smul_eq_zero.1 hz).resolve_left (pow_ne_zero _ hl.ne_zero)
    rw [← ofAdd_toAdd ((P.t.comp (resLe (K_le T))) g), hz', ofAdd_zero]
  refine ⟨?_, ht⟩
  have hβ : P.βL g = 1 := P.β_t ht
  have hγ : P.γ (resQ T.L g) = 1 := by
    have hcQ : Continuous (resQ T.L) := Af.continuous_restrictScalarsHom ℚ T.L Ω
    have hk : IsClosed (((cycZ ℚ Ω l).comp (resQ T.L)).ker : Set (G T.L Ω)) :=
      isClosed_singleton.preimage ((continuous_cycZ ℚ Ω l).comp hcQ)
    have hp := kill ((cycZ ℚ Ω l).comp (resQ T.L)) hk hg
    have hu : ((((cycZ ℚ Ω l).comp (resQ T.L)) g : ℤ_[l]ˣ) : ℤ_[l]) = 1 :=
      padic_pow h2 a _ (by rw [← Units.val_pow_eq_pow_val, hp, Units.val_one])
    exact P.γ_ker (Units.ext hu)
  have hκ : P.κ₀ (resLe (K_le T) g) = 1 := by
    have hk : IsClosed ((P.κ₀.comp (resLe (K_le T))).ker : Set (G T.L Ω)) :=
      (Subgroup.isClosed_of_isOpen _ P.κ₀_open).preimage hcLe
    have hp := kill (P.κ₀.comp (resLe (K_le T))) hk hg
    obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
    have hq : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
      rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
    have hcop : Nat.Coprime (l ^ a) m := Nat.Coprime.pow_left a hm
    have := pow_gcd_eq_one.2 ⟨hp, hq⟩
    rwa [hcop, pow_one] at this
  have hγ' : P.γ (AlgEquiv.restrictScalars ℚ g) = 1 := hγ
  simp only [Pre.κ, MonoidHom.mul_apply, MonoidHom.comp_apply, hβ, hγ, hκ]
  simp [hγ', hβ]
