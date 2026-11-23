import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.CharacterColumnKernels.StatementRho
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2BoundedTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPowMovesPadicRootOfUnity

open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.UnramifiedH2Bound

open GlobalTheory.ShapeNeg GlobalTheory.CyclotomicH2Bound

theorem pow_mul_eq_zero_of_mul {p : ℕ} (hp : p.Prime) {n m : ℕ} {b : ℤ} (hb : ¬ ((p : ℤ) ^ m ∣ b))
    {x : ZMod (p ^ n)} (hx : (b : ZMod (p ^ n)) * x = 0) : ((p ^ m : ℕ) : ZMod (p ^ n)) * x = 0 := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩

  have hbx : b • x = 0 := by rwa [zsmul_eq_mul]
  have h1 : (addOrderOf x : ℤ) ∣ b := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hbx
  have h2 : addOrderOf x ∣ p ^ n := by
    have := addOrderOf_dvd_card (x := x)
    rwa [ZMod.card] at this
  obtain ⟨j, -, hjx⟩ := (Nat.dvd_prime_pow hp).mp h2
  have hjm : j < m := by
    by_contra hcon
    push Not at hcon
    apply hb
    rw [hjx] at h1
    exact (pow_dvd_pow (p : ℤ) hcon).trans (by exact_mod_cast h1)
  have h3 : addOrderOf x ∣ p ^ m := by
    rw [hjx]; exact pow_dvd_pow _ hjm.le
  have h4 : (p ^ m : ℕ) • x = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp h3
  rwa [nsmul_eq_mul] at h4

theorem h2_bounded_of_trivial_action : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} → (p : O) ≠ 0 →
    ∀ {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) →
    ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M), (∀ g m, ρ g m = m) →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  intro hTD p _ K hK O _ _ _ _ ϖ hϖ hpϖ hp0 M _ _ eM ρ hρ hcont
  have hp : p.Prime := Fact.out

  obtain ⟨σ, N, ζ', hζ'1, hσζ'⟩ :=
    GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity (p := p) (K := K) hK 1 Nat.one_pos
  rw [pow_one] at hσζ'

  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {(p : O) ^ N}) (by rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero N hp0) hϖ
  have hfinQ : Finite (O ⧸ Ideal.span {(p : O) ^ N}) := by
    rw [hk]; exact finite_quot hϖ k
  refine ⟨(p ^ N) ^ ((p ^ N) ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N})), ?_⟩
  intro n hn h
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
  have htriv : ∀ (g : Formalism.GaloisCohomology.GK p K) (m : Lev M (ϖ ^ n)), levRepZ p n h ρ g m = m := by
    intro g m
    rw [levRepZ_apply]
    exact Lev.ext (by rw [levRep_val, hρ])

  obtain ⟨x₀, hx₀⟩ := lev_cyclic eM hϖ n
  have hx₀k : (ϖ ^ n) • x₀ = 0 := Lev.ext (by rw [Lev.val_smul, Lev.smul_val, Lev.val_zero])
  have hfinL : Finite (Lev M (ϖ ^ n)) := by
    have := finite_quot hϖ n
    refine Finite.of_surjective (fun q : O ⧸ Ideal.span {ϖ ^ n} => q.out • x₀) ?_
    intro y
    obtain ⟨t, rfl⟩ := hx₀ y
    exact ⟨Ideal.Quotient.mk _ t, out_smul n hx₀k t⟩
  obtain ⟨⟨e⟩, -, -, -, hcup⟩ :=
    hTD p K hK n (Lev M (ϖ ^ n)) (levRepZ p n h ρ) hn (hcont n h)

  have hkill : ∀ (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (m : Lev M (ϖ ^ n)), ((p ^ N : ℕ) : ZMod (p ^ n)) * φ.1 m = 0 := by
    intro φ m
    by_cases hnN : n ≤ N
    · rw [(ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow p hnN), zero_mul]
    push Not at hnN
    obtain ⟨ζ, hζ⟩ := exists_prim p n
    have hσζn : (σ ζ) ^ (p ^ n) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hσζn
    have hcyc := cycK_eq_of_prim n σ hζ a ha.symm
    have hfixm : ((Formalism.GaloisCohomology.cycK p K n σ : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) *
        φ.1 (levRepZ p n h ρ σ⁻¹ m) = φ.1 m := by
      rw [← twDual_apply]
      exact DFunLike.congr_fun ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).mp φ.2 σ) m
    rw [htriv, hcyc] at hfixm
    have hnd : ¬ ((p : ℤ) ^ N ∣ (a : ℤ) - 1) := by
      rintro ⟨d, hd⟩
      apply hσζ'
      have hζ'n : ζ' ^ (p ^ n) = 1 := by
        obtain ⟨c, hc⟩ := pow_dvd_pow p hnN.le
        rw [hc, pow_mul, hζ'1, one_pow]
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hζ'n
      have hσ' : σ ζ' = ζ' ^ a := by
        rw [← hj, map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]
      have hne : ζ' ≠ 0 := by
        rintro rfl
        rw [zero_pow (pow_ne_zero N hp.ne_zero)] at hζ'1
        exact zero_ne_one hζ'1
      have ha' : (a : ℤ) = 1 + ((p ^ N : ℕ) : ℤ) * d := by push_cast; linarith
      rw [hσ', ← zpow_natCast, ha', zpow_add₀ hne, zpow_one, zpow_mul, zpow_natCast, hζ'1,
        one_zpow, mul_one]
    have hb : (((a : ℤ) - 1 : ℤ) : ZMod (p ^ n)) * φ.1 m = 0 := by
      push_cast
      rw [sub_mul, one_mul, hfixm, sub_self]
    exact pow_mul_eq_zero_of_mul hp hnd hb

  have hTcard : Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ≤ p ^ N := by
    have key : ∀ z : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0},
        z.1.val = p ^ (n - N) * (z.1.val / p ^ (n - N)) ∧ z.1.val / p ^ (n - N) < p ^ N := by
      intro z
      have hlt : z.1.val < p ^ (n - N) * p ^ N := by
        calc z.1.val < p ^ n := ZMod.val_lt _
          _ ≤ p ^ (n - N + N) := Nat.pow_le_pow_right hp.pos (by omega)
          _ = _ := pow_add _ _ _
      have hdvd : p ^ (n - N) ∣ z.1.val := by
        by_cases hnN : n ≤ N
        · rw [Nat.sub_eq_zero_of_le hnN, pow_zero]; exact one_dvd _
        · push Not at hnN
          have h1 : ((p ^ N * z.1.val : ℕ) : ZMod (p ^ n)) = 0 := by
            rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact z.2
          rw [ZMod.natCast_eq_zero_iff] at h1
          have h2 : p ^ n = p ^ N * p ^ (n - N) := by rw [← pow_add]; congr 1; omega
          have h1' : p ^ N * p ^ (n - N) ∣ p ^ N * z.1.val := by rw [← h2]; exact h1
          exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos N) h1'
      exact ⟨(Nat.mul_div_cancel' hdvd).symm, Nat.div_lt_of_lt_mul hlt⟩
    have hinj : Function.Injective
        (fun z : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} => ((z.1.val / p ^ (n - N) : ℕ) : ZMod (p ^ N))) := by
      intro z w hzw
      have hz := key z
      have hw := key w
      have hv := congrArg ZMod.val hzw
      simp only [ZMod.val_cast_of_lt hz.2, ZMod.val_cast_of_lt hw.2] at hv
      apply Subtype.ext
      apply ZMod.val_injective
      rw [hz.1, hw.1, hv]
    have : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
    calc _ ≤ Nat.card (ZMod (p ^ N)) := Nat.card_le_card_of_injective _ hinj
      _ = p ^ N := Nat.card_zmod _

  have hval : ∀ (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (t : O),
      φ.1 (t • x₀) = φ.1 ((Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out • x₀) := by
    intro φ t
    have hmem : (Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out - t ∈
        Ideal.span {(p : O) ^ N} :=
      Ideal.Quotient.eq.mp (by rw [Ideal.Quotient.mk_out])
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
    have hout : (Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out = t + ((p ^ N : ℕ) : O) * s := by
      rw [Nat.cast_pow]; linear_combination -hs
    rw [hout, add_smul, mul_smul, Nat.cast_smul_eq_nsmul, td_add, td_nsmul, nsmul_eq_mul,
      hkill φ, add_zero]
  have hΦ : Function.Injective (fun (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (q : O ⧸ Ideal.span {(p : O) ^ N}) =>
      (⟨φ.1 (q.out • x₀), hkill φ _⟩ : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0})) := by
    intro φ ψ hφψ
    apply Subtype.ext
    apply TDual.ext
    intro m
    obtain ⟨t, rfl⟩ := hx₀ m
    rw [hval φ t, hval ψ t]
    exact congrArg Subtype.val (congrFun hφψ (Ideal.Quotient.mk _ t))
  have hfinH0 : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Finite.of_injective _ hΦ
  have hH0card : Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) ≤ (p ^ N) ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N}) := by
    calc _ ≤ Nat.card (O ⧸ Ideal.span {(p : O) ^ N} → {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0}) :=
          Nat.card_le_card_of_injective _ hΦ
      _ = Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N}) := Nat.card_fun
      _ ≤ _ := Nat.pow_le_pow_left hTcard _

  have hsmul0 : ∀ φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))), ((p ^ N : ℕ) : ZMod (p ^ n)) • φ = 0 := by
    intro φ
    apply Subtype.ext
    apply TDual.ext
    intro m
    rw [Submodule.coe_smul, TDual.smul_apply, hkill φ m]
    rfl
  have hΨ : Function.Injective (fun (x : H2 ((levRepZ p n h ρ).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))))
      (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) =>
      (⟨e (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) x φ), by
        have h0 := congrArg e (congrArg
          (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) x) (hsmul0 φ))
        rw [LinearMap.map_smul, LinearEquiv.map_smul, LinearMap.map_zero, LinearEquiv.map_zero,
          smul_eq_mul] at h0
        exact h0⟩ : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0})) := by
    intro x y hxy
    apply hcup.1
    apply LinearMap.ext
    intro φ
    apply e.injective
    exact congrArg Subtype.val (congrFun hxy φ)
  calc Nat.card (H2 (levRepZ p n h ρ))
      = Nat.card (H2 ((levRepZ p n h ρ).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := rfl
    _ ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))) → {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0}) := Nat.card_le_card_of_injective _ hΨ
    _ = Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ^ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Nat.card_fun
    _ ≤ (p ^ N) ^ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Nat.pow_le_pow_left hTcard _
    _ ≤ _ := Nat.pow_le_pow_right (pow_pos hp.pos N) hH0card

end GlobalTheory.UnramifiedH2Bound
