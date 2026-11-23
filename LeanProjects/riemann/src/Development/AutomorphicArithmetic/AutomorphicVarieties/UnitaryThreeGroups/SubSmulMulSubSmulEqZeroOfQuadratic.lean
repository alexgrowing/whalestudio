import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsQuadraticGaussSum

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.U3.EtaMu

private def Fx {Ω : Type} [Field Ω] (s : Ω →+* Ω) (a : ℤ) : Prop := ∀ δ : Ω, δ ^ 2 = (a : Ω) → s δ = δ

section
variable {Ω : Type} [Field Ω] {s : Ω →+* Ω}

private theorem fx_of {a : ℤ} {x : Ω} (hx : x ^ 2 = (a : Ω)) (hs : s x = x) : Fx s a := by
  intro δ hδ
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hδ.trans hx.symm) with h | h
  · rw [h, hs]
  · rw [h, map_neg, hs]

private theorem fx_mul [IsAlgClosed Ω] {a b : ℤ} (ha : Fx s a) (hb : Fx s b) : Fx s (a * b) := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (a : Ω) two_pos
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (b : Ω) two_pos
  refine fx_of (x := x * y) (by rw [mul_pow, hx, hy, Int.cast_mul]) ?_
  rw [map_mul, ha x hx, hb y hy]

private theorem fx_one : Fx s 1 := fx_of (x := 1) (by simp) (map_one s)

private theorem fx_pow [IsAlgClosed Ω] {a : ℤ} (ha : Fx s a) (k : ℕ) : Fx s (a ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact fx_one
  | succ k ih =>
    rw [pow_succ]
    exact fx_mul ih ha

private theorem fx_four : Fx s 4 := fx_of (x := 2) (by norm_num) (map_ofNat s 2)

variable {M : ℕ}

private theorem fix_dvd (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) {n : ℕ} (hn : n ∣ M) {ζ : Ω} (hζ : ζ ^ n = 1) :
    s ζ = ζ := by
  obtain ⟨k, rfl⟩ := hn
  exact h ζ (by rw [pow_mul, hζ, one_pow])

private theorem fx_neg_one (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) (h4 : 4 ∣ M) : Fx s (-1) := by
  intro δ hδ
  refine fix_dvd h h4 ?_
  have : δ ^ 4 = (δ ^ 2) ^ 2 := by ring
  rw [this, hδ]
  norm_num

private theorem fx_two [IsAlgClosed Ω] (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) (h8 : 8 ∣ M) : Fx s 2 := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Ω) (by norm_num : 0 < 2)
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_pow_nat_eq i (by norm_num : 0 < 2)
  have hη8 : η ^ 8 = 1 := by
    calc η ^ 8 = ((η ^ 2) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hη, hi]; norm_num
  have h14 : η ^ 14 = -i := by
    calc η ^ 14 = ((η ^ 2) ^ 2) ^ 3 * η ^ 2 := by ring
      _ = -i := by rw [hη, hi]; ring
  have hsη : s η = η := fix_dvd h h8 hη8
  refine fx_of (x := η + η ^ 7) ?_ ?_
  · calc (η + η ^ 7) ^ 2 = η ^ 2 + 2 * η ^ 8 + η ^ 14 := by ring
      _ = ((2 : ℤ) : Ω) := by rw [hη, hη8, h14]; push_cast; ring
  · rw [map_add, map_pow, hsη]

private theorem fx_odd [IsAlgClosed Ω] [CharZero Ω] (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) (n : ℕ) :
    n % 2 = 1 → n ∣ M → ∃ a : ℤ, a % 4 = 1 ∧ a.natAbs = n ∧ Fx s a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn2 hnM
    by_cases h1 : n = 1
    · subst h1
      exact ⟨1, rfl, rfl, fx_one⟩
    · set p := n.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime h1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      rw [← hp_def] at hk
      have hp2 : p ≠ 2 := by
        intro h2
        rw [h2] at hk
        omega
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, mul_zero] at hk
          omega
        · exact h0
      have hkn : k < n := by
        rw [hk]
        have := hp.two_le
        nlinarith
      have hodd : Odd (p * k) := by
        rw [← hk]
        exact Nat.odd_iff.mpr hn2
      have hk2 : k % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp hodd).2
      obtain ⟨a', ha'4, ha'abs, ha'⟩ := ih k hkn hk2 ((Dvd.intro_left p hk.symm).trans hnM)
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
      obtain ⟨⟨x, hx⟩, hall⟩ := CF.gauss Ω p ζ hp2 hζ
      have hpM : p ∣ M := (Dvd.intro k hk.symm).trans hnM
      have hsz : s ζ = ζ ^ 1 := by
        rw [pow_one]
        exact fix_dvd h hpM hζ.pow_eq_one
      have hsx : s x = x := by
        have := (hall x hx).2 s 1 hsz
        simpa [legendreSym.at_one] using this
      have hps : (CF.pStar p).natAbs = p := by
        simp [CF.pStar, Int.natAbs_mul, Int.natAbs_pow]
      have hp4 : CF.pStar p % 4 = 1 := by
        obtain ⟨a, ha⟩ := hp.odd_of_ne_two hp2
        clear_value p
        rcases Nat.even_or_odd a with ⟨c, hc⟩ | ⟨c, hc⟩
        · have e : p / 2 = 2 * c := by omega
          have hpz : (p : ℤ) = 4 * c + 1 := by omega
          rw [CF.pStar, e, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
        · have e : p / 2 = 2 * c + 1 := by omega
          have hpz : (p : ℤ) = 4 * c + 3 := by omega
          rw [CF.pStar, e, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
      refine ⟨CF.pStar p * a', ?_, ?_, fx_mul (fx_of hx hsx) ha'⟩
      · rw [Int.mul_emod, hp4, ha'4]
        rfl
      · rw [Int.natAbs_mul, hps, ha'abs, hk]

private theorem fx_disc [IsAlgClosed Ω] [CharZero Ω] {d : ℤ} (hd0 : d ≠ 0) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (h : ∀ ζ : Ω, ζ ^ d.natAbs = 1 → s ζ = ζ) : Fx s d := by
  have hM0 : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0
  obtain ⟨j, u, hu, hdu⟩ := Nat.exists_eq_two_pow_mul_odd hM0
  obtain ⟨a, ha4, haabs, ha⟩ := fx_odd h u (Nat.odd_iff.mp hu) (Dvd.intro_left _ hdu.symm)
  have hsign : d = 2 ^ j * a ∨ d = -1 * (2 ^ j * a) := by
    have e : d.natAbs = (2 ^ j * a).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_pow, haabs, hdu]
      rfl
    rcases Int.natAbs_eq_natAbs_iff.mp e with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by rw [h']; ring)
  rcases Nat.lt_or_ge j 2 with hj | hj
  · interval_cases j
    · rcases hsign with h' | h'
      · rw [h']
        simpa using ha
      · exfalso
        norm_num at h'
        omega
    · exfalso
      rcases hsign with h' | h' <;> norm_num at h' <;> omega
  · have h4 : 4 ∣ d.natAbs := by
      rw [hdu, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (pow_dvd_pow 2 hj).mul_right u
    have hneg : Fx s (-1) := fx_neg_one h h4
    have hpow : Fx s (2 ^ j) := by
      rcases Nat.lt_or_ge j 3 with hj3 | hj3
      · have hj2 : j = 2 := by omega
        rw [hj2, show (2 : ℤ) ^ 2 = 4 by norm_num]
        exact fx_four
      · have h8 : 8 ∣ d.natAbs := by
          rw [hdu, show (8 : ℕ) = 2 ^ 3 by norm_num]
          exact (pow_dvd_pow 2 hj3).mul_right u
        exact fx_pow (fx_two h h8) j
    rcases hsign with h' | h'
    · rw [h']
      exact fx_mul hpow ha
    · rw [h']
      exact fx_mul hneg (fx_mul hpow ha)

end

private theorem sub_smul_mul_sub_smul_eq_zero_of_quadratic {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) :
    (discr K % 4 = 0 ∨ discr K % 4 = 1) ∧ ∃ δ : K, δ ^ 2 = (discr K : K) ∧
      ∀ x : K, ∃ a b : ℚ, 2 * x * δ = (a : K) * δ + (b : K) := by
  classical
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hK }
  haveI : IsGalois ℚ K := inferInstance
  have hcard : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact (IsGalois.card_aut_eq_finrank ℚ K).trans hK
  obtain ⟨σ, hσ1⟩ : ∃ σ : K ≃ₐ[ℚ] K, σ ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : Fintype.card (K ≃ₐ[ℚ] K) ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun a b => by rw [hcon a, hcon b])
    omega
  have hall : ∀ τ : K ≃ₐ[ℚ] K, τ = 1 ∨ τ = σ := by
    intro τ
    by_contra hcon
    push_neg at hcon
    have h3 : ({1, σ, τ} : Finset (K ≃ₐ[ℚ] K)).card = 3 :=
      Finset.card_eq_three.mpr ⟨1, σ, τ, hσ1.symm, hcon.1.symm, hcon.2.symm, rfl⟩
    have h4 := Finset.card_le_univ ({1, σ, τ} : Finset (K ≃ₐ[ℚ] K))
    omega
  have hσσ : ∀ x : K, σ (σ x) = x := by
    have hsq : σ * σ = 1 := by
      rcases hall (σ * σ) with h | h
      · exact h
      · exfalso
        exact hσ1 (mul_left_cancel (h.trans (mul_one σ).symm))
    intro x
    rw [← AlgEquiv.mul_apply, hsq, AlgEquiv.one_apply]
  have hother : ∀ τ : K ≃ₐ[ℚ] K, ¬ (τ ≠ 1 ∧ τ ≠ σ) := by
    intro τ hτ
    rcases hall τ with h | h
    · exact hτ.1 h
    · exact hτ.2 h
  have htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + σ x := by
    intro x
    rw [trace_eq_sum_automorphisms, Fintype.sum_eq_add 1 σ (Ne.symm hσ1)]
    · rw [AlgEquiv.one_apply]
    · intro τ hτ
      exact absurd hτ (hother τ)
  have hnm : ∀ x : K, algebraMap ℚ K (Algebra.norm ℚ x) = x * σ x := by
    intro x
    rw [Algebra.norm_eq_prod_automorphisms, Fintype.prod_eq_mul 1 σ (Ne.symm hσ1)]
    · rw [AlgEquiv.one_apply]
    · intro τ hτ
      exact absurd hτ (hother τ)
  have hcardι : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_basis (integralBasis K), hK]
  let e := Fintype.equivFinOfCardEq hcardι
  obtain ⟨u, hu_def⟩ : ∃ u, u = integralBasis K (e.symm 0) := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v, v = integralBasis K (e.symm 1) := ⟨_, rfl⟩
  have hD : ((discr K : ℤ) : ℚ) = Algebra.trace ℚ K (u * u) * Algebra.trace ℚ K (v * v) -
      Algebra.trace ℚ K (u * v) * Algebra.trace ℚ K (v * u) := by
    rw [coe_discr, ← Algebra.discr_reindex ℚ (integralBasis K) e, Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Function.comp_apply, hu_def, hv_def]
  have hu : IsIntegral ℤ u := by
    rw [hu_def, integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  have hv : IsIntegral ℤ v := by
    rw [hv_def, integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  have hintZ : ∀ q : ℚ, IsIntegral ℤ q → ∃ r : ℤ, (r : ℚ) = q := by
    intro q hq
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
    exact ⟨r, by simpa using hr⟩
  have hP : IsIntegral ℤ (u * σ v) := hu.mul (map_isIntegral_int σ hv)
  obtain ⟨α, hα⟩ := hintZ _ (Algebra.isIntegral_trace (L := ℚ) hP)
  obtain ⟨β, hβ⟩ := hintZ _ (Algebra.isIntegral_norm ℚ hP)
  have hDK : ((discr K : ℤ) : K) = (u * u + σ (u * u)) * (v * v + σ (v * v)) -
      (u * v + σ (u * v)) * (v * u + σ (v * u)) := by
    have h := congrArg (algebraMap ℚ K) hD
    simp only [map_sub, map_mul, htr, map_intCast] at h
    rw [h]
    simp only [map_mul]
  obtain ⟨δ, hδ_def⟩ : ∃ δ : K, δ = u * σ v - σ u * v := ⟨_, rfl⟩
  have hδ2 : δ ^ 2 = ((discr K : ℤ) : K) := by
    rw [hDK, hδ_def]
    simp only [map_mul]
    ring
  have hα' : (α : K) = u * σ v + σ u * v := by
    have h := htr (u * σ v)
    rw [← hα, map_intCast, map_mul, hσσ] at h
    exact h
  have hβ' : (β : K) = u * σ v * (σ u * v) := by
    have h := hnm (u * σ v)
    rw [← hβ, map_intCast, map_mul, hσσ] at h
    exact h
  have hDK2 : ((discr K : ℤ) : K) = (α : K) ^ 2 - 4 * (β : K) := by
    rw [← hδ2, hα', hβ', hδ_def]
    ring
  have hDZ : discr K = α ^ 2 - 4 * β := by exact_mod_cast hDK2
  have hmod : discr K % 4 = 0 ∨ discr K % 4 = 1 := by
    rw [hDZ]
    rcases Int.even_or_odd α with ⟨k, hk⟩ | ⟨k, hk⟩
    · left
      have h' : α ^ 2 - 4 * β = 4 * (k * k - β) := by rw [hk]; ring
      rw [h']
      exact Int.mul_emod_right 4 _
    · right
      have h' : α ^ 2 - 4 * β = 4 * (k * k + k - β) + 1 := by rw [hk]; ring
      rw [h']
      generalize k * k + k - β = X
      omega
  have hσδ : σ δ = -δ := by
    rw [hδ_def, map_sub, map_mul, map_mul, hσσ, hσσ]
    ring
  refine ⟨hmod, δ, hδ2, fun x => ⟨Algebra.trace ℚ K x, Algebra.trace ℚ K (x * δ), ?_⟩⟩
  have h1 : ((Algebra.trace ℚ K x : ℚ) : K) = x + σ x :=
    (eq_ratCast (algebraMap ℚ K) _).symm.trans (htr x)
  have h2 : ((Algebra.trace ℚ K (x * δ) : ℚ) : K) = x * δ + σ x * -δ := by
    rw [← eq_ratCast (algebraMap ℚ K), htr, map_mul, hσδ]
  rw [h1, h2]
  ring

private theorem cls_eq_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {N : ℕ} [NeZero N] (s : G ℚ Ω)
    (h : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) : Chr.cls ℚ Ω N s = 1 := by
  have key : ∀ t ∈ rootsOfUnity N Ω,
      (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) (t : Ω) = (t : Ω) ^ (1 : ZMod N).val := by
    intro t ht
    have htN : (t : Ω) ^ N = 1 := by
      rw [mem_rootsOfUnity] at ht
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    change s (t : Ω) = _
    rw [h _ htN, ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge 1 N with hN | hN
    · rw [Nat.mod_eq_of_lt hN, pow_one]
    · have hN1 : N = 1 := by
        have := NeZero.ne N
        omega
      rw [hN1] at htN ⊢
      rw [Nat.mod_self, pow_zero]
      simpa using htN
  apply Units.ext
  rw [Units.val_one]
  exact (modularCyclotomicCharacter.unique Ω (Chr.card_roots ℚ Ω N) _ key).symm

end UpperTheory.V.U3.EtaMu

open UpperTheory.V.U3.EtaMu in
theorem UpperTheory.V.U3.eta_killsMu :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ), Af.KillsMu (discr K).natAbs D.η ∧ 1 ≤ (discr K).natAbs ∧ Af.KillsMu N (Chr.dirG ℚ Ω ψ) ∧ Af.KillsMu N (Chr.dirG ℚ Ω (comp l ψ)) := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hK := D.gd.quad
  obtain ⟨hd4, δ, hδ, hspan⟩ := sub_smul_mul_sub_smul_eq_zero_of_quadratic hK
  have hd0 : discr K ≠ 0 := discr_ne_zero K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    have hmem : s ∈ galOf ℚ K Ω := by
      rw [mem_galOf]
      have hfx : Fx (s : Ω →+* Ω) (discr K) := fx_disc hd0 hd4 (fun ζ hζ => by simpa using hs ζ hζ)
      have hδΩ : (algebraMap K Ω δ) ^ 2 = ((discr K : ℤ) : Ω) := by
        rw [← map_pow, hδ, map_intCast]
      have hsδ : s (algebraMap K Ω δ) = algebraMap K Ω δ := by simpa using hfx _ hδΩ
      have hδne : algebraMap K Ω δ ≠ 0 := by
        intro h0
        rw [h0] at hδΩ
        have h00 : ((discr K : ℤ) : Ω) = 0 := by rw [← hδΩ]; ring
        exact hd0 (by exact_mod_cast h00)
      intro x
      obtain ⟨a, b, hab⟩ := hspan x
      have e1 := congrArg (algebraMap K Ω) hab
      simp only [map_mul, map_add, map_ratCast, map_ofNat] at e1
      have e2 := congrArg s e1
      simp only [map_mul, map_add, map_ratCast, map_ofNat, hsδ] at e2
      have hz : (s (algebraMap K Ω x) - algebraMap K Ω x) * (2 * algebraMap K Ω δ) = 0 := by
        linear_combination e2 - e1
      rcases mul_eq_zero.mp hz with h | h
      · exact sub_eq_zero.mp h
      · exfalso
        exact hδne (by linear_combination (1 / 2 : Ω) * h)
    rw [← MonoidHom.mem_ker, D.η_ker]
    exact hmem
  · exact Int.natAbs_pos.mpr hd0
  · intro s hs
    simp only [Chr.dirG, MonoidHom.comp_apply, cls_eq_one s hs, map_one]
  · intro s hs
    simp only [Chr.dirG, MonoidHom.comp_apply, cls_eq_one s hs, map_one]
