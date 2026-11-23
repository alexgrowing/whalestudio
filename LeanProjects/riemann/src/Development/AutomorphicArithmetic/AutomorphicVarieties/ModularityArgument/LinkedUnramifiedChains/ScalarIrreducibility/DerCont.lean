import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.NormLeOneOfInt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSpanModSq

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

section Abs

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R]

private theorem sup_pow_le (t : R) (B : Ideal R) (k : ℕ) :
    (Ideal.span {t} ⊔ B) ^ k ≤ Ideal.span {t ^ k} ⊔ B := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton, ← pow_succ]
    have h1 : Ideal.span {t ^ k} * B ≤ B := Ideal.mul_le_right
    have h2 : B * (Ideal.span {t} ⊔ B) ≤ B := Ideal.mul_le_left
    exact sup_le (sup_le le_sup_left (le_trans h1 le_sup_right)) (le_trans h2 le_sup_right)

private theorem exists_pow_le [IsLocalRing O] [Finite (ResidueField O)] [IsLocalRing R] (I : Ideal R)
    (hI : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ I) (s : Finset R)
    (hs : ∀ a : R, ∃ b ∈ Submodule.span O (s : Set R), a - b ∈ I) :
    ∃ j, maximalIdeal R ^ j ≤ I := by
  classical
  have hfin : Finite (R ⧸ I) := by
    let σ : ResidueField O → O := Function.surjInv (residue_surjective (R := O))
    have hσ : ∀ x, residue O (σ x) = x := Function.surjInv_eq _
    let φ : (s → ResidueField O) → R ⧸ I :=
      fun x => Ideal.Quotient.mk I (∑ e : s, algebraMap O R (σ (x e)) * (e : R))
    refine Finite.of_surjective φ fun z => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨b, hb, hab⟩ := hs a
    obtain ⟨f, rfl⟩ := Submodule.mem_span_finset'.1 hb
    refine ⟨fun e => residue O (f e), ?_⟩
    have h1 : (∑ e : s, algebraMap O R (σ (residue O (f e))) * (e : R)) - ∑ e : s, f e • (e : R) ∈ I := by
      rw [← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun e _ => ?_
      rw [Algebra.smul_def, ← sub_mul, ← map_sub]
      refine Ideal.mul_mem_right _ _ (hI _ ?_)
      rw [← residue_eq_zero_iff, map_sub, hσ, sub_self]
    have h2 := I.sub_mem h1 hab
    rw [sub_sub_sub_cancel_right] at h2
    exact Ideal.Quotient.eq.2 h2
  haveI : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨j, hj⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
  refine ⟨j, ?_⟩
  have hm : (maximalIdeal R).map (Ideal.Quotient.mk I) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_jacobson_bot]
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hu : IsUnit (a * b + 1) := by
      by_contra h
      have h2 := Ideal.sub_mem _ ((mem_maximalIdeal _).2 h) (Ideal.mul_mem_right b _ ha)
      rw [add_sub_cancel_left] at h2
      exact (Ideal.ne_top_iff_one _).1 (maximalIdeal.isMaximal R).ne_top h2
    simpa using hu.map (Ideal.Quotient.mk I)
  have h3 := Ideal.pow_right_mono hm j
  rw [hj, ← Ideal.map_pow] at h3
  intro a ha
  exact Ideal.Quotient.eq_zero_iff_mem.1 (h3 (Ideal.mem_map_of_mem _ ha))

private theorem exists_span_mod_sq [IsNoetherianRing R] [CommRing K] [Algebra O K] (y : R →ₐ[O] K)
    (h : Module.Finite O y.range) :
    ∃ s : Finset R, ∀ a : R, ∃ b ∈ Submodule.span O (s : Set R), a - b ∈ RingHom.ker y ^ 2 :=
  _root_.UpperTheory.Reformulated.B.Ra7.exists_span_mod_sq y h

private theorem derCont_abs [IsLocalRing O] [Finite (ResidueField O)] [IsLocalRing R] [IsNoetherianRing R]
    [NormedField K] [Algebra O K] (y : R →ₐ[O] K) (hfin : Module.Finite O y.range) (hle : ∀ a, ‖y a‖ ≤ 1)
    (hlt : ∀ a ∈ maximalIdeal R, ‖y a‖ < 1) (p : O) (hp : maximalIdeal O = Ideal.span {p})
    (hpR : algebraMap O R p ∈ maximalIdeal R) (D : R →ₗ[O] K)
    (hD : ∀ f g, D (f * g) = y f * D g + y g * D f) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ a ∈ maximalIdeal R ^ k, ‖D a‖ ≤ ε ∧ ‖y a‖ ≤ ε := by
  classical
  have hDq : ∀ x ∈ RingHom.ker y ^ 2, D x = 0 := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun f hf g hg => ?_)
      (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    have hf' : y f = 0 := RingHom.mem_ker.1 hf
    have hg' : y g = 0 := RingHom.mem_ker.1 hg
    rw [hD, hf', hg']
    simp
  have hyq : ∀ x ∈ RingHom.ker y ^ 2, y x = 0 := fun x hx =>
    RingHom.mem_ker.1 (Ideal.pow_le_self two_ne_zero hx)
  obtain ⟨s, hs⟩ := exists_span_mod_sq y hfin
  have hO : ∀ o : O, ‖algebraMap O K o‖ ≤ 1 := fun o => by simpa using hle (algebraMap O R o)
  have hC : 0 ≤ ∑ e ∈ s, ‖D e‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbd : ∀ b, ‖D b‖ ≤ ∑ e ∈ s, ‖D e‖ := by
    intro b
    obtain ⟨b₀, hb₀, hc⟩ := hs b
    have e0 : D b = D b₀ := by
      have := hDq _ hc
      rwa [map_sub, sub_eq_zero] at this
    rw [e0]
    obtain ⟨f, rfl⟩ := Submodule.mem_span_finset'.1 hb₀
    rw [map_sum, ← Finset.sum_coe_sort s]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e _ => ?_)
    rw [map_smul, Algebra.smul_def, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hO _)
  obtain ⟨j, hj⟩ := exists_pow_le (Ideal.span {algebraMap O R p} ⊔ RingHom.ker y ^ 2)
    (fun a ha => by
      rw [hp] at ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)))
    s (fun a => by
      obtain ⟨b, hb, hab⟩ := hs a
      exact ⟨b, hb, Ideal.mem_sup_right hab⟩)
  have hρ : ‖y (algebraMap O R p)‖ < 1 := hlt _ hpR
  have hyp : y (algebraMap O R p) = algebraMap O K p := y.commutes p
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hε (by positivity : 0 < ∑ e ∈ s, ‖D e‖ + 1)) hρ
  rw [lt_div_iff₀ (by positivity)] at hn
  have hρ0 : 0 ≤ ‖y (algebraMap O R p)‖ ^ n := by positivity
  refine ⟨j * n, fun a ha => ?_⟩
  have ha' : a ∈ Ideal.span {algebraMap O R p ^ n} ⊔ RingHom.ker y ^ 2 :=
    sup_pow_le _ _ n (Ideal.pow_right_mono hj n (by rwa [← pow_mul]))
  obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 ha'
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have e1 : b * algebraMap O R p ^ n = p ^ n • b := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  constructor
  · rw [map_add, hDq c hc, add_zero, e1, map_smul, Algebra.smul_def, norm_mul, map_pow, norm_pow, ← hyp]
    have := mul_le_mul_of_nonneg_left (hbd b) hρ0
    nlinarith
  · rw [map_add, hyq c hc, add_zero, map_mul, norm_mul, map_pow, norm_pow]
    have := mul_le_mul (hle b) (le_refl (‖y (algebraMap O R p)‖ ^ n)) hρ0 zero_le_one
    nlinarith

end Abs

theorem UpperTheory.V.J.derCont :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (y : R →ₐ[c.O] Qbar l),
        ∀ D ∈ PtDer y (Qbar l), ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a ∈ maximalIdeal R ^ k, ‖D a‖ ≤ ε ∧ ‖y a‖ ≤ ε := by
  intro l _ c _ R _ _ _ y D hD ε hε
  obtain ⟨hfin, hle, hlt⟩ := coPt l c R y
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hpR : algebraMap c.O R p ∈ maximalIdeal R := fun h => hp.not_isUnit (isUnit_of_map_unit _ _ h)
  exact derCont_abs y hfin hle hlt p hp.maximalIdeal_eq hpR D (fun f g => hD f g) hε
