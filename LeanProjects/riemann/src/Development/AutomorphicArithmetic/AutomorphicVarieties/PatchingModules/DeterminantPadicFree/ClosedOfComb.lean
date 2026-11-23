import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem char_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    (l : K) = 0 := by
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : p.Prime := CharP.char_is_prime K p
  have hpl : p = l := by
    by_contra hne
    have hunit : IsUnit (p : ℤ_[l]) := by
      by_contra hnu
      have hlt : ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
        rw [Int.cast_natCast]
        exact PadicInt.mem_nonunits.mp hnu
      rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast] at hlt
      exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp hlt).symm
    have h := hunit.map f
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h
  subst hpl
  exact CharP.cast_eq_zero K p

private theorem closed_of_comb {A G ι : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [TopologicalSpace G] [Fintype ι] (ρ : ι → G → A) (hρ : ∀ a, AdicCont (maximalIdeal A) (ρ a))
    (q : ι → FractionRing A) (ψ : G → A)
    (h : ∀ g, algebraMap A (FractionRing A) (ψ g) = ∑ a, q a * algebraMap A (FractionRing A) (ρ a g)) :
    IsClosed {g | ψ g = 1} := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) Finset.univ q
  choose c hc using fun a => hb a (Finset.mem_univ a)
  have key : ∀ g, ψ g = 1 ↔ ∑ a, c a * ρ a g - (b : A) = 0 := by
    intro g
    have h1 : algebraMap A (FractionRing A) ((b : A) * ψ g) =
        algebraMap A (FractionRing A) (∑ a, c a * ρ a g) := by
      rw [map_mul, h g, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hc a, Algebra.smul_def, mul_assoc]
    have h2 := IsFractionRing.injective A (FractionRing A) h1
    have hb0 : (b : A) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    rw [sub_eq_zero, ← h2]
    constructor
    · intro h
      rw [h, mul_one]
    · intro h
      exact mul_left_cancel₀ hb0 (h.trans (mul_one _).symm)
  have hset : {g | ψ g = 1} =
      ⋂ N : ℕ, {g | Ideal.Quotient.mk (maximalIdeal A ^ N) (∑ a, c a * ρ a g - (b : A)) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Ideal.Quotient.eq_zero_iff_mem, key]
    constructor
    · intro h N
      rw [h]
      exact Ideal.zero_mem _
    · intro h
      have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
      have hmem : ∑ a, c a * ρ a g - (b : A) ∈ ⨅ i, maximalIdeal A ^ i := Submodule.mem_iInf _ |>.mpr h
      rw [hbot] at hmem
      exact (Submodule.mem_bot A).mp hmem
  rw [hset]
  refine isClosed_iInter fun N => ?_
  have hF : IsLocallyConstant (fun g => fun a => Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g)) := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    have hy : (fun g => fun a => Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g)) ⁻¹' {y} =
        ⋂ a, {g | Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g) = y a} := by
      ext g
      simp [funext_iff]
    rw [hy]
    exact isOpen_iInter_of_finite fun a => (hρ a N).isOpen_fiber (y a)
  have hG := (hF.comp (fun w => ∑ a, Ideal.Quotient.mk (maximalIdeal A ^ N) (c a) * w a -
    Ideal.Quotient.mk (maximalIdeal A ^ N) (b : A))).isClopen_fiber 0
  convert hG.isClosed using 1
  ext g
  simp [map_sub, map_sum, map_mul]

theorem UpperTheory.V.Pa.Det.psiMu :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (x : Point r) (v : F.Vl) (i : Fin n) (g : F.Gv v), g ∈ F.mu v → x.ψ v i g = 1 := by
  intro l _ F O _ _ _ n r x v i g hg
  have hl : (l : x.K) = 0 := char_of_padic ((algebraMap O x.K).comp (algebraMap ℤ_[l] O))
  haveI : CharP x.K l := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hl
  haveI : CharP (PowerSeries x.K) l :=
    charP_of_injective_algebraMap (algebraMap x.K (PowerSeries x.K)).injective l
  obtain ⟨P, hP⟩ := x.flag v
  have hclosed : IsClosed {s : F.Gv v | ((x.ψ v i s : (PowerSeries x.K)ˣ) : PowerSeries x.K) = 1} := by
    refine closed_of_comb (ι := Fin n × Fin n) (fun ab s => (mat x.ρ) (F.φ v s) ab.1 ab.2) ?_
      (fun ab => (P : Matrix (Fin n) (Fin n) _) i ab.1 * ((P⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) ab.2 i)
      _ ?_
    · intro ab N
      exact (x.cont ab.1 ab.2 N).comp_continuous (F.φ_cont v)
    · intro s
      have hs := (hP s).2 i
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at hs
      rw [← hs]
      simp only [pushRep, mat, MonoidHom.comp_apply, Units.coeHom_apply, Units.val_mul, Matrix.mul_apply,
        Finset.sum_mul, Fintype.sum_prod_type, Matrix.GeneralLinearGroup.map_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
  have hker : (commutator (F.Gv v)).topologicalClosure ≤ (x.ψ v i).ker := by
    apply Subgroup.topologicalClosure_minimal
    · exact Abelianization.commutator_subset_ker (x.ψ v i)
    · convert hclosed using 1
      ext s
      rw [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq, Units.val_eq_one]
  obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.mp (Subgroup.mem_comap.mp hg)
  have hgk : g ^ l ^ k ∈ (commutator (F.Gv v)).topologicalClosure := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using hk
  have h1 : x.ψ v i g ^ l ^ k = 1 := by
    rw [← map_pow]
    exact hker hgk
  have h2 : ((x.ψ v i g : PowerSeries x.K) - 1) ^ l ^ k = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, sub_self]
  have h3 : (x.ψ v i g : PowerSeries x.K) - 1 = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.mp h2
  exact Units.ext (sub_eq_zero.mp h3)
