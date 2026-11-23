import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import ReciprocityTheory.GaloisValuations.Global
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Inertia
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import GroundTheory.PAdicHodge.AxLemma
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubOnePowTotient

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue

noncomputable section

namespace GlobalTheory.IntTate

open Polynomial GlobalTheory.CycTrace

variable {l : ℕ} [hl : Fact l.Prime] {W : IntermediateField ℚ_[l] (PadicAlgCl l)}

def IntVal (W : IntermediateField ℚ_[l] (PadicAlgCl l)) : Prop :=
  ∀ a : W, a ≠ 0 → ∃ v : ℤ, ‖(a : PadicAlgCl l)‖ = ((l : ℝ)⁻¹) ^ v

theorem coeff_bound_unif (hW : IntVal W) (π : PadicAlgCl l) (e : ℕ) (hπ : ‖π‖ ^ e = (l : ℝ)⁻¹)
    (Q : W[X]) (hQ : Q.natDegree < e) (k : ℕ) :
    (l : ℝ)⁻¹ * ‖(Q.coeff k : PadicAlgCl l)‖ ≤ ‖aeval π Q‖ := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have he : e ≠ 0 := by omega
  have hr0 : 0 < ‖π‖ := by
    rcases (norm_nonneg π).eq_or_lt with h | h
    · rw [← h, zero_pow he] at hπ
      exact absurd hπ (inv_pos.2 hl0).ne
    · exact h
  have hr1 : ‖π‖ < 1 := by
    by_contra h
    have := one_le_pow₀ (not_lt.1 h) (n := e)
    rw [hπ] at this
    exact absurd (inv_lt_one_of_one_lt₀ hl1) (not_lt.2 this)
  by_cases hk : k < e
  swap
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  have hs : ∀ (a : W) (y : PadicAlgCl l), ‖a • y‖ = ‖(a : PadicAlgCl l)‖ * ‖y‖ := fun a y => norm_mul _ _
  rw [aeval_eq_sum_range' hQ]
  refine le_trans ?_ (norm_le_norm_sum (Finset.range e) (fun j => Q.coeff j • π ^ j) ?_
    (Finset.mem_range.2 hk))
  · simp only [hs, norm_pow]
    rw [mul_comm, ← hπ]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le hk.le) (norm_nonneg _)
  · intro i hi j hj h0 hij
    simp only [hs, norm_pow] at hij
    have hi0 : Q.coeff i ≠ 0 := fun h => h0 (by simp [h])
    have hj0 : Q.coeff j ≠ 0 := by
      intro h
      rw [h, ZeroMemClass.coe_zero, norm_zero, zero_mul] at hij
      exact (mul_pos (norm_pos_iff.2 (by simpa using hi0)) (pow_pos hr0 _)).ne' hij
    obtain ⟨u, hu⟩ := hW _ hi0
    obtain ⟨v, hv⟩ := hW _ hj0
    rw [hu, hv, ← hπ, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_add₀ hr0.ne', ← zpow_add₀ hr0.ne'] at hij
    have h3 := zpow_right_injective₀ hr0 hr1.ne hij
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    have h4 : (e : ℤ) ∣ (i : ℤ) - j := ⟨v - u, by linear_combination h3⟩
    have h5 := Int.eq_zero_of_abs_lt_dvd h4 (by rw [abs_lt]; constructor <;> omega)
    omega

theorem coeff_bound (hW : IntVal W) (N : ℕ) (z : PadicAlgCl l) (hz : IsPrimitiveRoot z (l ^ (N + 1)))
    (P : W[X]) (hP : P.natDegree < (l ^ (N + 1)).totient) (k : ℕ) :
    (l : ℝ)⁻¹ * ‖(P.coeff k : PadicAlgCl l)‖ ≤ ‖aeval z P‖ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hπ := norm_sub_one_pow_totient l N z hz
  rw [norm_l] at hπ
  have hQ := coeff_bound_unif hW (z - 1) _ hπ (taylor 1 P) (by rwa [natDegree_taylor])
  have e1 : aeval (z - 1) (taylor 1 P) = aeval z P := by
    rw [taylor_apply, aeval_comp]; simp
  rw [e1] at hQ
  have e2 : P = taylor (-1) (taylor 1 P) := by rw [taylor_taylor]; simp
  generalize taylor 1 P = Q at hQ e2
  have : ‖(P.coeff k : PadicAlgCl l)‖ ≤ l * ‖aeval z P‖ := by
    conv_lhs => rw [e2, taylor_coeff, eval_eq_sum_range]
    push_cast
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
    intro j _
    rw [hasseDeriv_coeff]
    push_cast
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
    have h1 := IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) ((j + k).choose k)
    have h2 := hQ (j + k)
    rw [inv_mul_le_iff₀ hl0] at h2
    calc _ ≤ 1 * ‖(Q.coeff (j + k) : PadicAlgCl l)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ _ := by rwa [one_mul]
  rwa [inv_mul_le_iff₀ hl0]

theorem aeval_cyclotomic {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ} (hn : 0 < n) {w : L}
    (hw : IsPrimitiveRoot w n) : aeval w (cyclotomic n K) = 0 := by
  rw [aeval_def, ← eval_map, map_cyclotomic]
  exact hw.isRoot_cyclotomic hn

theorem exists_poly_small {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ} (hn : 0 < n) {w : L}
    (hw : IsPrimitiveRoot w n) (t : ℕ) : ∃ R : K[X], R.natDegree < n.totient ∧ aeval w R = w ^ t := by
  refine ⟨X ^ t %ₘ cyclotomic n K, ?_, (aeval_modByMonic_eq_self_of_root (aeval_cyclotomic hn hw)).trans (by simp)⟩
  rw [← natDegree_cyclotomic n K]
  refine natDegree_modByMonic_lt _ (cyclotomic.monic _ _) ?_
  intro h
  have := natDegree_cyclotomic n K
  rw [h, natDegree_one] at this
  exact (Nat.totient_pos.2 hn).ne this

theorem exists_poly_pow (n m : ℕ) (z : PadicAlgCl l) (hz : IsPrimitiveRoot z (l ^ (n + m + 1))) (k : ℕ) :
    ∃ P : W[X], aeval z P = z ^ k ∧
      ∀ j, P.coeff j ≠ 0 → j < (l ^ (n + m + 1)).totient ∧ (l ^ m ∣ j ↔ l ^ m ∣ k) := by
  have hp := hl.out
  have hM : 0 < l ^ m := pow_pos hp.pos m
  have hw : IsPrimitiveRoot (z ^ (l ^ m)) (l ^ (n + 1)) :=
    hz.pow (pow_pos hp.pos _) (by ring)
  have htot : (l ^ (n + m + 1)).totient = (l ^ (n + 1)).totient * l ^ m := by
    rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp]; ring
  obtain ⟨R, hR1, hR2⟩ := exists_poly_small (K := W) (pow_pos hp.pos _) hw (k / l ^ m)
  refine ⟨expand W (l ^ m) R * X ^ (k % l ^ m), ?_, fun j hj => ?_⟩
  · rw [map_mul, expand_aeval, hR2, aeval_X_pow, ← pow_mul, ← pow_add, Nat.div_add_mod]
  · rw [coeff_mul_X_pow'] at hj
    split_ifs at hj with h
    swap
    · exact absurd rfl hj
    rw [coeff_expand hM] at hj
    split_ifs at hj with hd
    swap
    · exact absurd rfl hj
    obtain ⟨t, ht⟩ := hd
    rw [ht, Nat.mul_div_cancel_left _ hM] at hj
    have h1 : t + 1 ≤ (l ^ (n + 1)).totient := lt_of_le_of_lt (le_natDegree_of_ne_zero hj) hR1
    have h2 := Nat.mul_le_mul_right (l ^ m) h1
    have h3 := Nat.mod_lt k hM
    have h4 : j = l ^ m * t + k % l ^ m := by omega
    refine ⟨?_, ?_⟩
    · rw [htot, h4]; nlinarith
    · rw [h4, Nat.dvd_add_right (Dvd.intro _ rfl), Nat.dvd_mod_iff dvd_rfl]

def sp (W : IntermediateField ℚ_[l] (PadicAlgCl l)) (z : PadicAlgCl l) (A : ℕ → Prop) : Submodule W (PadicAlgCl l) :=
  Submodule.span W {w | ∃ k, A k ∧ w = z ^ k}

theorem sp_repr (n m : ℕ) (z : PadicAlgCl l) (hz : IsPrimitiveRoot z (l ^ (n + m + 1))) (A : Prop → Prop)
    (w : PadicAlgCl l) (hw : w ∈ sp W z fun k => A (l ^ m ∣ k)) :
    ∃ P : W[X], aeval z P = w ∧ ∀ j, P.coeff j ≠ 0 → j < (l ^ (n + m + 1)).totient ∧ A (l ^ m ∣ j) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, hk, rfl⟩ := hw
    obtain ⟨P, h1, h2⟩ := exists_poly_pow (W := W) n m z hz k
    exact ⟨P, h1, fun j hj => ⟨(h2 j hj).1, by rwa [propext (h2 j hj).2]⟩⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, rfl, h1⟩ := hx
    obtain ⟨Q, rfl, h2⟩ := hy
    refine ⟨P + Q, by simp, fun j hj => ?_⟩
    by_cases h : P.coeff j = 0
    · exact h2 j (by simpa [h] using hj)
    · exact h1 j h
  | smul c x _ hx =>
    obtain ⟨P, rfl, h1⟩ := hx
    exact ⟨c • P, by simp, fun j hj => h1 j (fun h => hj (by simp [h]))⟩

theorem bound (hW : IntVal W) (n m : ℕ) (z : PadicAlgCl l) (hz : IsPrimitiveRoot z (l ^ (n + m + 1)))
    (b w : PadicAlgCl l) (hb : b ∈ sp W z fun k => l ^ m ∣ k) (hw : w ∈ sp W z fun k => ¬ l ^ m ∣ k) :
    ‖b‖ ≤ l * ‖b + w‖ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  obtain ⟨P, rfl, h1⟩ := sp_repr n m z hz id b hb
  obtain ⟨Q, rfl, h2⟩ := sp_repr n m z hz Not w hw
  have hpos : 0 < (l ^ (n + m + 1)).totient := Nat.totient_pos.2 (pow_pos hl.out.pos _)
  have hdeg : (P + Q).natDegree < (l ^ (n + m + 1)).totient := by
    refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_) (Nat.sub_lt hpos one_pos)
    have a1 : P.coeff N = 0 := by by_contra h; have := (h1 N h).1; omega
    have a2 : Q.coeff N = 0 := by by_contra h; have := (h2 N h).1; omega
    simp [a1, a2]
  have hz1 : ‖z‖ = 1 := norm_root_eq_one (pow_pos hl.out.pos _).ne' hz.pow_eq_one
  rw [← map_add]
  conv_lhs => rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
  intro j _
  by_cases h : P.coeff j = 0
  · rw [h, zero_smul, norm_zero]; positivity
  have a2 : Q.coeff j = 0 := by by_contra h'; exact (h2 j h').2 (h1 j h).2
  have := coeff_bound hW (n + m) z hz _ hdeg j
  rw [coeff_add, a2, add_zero, inv_mul_le_iff₀ hl0] at this
  refine le_trans (le_of_eq ?_) this
  change ‖(P.coeff j : PadicAlgCl l) * z ^ j‖ = _
  rw [norm_mul, norm_pow, hz1, one_pow, mul_one]

theorem mem_sp_of_adjoin (z y : PadicAlgCl l) (hy : y ∈ IntermediateField.adjoin W {z}) :
    y ∈ sp W z fun _ => True := by
  have hz : IsAlgebraic W z := Algebra.IsAlgebraic.isAlgebraic z
  have hy' : y ∈ Algebra.adjoin W {z} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hz]
    exact hy
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
  obtain ⟨p, rfl⟩ := hy'
  change aeval z p ∈ _
  rw [aeval_eq_sum_range]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, trivial, rfl⟩)

theorem decomp (z : PadicAlgCl l) (A : ℕ → Prop) (y : PadicAlgCl l) (hy : y ∈ sp W z fun _ => True) :
    ∃ b ∈ sp W z A, ∃ w ∈ sp W z (fun k => ¬ A k), y = b + w := by
  have : (sp W z fun _ => True) ≤ sp W z A ⊔ sp W z (fun k => ¬ A k) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, -, rfl⟩
    by_cases h : A k
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨k, h, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨k, h, rfl⟩)
  obtain ⟨b, hb, w, hw, e⟩ := Submodule.mem_sup.1 (this hy)
  exact ⟨b, hb, w, hw, e.symm⟩

def chi (W : IntermediateField ℚ_[l] (PadicAlgCl l)) : (PadicAlgCl l ≃ₐ[W] PadicAlgCl l) →* ℤ_[l] :=
  (Units.coeHom ℤ_[l]).comp ((cyclotomicCharacter (PadicAlgCl l) l).comp
    (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[W] PadicAlgCl l) (PadicAlgCl l)))

theorem chi_spec (σ : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) (n : ℕ) (t : PadicAlgCl l) (ht : t ^ l ^ n = 1) :
    σ t = t ^ (PadicInt.toZModPow n (chi W σ)).val := by
  have : NeZero ((l : ℕ) : PadicAlgCl l) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ (PadicAlgCl l) σ) t ht

theorem norm_chi (σ : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) : ‖chi W σ‖ = 1 :=
  PadicInt.norm_units _

def emb (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* PadicAlgCl l :=
  (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom

theorem norm_emb (a : ℤ_[l]) : ‖emb l a‖ = ‖a‖ := PadicAlgCl.norm_extends l _

theorem emb_mem (a : ℤ_[l]) : emb l a ∈ W := W.algebraMap_mem _

theorem map_emb (σ : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) (a : ℤ_[l]) : σ (emb l a) = emb l a :=
  σ.commutes ⟨_, emb_mem a⟩

theorem norm_gal (σ : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) (x : PadicAlgCl l) : ‖σ x‖ = ‖x‖ :=
  ReciprocityTheory.Neutral.Cmp.norm_map (σ.restrictScalars ℚ_[l]) x

theorem norm_le_of_toZModPow (n : ℕ) (a : ℤ_[l]) (h : PadicInt.toZModPow n a = 0) : ‖a‖ ≤ ((l : ℝ)⁻¹) ^ n := by
  have h1 : a ∈ RingHom.ker (PadicInt.toZModPow (p := l) n) := h
  rw [PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow] at h1
  simpa using h1

theorem chi_mod_eq_one (σ : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) (n : ℕ) (z : PadicAlgCl l)
    (hz : IsPrimitiveRoot z (l ^ (n + 1))) (h : σ z = z) : PadicInt.toZModPow (n + 1) (chi W σ) = 1 := by
  have h1 : 1 < l ^ (n + 1) := Nat.one_lt_pow (by omega) hl.out.one_lt
  have : NeZero (l ^ (n + 1)) := ⟨by omega⟩
  have h2 := chi_spec σ _ z hz.pow_eq_one
  rw [h] at h2
  have h3 := hz.pow_inj h1 (ZMod.val_lt _) ((pow_one z).trans h2)
  rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow (n + 1) (chi W σ)), ← h3, Nat.cast_one]

theorem exists_gamma (hW : IntVal W) (n j : ℕ) (hj : 1 ≤ j) :
    ∃ γ : PadicAlgCl l ≃ₐ[W] PadicAlgCl l, (∀ t : PadicAlgCl l, t ^ l ^ (n + 1) = 1 → γ t = t) ∧ chi W γ ^ j ≠ 1 := by
  have hp := hl.out
  have : NeZero ((l : ℕ) : PadicAlgCl l) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  set a := 1 + l ^ (n + 1) with ha
  have ha1 : 1 < a := by have := pow_pos hp.pos (n + 1); omega
  set m := a ^ j with hm
  have hm1 : 1 < m := Nat.one_lt_pow (by omega) ha1
  have hlt : m < l ^ (n + m + 1) := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) (Nat.pow_le_pow_right hp.pos (by omega))
  have hpos : 0 < l ^ (n + m + 1) := pow_pos hp.pos _
  have : NeZero (l ^ (n + m + 1)) := ⟨hpos.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ (n + m + 1))
  have hint : IsIntegral W z := Algebra.IsIntegral.isIntegral z
  have hdeg : (l ^ (n + m + 1)).totient ≤ (minpoly W z).natDegree := by
    by_contra hlt
    have h := coeff_bound hW (n + m) z hz _ (not_le.1 hlt) (minpoly W z).natDegree
    rw [minpoly.aeval, norm_zero, coeff_natDegree, (minpoly.monic hint).leadingCoeff] at h
    have : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hp.pos)
    simp at h
    exact hp.ne_zero h
  have heq : cyclotomic (l ^ (n + m + 1)) W = minpoly W z :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic _ _)
      (minpoly.dvd W z (aeval_cyclotomic hpos hz)) (by rwa [natDegree_cyclotomic])
  have hcop : a.Coprime (l ^ (n + m + 1)) := by
    refine Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_).symm
    rw [ha, Nat.dvd_add_left (dvd_pow_self l (by omega))]
    exact hp.not_dvd_one
  obtain ⟨γ, hγ⟩ := minpoly.exists_algEquiv_of_root' hint.isAlgebraic
    (heq ▸ aeval_cyclotomic hpos (hz.pow_of_coprime a hcop))
  refine ⟨γ, fun t ht => ?_, fun h => ?_⟩
  · have ht' : t ^ l ^ (n + m + 1) = 1 := by
      rw [show n + m + 1 = n + 1 + m by ring, pow_add, pow_mul, ht, one_pow]
    obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one ht'
    rw [map_pow, hγ, ← pow_mul, mul_comm, pow_mul, ha, pow_add, ht, pow_one, mul_one]
  · have h1 : ∀ i : ℕ, (γ ^ i) z = z ^ a ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hγ, ← pow_mul, ← pow_succ']
    have h2 := chi_spec (γ ^ j) _ z hz.pow_eq_one
    have : Fact (1 < l ^ (n + m + 1)) := ⟨by omega⟩
    rw [map_pow, h, map_one, ZMod.val_one, h1] at h2
    have := hz.pow_inj hlt (by omega) h2
    omega

theorem gal_smul (g : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) (c : W) (x : PadicAlgCl l) : g (c • x) = c • g x := by
  change g ((c : PadicAlgCl l) * x) = (c : PadicAlgCl l) * g x
  rw [map_mul]
  exact congrArg (· * g x) (g.commutes c)

theorem sp_stable (n m : ℕ) (z : PadicAlgCl l) (hz : IsPrimitiveRoot z (l ^ (n + m + 1)))
    (g : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) (w : PadicAlgCl l) (hw : w ∈ sp W z fun k => ¬ l ^ m ∣ k) :
    g w ∈ sp W z fun k => ¬ l ^ m ∣ k := by
  have : NeZero (l ^ (n + m + 1)) := ⟨(pow_pos hl.out.pos _).ne'⟩
  obtain ⟨a, -, hac, ha⟩ := (hz.isPrimitiveRoot_iff (ξ := g z)).1 (hz.map_of_injective g.injective)
  have hac' : (l ^ m).Coprime a := (Nat.Coprime.coprime_dvd_right (pow_dvd_pow l (by omega)) hac).symm
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, hk, rfl⟩ := hw
    refine Submodule.subset_span ⟨a * k, fun h => hk (hac'.dvd_of_dvd_mul_left h), ?_⟩
    rw [map_pow, ← ha, pow_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [gal_smul]; exact Submodule.smul_mem _ c hx

theorem sp_fixed (N : ℕ) (z : PadicAlgCl l) (g : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) (hg : g (z ^ N) = z ^ N)
    (b : PadicAlgCl l) (hb : b ∈ sp W z fun k => N ∣ k) : g b = b := by
  induction hb using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, ⟨t, rfl⟩, rfl⟩ := hw
    rw [pow_mul, map_pow, hg]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [gal_smul, hx]

theorem sp_pow_le (N : ℕ) (z : PadicAlgCl l) : (sp W (z ^ N) fun _ => True) ≤ sp W z fun k => N ∣ k := by
  refine Submodule.span_mono ?_
  rintro _ ⟨k, -, rfl⟩
  exact ⟨N * k, Dvd.intro _ rfl, (pow_mul _ _ _).symm⟩

theorem estimate (hW : IntVal W) (n m : ℕ) (z : PadicAlgCl l) (hz : IsPrimitiveRoot z (l ^ (n + m + 1)))
    (g : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) (hg : g (z ^ l ^ m) = z ^ l ^ m) (c : ℤ_[l]) (y₀ y : PadicAlgCl l)
    (h₀ : y₀ ∈ sp W (z ^ l ^ m) fun _ => True) (hy : y ∈ sp W z fun _ => True) :
    ∃ b : PadicAlgCl l, ‖b - y₀‖ ≤ l * ‖y - y₀‖ ∧ ‖1 - c‖ * ‖b‖ ≤ l * ‖g y - emb l c * y‖ := by
  obtain ⟨b, hb, w, hw, rfl⟩ := decomp z (fun k => l ^ m ∣ k) y hy
  refine ⟨b, ?_, ?_⟩
  · have := bound hW n m z hz (b - y₀) w (sub_mem hb (sp_pow_le _ _ h₀)) hw
    rwa [sub_add_eq_add_sub] at this
  · have := bound hW n m z hz (emb l (1 - c) * b) (g w - emb l c * w)
      (Submodule.smul_mem _ (⟨_, emb_mem (1 - c)⟩ : W) hb)
      (sub_mem (sp_stable n m z hz g w hw) (Submodule.smul_mem _ (⟨_, emb_mem c⟩ : W) hw))
    rw [norm_mul, norm_emb] at this
    convert this using 3
    rw [map_add, sp_fixed _ z g hg b hb, map_sub, map_one]
    ring

theorem ax (z x : PadicAlgCl l) (r : ℝ)
    (h : ∀ σ : PadicAlgCl l ≃ₐ[W] PadicAlgCl l, σ z = z → ‖σ x - x‖ ≤ r) :
    ∃ y ∈ sp W z fun _ => True, ‖x - y‖ ≤ GroundTheory.PAdicHodge.axConstant l * r := by
  obtain ⟨y, hy, hxy⟩ := GroundTheory.PAdicHodge.ax_lemma (K := (IntermediateField.adjoin W {z}).restrictScalars ℚ_[l]) x (r := r)
    (fun τ => h { τ.toRingEquiv with
      commutes' := fun k => τ.commutes ⟨k, (IntermediateField.adjoin W {z}).algebraMap_mem k⟩ }
      (τ.commutes ⟨z, IntermediateField.mem_adjoin_simple_self W z⟩))
  exact ⟨y, mem_sp_of_adjoin z y hy, hxy⟩

def Small (j : ℕ) (H : Subgroup (PadicAlgCl l ≃ₐ[W] PadicAlgCl l)) : Prop :=
  ∃ C : ℝ, ∀ (x : PadicAlgCl l) (ε : ℝ), (∀ σ ∈ H, ‖σ x - emb l (chi W σ ^ j) * x‖ ≤ ε) → ‖x‖ ≤ C * ε

theorem norm_chi_pow (σ : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) (j : ℕ) : ‖emb l (chi W σ ^ j)‖ = 1 := by
  rw [norm_emb, norm_pow, norm_chi, one_pow]

theorem move_le (j n : ℕ) (z : PadicAlgCl l) (hz : IsPrimitiveRoot z (l ^ (n + 1))) (x : PadicAlgCl l) (ε : ℝ)
    (σ : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) (h : σ z = z) (H : ‖σ x - emb l (chi W σ ^ j) * x‖ ≤ ε) :
    ‖σ x - x‖ ≤ ε + ((l : ℝ)⁻¹) ^ (n + 1) * ‖x‖ := by
  have e : σ x - x = (σ x - emb l (chi W σ ^ j) * x) + emb l (chi W σ ^ j - 1) * x := by
    rw [map_sub, map_one]; ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add H ?_)
  rw [norm_mul, norm_emb]
  refine mul_le_mul_of_nonneg_right (norm_le_of_toZModPow _ _ ?_) (norm_nonneg _)
  rw [map_sub, map_pow, chi_mod_eq_one σ n z hz h, one_pow, map_one, sub_self]

theorem small_top (hW : IntVal W) (j : ℕ) (hj : 1 ≤ j) : Small (W := W) j ⊤ := by
  have hp := hl.out
  have : NeZero ((l : ℕ) : PadicAlgCl l) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hq0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hA : 1 ≤ GroundTheory.PAdicHodge.axConstant l := GroundTheory.PAdicHodge.one_le_axConstant
  set A := GroundTheory.PAdicHodge.axConstant l
  set D : ℝ := 3 * (l * A) with hD
  have hD0 : 0 < D := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (4 * D) by positivity) hq1
  obtain ⟨γ, hγ, hγ1⟩ := exists_gamma hW n j hj
  set δ := ‖1 - chi W γ ^ j‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.2 (sub_ne_zero.2 hγ1.symm)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (4 * D) by positivity) hq1
  have : NeZero (l ^ (n + m + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ (n + m + 1))
  have hw : IsPrimitiveRoot (z ^ (l ^ m)) (l ^ (n + 1)) := hz.pow (pow_pos hp.pos _) (by ring)
  refine ⟨2 * (D / δ + D), fun x ε H => ?_⟩
  have hε : 0 ≤ ε := (norm_nonneg _).trans (H 1 trivial)
  obtain ⟨y₀, hy₀, h₀⟩ := ax (W := W) (z ^ l ^ m) x _ fun σ h => move_le j n _ hw x ε σ h (H σ trivial)
  obtain ⟨y, hy, h₁⟩ := ax (W := W) z x _ fun σ h => move_le j (n + m) _ hz x ε σ h (H σ trivial)
  obtain ⟨b, hb1, hb2⟩ := estimate hW n m z hz γ (hγ _ hw.pow_eq_one) (chi W γ ^ j) y₀ y hy₀ hy
  have ha1 : ((l : ℝ)⁻¹) ^ (n + 1) ≤ 1 / (4 * D) := (pow_le_pow_of_le_one hq0.le hq1.le (by omega)).trans hn.le
  have ha2 : ((l : ℝ)⁻¹) ^ (n + m + 1) ≤ 1 / (4 * D) := (pow_le_pow_of_le_one hq0.le hq1.le (by omega)).trans hn.le
  have ha3 : ((l : ℝ)⁻¹) ^ (n + m + 1) ≤ δ / (4 * D) := (pow_le_pow_of_le_one hq0.le hq1.le (by omega)).trans hm.le
  have hX := norm_nonneg x
  set u := ε + 1 / (4 * D) * ‖x‖ with hu
  set v := ε + δ / (4 * D) * ‖x‖ with hv
  have hu0 : 0 ≤ u := by positivity
  have hv0 : ε ≤ v := le_add_of_nonneg_right (by positivity)
  have k0 : ‖x - y₀‖ ≤ A * u := h₀.trans (by rw [hu]; gcongr)
  have k1 : ‖x - y‖ ≤ A * u := h₁.trans (by rw [hu]; gcongr)
  have k2 : ‖x - y‖ ≤ A * v := h₁.trans (by rw [hv]; gcongr)
  have k3 : ‖y - y₀‖ ≤ 2 * (A * u) := by
    have e : y - y₀ = (x - y₀) - (x - y) := by ring
    rw [e]; refine (norm_sub_le _ _).trans ?_; linarith
  have k4 : ‖γ y - emb l (chi W γ ^ j) * y‖ ≤ 3 * (A * v) := by
    have e : γ y - emb l (chi W γ ^ j) * y =
        (γ x - emb l (chi W γ ^ j) * x) - γ (x - y) + emb l (chi W γ ^ j) * (x - y) := by
      rw [map_sub]; ring
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add_left (norm_sub_le _ _) _).trans ?_)
    rw [norm_gal, norm_mul, norm_chi_pow, one_mul]
    have := H γ trivial
    nlinarith
  have k5 : ‖x‖ ≤ ‖b‖ + D * u := by
    have e : x = b - (b - y₀) + (x - y₀) := by ring
    have h1 : ‖x‖ ≤ ‖b‖ + ‖b - y₀‖ + ‖x - y₀‖ := by
      conv_lhs => rw [e]
      exact (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    have h2 : ‖b - y₀‖ ≤ l * (2 * (A * u)) := hb1.trans (by gcongr)
    have h3 : A * u ≤ l * (A * u) := le_mul_of_one_le_left (by positivity) hl1.le
    rw [hD]; linarith
  have k6 : ‖b‖ ≤ D * v / δ := by
    rw [le_div_iff₀ hδ0, mul_comm]
    refine hb2.trans ((mul_le_mul_of_nonneg_left k4 (by positivity)).trans (le_of_eq ?_))
    rw [hD]; ring
  have e1 : D * u = D * ε + ‖x‖ / 4 := by rw [hu]; field_simp
  have e2 : D * v / δ = D / δ * ε + ‖x‖ / 4 := by rw [hv]; field_simp
  linarith

theorem small_inf (j : ℕ) (H : Subgroup (PadicAlgCl l ≃ₐ[W] PadicAlgCl l)) (hH : Small j H) (α : PadicAlgCl l) :
    Small j (H ⊓ MulAction.stabilizer _ α) := by
  classical
  obtain ⟨C, hC⟩ := hH
  have hint : IsIntegral W α := Algebra.IsIntegral.isIntegral α
  have hfin : (MulAction.orbit H α).Finite := by
    refine ((minpoly W α).rootSet_finite (PadicAlgCl l)).subset ?_
    rintro _ ⟨σ, rfl⟩
    rw [mem_rootSet_of_ne (minpoly.ne_zero hint)]
    change aeval ((σ : PadicAlgCl l ≃ₐ[W] PadicAlgCl l) α) _ = 0
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  haveI : Fintype (MulAction.orbit H α) := hfin.fintype
  have hτ : ∀ t : MulAction.orbit H α, ∃ τ : PadicAlgCl l ≃ₐ[W] PadicAlgCl l, τ ∈ H ∧ τ α = t := by
    rintro ⟨_, σ, rfl⟩
    exact ⟨σ, σ.2, rfl⟩
  choose τ hτH hτ using hτ
  set c : (PadicAlgCl l ≃ₐ[W] PadicAlgCl l) → PadicAlgCl l := fun σ => emb l (chi W σ ^ j) with hc
  have cm : ∀ σ σ', c (σ * σ') = c σ * c σ' := fun σ σ' => by simp only [hc, map_mul, mul_pow]
  have c1 : ∀ σ, ‖c σ‖ = 1 := fun σ => norm_chi_pow σ j
  have cf : ∀ σ σ' : PadicAlgCl l ≃ₐ[W] PadicAlgCl l, σ (c σ') = c σ' := fun σ σ' => map_emb σ _
  have key : ∀ P : (PadicAlgCl l)[X], ∃ D : ℝ, ∀ (x : PadicAlgCl l) (ε : ℝ),
      (∀ σ ∈ H ⊓ MulAction.stabilizer _ α, ‖σ x - c σ * x‖ ≤ ε) →
      ‖∑ t : MulAction.orbit H α, P.eval (t : PadicAlgCl l) * (c (τ t)⁻¹ * τ t x)‖ ≤ D * ε := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      obtain ⟨D, hD⟩ := hP
      obtain ⟨E, hE⟩ := hQ
      refine ⟨D + E, fun x ε h => ?_⟩
      simp only [eval_add, add_mul, Finset.sum_add_distrib]
      exact (norm_add_le _ _).trans (add_le_add (hD x ε h) (hE x ε h))
    | monomial k a =>
      refine ⟨‖a‖ * (C * (Fintype.card (MulAction.orbit H α) * ‖α‖ ^ k)), fun x ε h => ?_⟩
      simp only [eval_monomial, mul_assoc, ← Finset.mul_sum]
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left (hC _ _ fun σ hσ => ?_) (norm_nonneg _)
      change ‖_ - c σ * _‖ ≤ _
      rw [map_sum, Finset.mul_sum, ← Equiv.sum_comp (MulAction.toPerm (⟨σ, hσ⟩ : H))
        (fun t : MulAction.orbit H α => c σ * ((t : PadicAlgCl l) ^ k * (c (τ t)⁻¹ * τ t x))),
        ← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      rw [← nsmul_eq_mul, ← Finset.card_univ]
      refine Finset.sum_le_card_nsmul _ _ _ fun t _ => ?_
      set t' : MulAction.orbit H α := MulAction.toPerm (⟨σ, hσ⟩ : H) t with ht'
      have e1 : (t' : PadicAlgCl l) = σ t := rfl
      have hh : (τ t')⁻¹ * σ * τ t ∈ H ⊓ MulAction.stabilizer _ α := by
        refine ⟨H.mul_mem (H.mul_mem (H.inv_mem (hτH _)) hσ) (hτH _), ?_⟩
        change (τ t').symm (σ (τ t α)) = α
        rw [hτ, ← e1, ← hτ t', AlgEquiv.symm_apply_apply]
      have h2 := h _ hh
      have e2 : τ t' (((τ t')⁻¹ * σ * τ t) x) = σ (τ t x) := (τ t').apply_symm_apply _
      have e3 : c (τ t)⁻¹ * c ((τ t')⁻¹ * σ * τ t) = c σ * c (τ t')⁻¹ := by
        have : c (τ t)⁻¹ * c (τ t) = 1 := by rw [← cm, inv_mul_cancel]; simp [hc]
        rw [cm, cm]
        linear_combination (c σ * c (τ t')⁻¹) * this
      have e4 : σ ((t : PadicAlgCl l) ^ k * (c (τ t)⁻¹ * τ t x)) - c σ * ((t' : PadicAlgCl l) ^ k * (c (τ t')⁻¹ * τ t' x))
          = (t' : PadicAlgCl l) ^ k * (c (τ t)⁻¹ * τ t' (((τ t')⁻¹ * σ * τ t) x - c ((τ t')⁻¹ * σ * τ t) * x)) := by
        rw [map_sub, e2, map_mul, map_mul, map_mul, map_pow, cf, cf, ← e1]
        linear_combination ((t' : PadicAlgCl l) ^ k * τ t' x) * e3
      rw [e4, norm_mul, norm_mul, c1, one_mul, norm_gal, norm_pow, ← hτ t', norm_gal]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
  let t₀ : MulAction.orbit H α := ⟨α, MulAction.mem_orbit_self α⟩
  obtain ⟨D, hD⟩ := key (∏ t ∈ Finset.univ.erase t₀, (X - Polynomial.C (t : PadicAlgCl l)))
  have hne : (∏ t ∈ Finset.univ.erase t₀, (X - Polynomial.C (t : PadicAlgCl l))).eval (t₀ : PadicAlgCl l) ≠ 0 := by
    rw [eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    exact fun e => Finset.ne_of_mem_erase ht (Subtype.ext e.symm)
  refine ⟨D / ‖(∏ t ∈ Finset.univ.erase t₀, (X - Polynomial.C (t : PadicAlgCl l))).eval (t₀ : PadicAlgCl l)‖, fun x ε h => ?_⟩
  have := hD x ε h
  rw [Finset.sum_eq_single t₀, norm_mul, norm_mul, c1, one_mul, norm_gal] at this
  · rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.2 hne), mul_comm]
    exact this
  · intro t _ ht
    rw [eval_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨ht, Finset.mem_univ t⟩) (by simp), zero_mul]
  · simp

theorem small_finset (hW : IntVal W) (j : ℕ) (hj : 1 ≤ j) (S : Finset (PadicAlgCl l)) :
    ∃ H : Subgroup (PadicAlgCl l ≃ₐ[W] PadicAlgCl l), Small j H ∧ ∀ σ ∈ H, ∀ y ∈ S, σ y = y := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, small_top hW j hj, by simp⟩
  | insert α S _ ih =>
    obtain ⟨H, h1, h2⟩ := ih
    refine ⟨_, small_inf j H h1 α, fun σ hσ y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hσ.2
    · exact h2 σ hσ.1 y hy

open ReciprocityTheory.DiscreteGroups.LocalClassField in
theorem intVal_Kur : IntVal (MaximalUnramifiedExtension l ⊥) := by
  intro a ha
  obtain ⟨n, hn, h⟩ := (mem_Kur_iff (K := ⊥) inferInstance _).1 a.2
  obtain ⟨y, hy, e⟩ := norm_Kn l ⊥ inferInstance hn h
  obtain ⟨b, rfl⟩ := IntermediateField.mem_bot.1 hy
  have hb : b ≠ 0 := by
    rintro rfl
    rw [map_zero, norm_zero, norm_eq_zero] at e
    exact ha (Subtype.ext e)
  refine ⟨b.valuation, ?_⟩
  rw [e, PadicAlgCl.norm_extends, Padic.norm_eq_zpow_neg_valuation hb, inv_zpow']

open ReciprocityTheory.DiscreteGroups.LocalClassField in
theorem inert_Kur (σ : PadicAlgCl l ≃ₐ[MaximalUnramifiedExtension l (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))] PadicAlgCl l)
    (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) : ‖σ x - x‖ < 1 := by
  have key : ∀ y : PadicAlgCl l, ‖y‖ < 1 → ‖σ y - y‖ < 1 := fun y hy => by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rwa [norm_gal]
    · rwa [norm_neg]
  rcases hx.lt_or_eq with h | h
  · exact key x h
  · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := exists_teichmuller_bar x h
    have h1 : σ ζ = ζ := σ.commutes ⟨ζ, mem_Kur_of_pow (K := ⊥) inferInstance hm hζ⟩
    have := key _ hxζ
    rwa [map_sub, h1, sub_sub_sub_cancel_right] at this

end GlobalTheory.IntTate

open GlobalTheory.IntTate ReciprocityTheory.Neutral.Cmp in

theorem GlobalTheory.IntTate.integral_tate_inertia : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
  ∀ (j : ℕ), 1 ≤ j → ∀ F : Finset Ω, ∃ c : ℕ, ∀ (n : ℕ) (x : Ω), x ∈ A →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → CgA A l n (s x) ((((cycMod ℚ Ω l n s : ZMod (l ^ n)).val : ℕ) : Ω) ^ j * x)) →
  CgA A l n ((l : Ω) ^ c * x) 0 := by
  intro l hl Ω _ _ _ A hA j hj F
  classical
  obtain ⟨ι, hι⟩ := exists_compat ℚ A hA
  obtain ⟨G, ⟨C, hC⟩, hG⟩ := small_finset (intVal_Kur (l := l)) j hj (F.image ι)
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hq0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt C hl1
  refine ⟨c, fun n x hx H => ?_⟩
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  have hl0' : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  refine ⟨(l : Ω) ^ c * x / (l : Ω) ^ n, ?_, by field_simp; ring⟩
  rw [hι, map_div₀, map_mul, map_pow, map_pow, map_natCast, norm_div,
    div_le_one (norm_pos_iff.mpr (pow_ne_zero _ hl0')), norm_mul, norm_pow, norm_pow, GlobalTheory.CycTrace.norm_l,
    inv_pow, inv_mul_le_iff₀ (by positivity)]
  refine (hC (ι x) _ fun σ hσ => ?_).trans (mul_le_mul_of_nonneg_right hc.le (by positivity))
  have hK : Kloc ℚ ι ≤ ⊥ := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨q, rfl⟩
    refine IntermediateField.mem_bot.mpr ⟨(q : ℚ_[l]), ?_⟩
    simp
  let σ' : GK ℚ ι :=
    { σ.toRingEquiv with
      commutes' := fun k => σ.commutes ⟨k, ReciprocityTheory.DiscreteGroups.LocalClassField.le_Kur (hK k.2)⟩ }
  have hσ' : ∀ z, σ' z = σ z := fun _ => rfl
  have hs := (res_mem_ine_iff hι σ').2 (inert_Kur σ)
  obtain ⟨z, hz, e⟩ := H _ hs (fun y hy => ι.injective (by
    rw [res_spec, hσ']; exact hG σ hσ _ (Finset.mem_image_of_mem _ hy)))
  have hχ : (cycMod ℚ Ω l n (res ι σ') : ZMod (l ^ n)) = PadicInt.toZModPow n (chi _ σ) := by
    have := cycZ_res ι l σ'
    change PadicInt.toZModPow n ((cycZ ℚ Ω l (res ι σ') : ℤ_[l]ˣ) : ℤ_[l]) = _
    rw [this]
    rfl
  have e' := congrArg ι e
  rw [map_sub, res_spec, hσ', map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, hχ] at e'
  set v := (PadicInt.toZModPow n (chi _ σ)).val with hv
  have e2 : σ (ι x) - emb l (chi _ σ ^ j) * ι x =
      (l : PadicAlgCl l) ^ n * ι z + emb l ((v : ℤ_[l]) ^ j - chi _ σ ^ j) * ι x := by
    rw [← e', map_sub, map_pow (emb l) (v : ℤ_[l]), map_natCast]; ring
  rw [e2]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, norm_pow, GlobalTheory.CycTrace.norm_l]
    exact mul_le_of_le_one_right (by positivity) ((hι z).1 hz)
  · rw [norm_mul, norm_emb]
    refine (mul_le_of_le_one_right (norm_nonneg _) ((hι x).1 hx)).trans (norm_le_of_toZModPow _ _ ?_)
    have : NeZero (l ^ n) := ⟨(pow_pos hl.out.pos _).ne'⟩
    rw [map_sub, map_pow, map_pow, map_natCast, hv, ZMod.natCast_zmod_val, sub_self]
