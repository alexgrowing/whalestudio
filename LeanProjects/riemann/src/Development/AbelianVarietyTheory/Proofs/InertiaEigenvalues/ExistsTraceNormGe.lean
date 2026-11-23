import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalToGlobal.ProjectiveLattices.AvMono
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCycCycChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPowStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial

noncomputable section

namespace GlobalTheory.Cyc

namespace DiffSmall

variable {l : ℕ} [Fact l.Prime]

theorem norm_gal (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv g x).symm

theorem norm_sub_le_max' (a b : Om l) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max a (-b)
  rwa [norm_neg, ← sub_eq_add_neg] at this

theorem norm_add_le_of_le {a b : Om l} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem norm_sub_le_one {a b : Om l} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 :=
  (norm_sub_le_max' a b).trans (max_le ha hb)

theorem norm_sum_le_of_le {ι : Type*} (s : Finset ι) (f : ι → Om l) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i ∈ s, ‖f i‖ ≤ r) : ‖∑ i ∈ s, f i‖ ≤ r :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr h

theorem norm_pow_sub_pow_le {u v : Om l} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (a : ℕ) :
    ‖u ^ a - v ^ a‖ ≤ ‖u - v‖ := by
  induction a with
  | zero => simp
  | succ a ih =>
    have : u ^ (a + 1) - v ^ (a + 1) = u * (u ^ a - v ^ a) + v ^ a * (u - v) := by ring
    rw [this]
    refine norm_add_le_of_le ?_ ?_
    · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hu).trans ih
    · rw [norm_mul, norm_pow]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hv)

theorem exists_generator (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] E] :
    ∃ x ∈ E, ‖x‖ ≤ 1 ∧ ∀ z ∈ E, ‖z‖ ≤ 1 → ∃ p : ℤ_[l][X], aeval x p = z := by
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] E
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] E
  have : Finite (IsLocalRing.ResidueField ℤ_[l]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := l)).toEquiv.symm
  obtain ⟨θ, hθ⟩ : ∃ θ : integralClosure ℤ_[l] E, Algebra.adjoin ℤ_[l] {θ} = ⊤ :=
    Formalism.L2.Pj.AvAlg.exists_adjoin_eq_top (FaithfulSMul.algebraMap_injective _ _)
  refine ⟨((θ : E) : Om l), (θ : E).2, (mem_integralClosure_padicInt_iff E _).1 θ.2, fun z hz hn => ?_⟩
  have hm : (⟨⟨z, hz⟩, (mem_integralClosure_padicInt_iff E _).2 hn⟩ : integralClosure ℤ_[l] E) ∈
      Algebra.adjoin ℤ_[l] {θ} := by rw [hθ]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
  obtain ⟨p, hp⟩ := hm
  refine ⟨p, ?_⟩
  let φ : integralClosure ℤ_[l] E →ₐ[ℤ_[l]] Om l :=
    (E.val.restrictScalars ℤ_[l]).comp (integralClosure ℤ_[l] E).val
  have := congrArg φ hp
  rw [show (aeval θ).toRingHom p = aeval θ p from rfl, ← aeval_algHom_apply] at this
  exact this

theorem gal_aeval (g : GQ l) (x : Om l) (p : ℤ_[l][X]) : g (aeval x p) = aeval (g x) p :=
  (aeval_algHom_apply ((g : Om l →ₐ[ℚ_[l]] Om l).restrictScalars ℤ_[l]) x p).symm

def intPoly (l : ℕ) [Fact l.Prime] : Subring (Om l)[X] :=
  liftsRing (algebraMap (integralClosure ℤ_[l] (Om l)) (Om l))

theorem mem_intPoly {Q : (Om l)[X]} : Q ∈ intPoly l ↔ ∀ n, ‖Q.coeff n‖ ≤ 1 := by
  rw [intPoly, ← lifts_iff_liftsRing, lifts_iff_coeff_lifts]
  refine forall_congr' fun n => ?_
  rw [← isIntegral_padicInt_iff_norm_le_one]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

theorem C_mem_intPoly {a : Om l} (ha : ‖a‖ ≤ 1) : C a ∈ intPoly l := by
  rw [mem_intPoly]; intro n; rw [coeff_C]; split_ifs <;> simp [ha]

theorem X_mem_intPoly : (X : (Om l)[X]) ∈ intPoly l := by
  rw [mem_intPoly]; intro n; rw [coeff_X]; split_ifs <;> simp

theorem map_mem_intPoly (p : ℤ_[l][X]) : p.map (algebraMap ℤ_[l] (Om l)) ∈ intPoly l := by
  rw [mem_intPoly]; intro n
  rw [coeff_map, ← isIntegral_padicInt_iff_norm_le_one]
  exact isIntegral_algebraMap

theorem norm_eval_le_prod {ι : Type*} (T : Finset ι) (r : ι → Om l) (hinj : Set.InjOn r T)
    (hr : ∀ k ∈ T, ‖r k‖ ≤ 1) {x : Om l} (hx : ‖x‖ ≤ 1) :
    ∀ Q ∈ intPoly l, (∀ k ∈ T, Q.eval (r k) = 0) → ‖Q.eval x‖ ≤ ∏ k ∈ T, ‖x - r k‖ := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro Q hQ _
    rw [Finset.prod_empty, eval_eq_sum_range]
    refine norm_sum_le_of_le _ _ zero_le_one fun n _ => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (mem_intPoly.1 hQ n) (by positivity) (pow_le_one₀ (norm_nonneg _) hx)
  | insert a T ha ih =>
    intro Q hQ hroot
    obtain ⟨Q₀, rfl⟩ := hQ
    let a₀ : integralClosure ℤ_[l] (Om l) :=
      ⟨r a, (isIntegral_padicInt_iff_norm_le_one _).2 (hr a (Finset.mem_insert_self _ _))⟩
    have h0 : Q₀.IsRoot a₀ := by
      have := hroot a (Finset.mem_insert_self _ _)
      rw [coe_mapRingHom, show r a = algebraMap _ (Om l) a₀ from rfl, eval_map, eval₂_at_apply] at this
      exact Subtype.ext this
    obtain ⟨Q₁, rfl⟩ := dvd_iff_isRoot.2 h0
    have he : ∀ z, eval z (mapRingHom (algebraMap (integralClosure ℤ_[l] (Om l)) (Om l))
        ((X - C a₀) * Q₁)) = (z - r a) * eval z (Q₁.map (algebraMap _ (Om l))) := by
      intro z
      simp [a₀]
    rw [he, Finset.prod_insert ha, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine ih (hinj.mono (by simp)) (fun k hk => hr k (Finset.mem_insert_of_mem hk)) _ ⟨Q₁, rfl⟩
      fun k hk => ?_
    have := hroot k (Finset.mem_insert_of_mem hk)
    rw [he] at this
    refine (mul_eq_zero.1 this).resolve_left fun h => ha ?_
    have := hinj (by simp [hk]) (by simp) (sub_eq_zero.1 h)
    exact this ▸ hk

theorem exists_power_sum {ι : Type*} [DecidableEq ι] (S : Finset ι) (r : ι → Om l)
    (hr : ∀ s ∈ S, ‖r s‖ ≤ 1) {s₀ : ι} (h₀ : s₀ ∈ S) :
    ∃ k : ℕ, ∏ t ∈ S.erase s₀, ‖r s₀ - r t‖ ≤ ‖∑ s ∈ S, r s ^ k‖ := by
  set P : (Om l)[X] := ∏ t ∈ S.erase s₀, (X - C (r t)) with hP
  have hPi : P ∈ intPoly l := prod_mem fun t ht =>
    sub_mem X_mem_intPoly (C_mem_intPoly (hr t (Finset.mem_of_mem_erase ht)))
  have h1 : ∑ s ∈ S, P.eval (r s) = ∏ t ∈ S.erase s₀, (r s₀ - r t) := by
    rw [Finset.sum_eq_single_of_mem s₀ h₀]
    · simp [hP, eval_prod]
    · intro s hs hne
      rw [hP, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, hs⟩) (by simp)
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.range (P.natDegree + 1))
    (fun k => ‖∑ s ∈ S, r s ^ k‖) ⟨0, by simp⟩
  refine ⟨k, ?_⟩
  rw [← norm_prod, ← h1]
  simp_rw [eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine norm_sum_le_of_le _ _ (norm_nonneg _) fun n hn => ?_
  rw [← Finset.mul_sum, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (mem_intPoly.1 hPi n)).trans (hk n hn)

theorem norm_root {ζ : Om l} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : ‖ζ‖ = 1 := by
  have : ‖ζ‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

theorem norm_move_le (K : FinExt l) {τ : GQ l} (hτ : τ ∈ Gj K 1) (i : ℕ) (hi : 1 ≤ i) :
    ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ i) → ∀ z ∈ Ks K i, ‖z‖ ≤ 1 → ‖τ z - z‖ ≤ ‖τ ζ - ζ‖ := by
  have hl : l.Prime := Fact.out
  induction i, hi using Nat.le_induction with
  | base =>
    intro ζ _ z hz _
    have : τ z = z := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ z hz
    simp [this]
  | succ i hi ih =>
    intro ζ hζ z hz hn
    obtain ⟨y, hy, rfl⟩ := (GlobalTheory.T.integers_eq_sum_zeta_pow_unique l K (i + 1) (by omega) ζ hζ).1 z hz hn
    have hζ1 : ‖ζ‖ ≤ 1 := (norm_root (pow_ne_zero _ hl.ne_zero) hζ.pow_eq_one).le
    have hτ1 : ‖τ ζ‖ ≤ 1 := by rwa [norm_gal]
    have hζ' : IsPrimitiveRoot (ζ ^ l) (l ^ i) :=
      hζ.pow (pow_pos hl.pos _) (by ring)
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine norm_sum_le_of_le _ _ (norm_nonneg _) fun a _ => ?_
    have : τ (ζ ^ (a : ℕ) * y a) - ζ ^ (a : ℕ) * y a =
        τ ζ ^ (a : ℕ) * (τ (y a) - y a) + y a * (τ ζ ^ (a : ℕ) - ζ ^ (a : ℕ)) := by
      rw [map_mul, map_pow]; ring
    rw [this]
    refine norm_add_le_of_le ?_ ?_
    · rw [norm_mul, norm_pow]
      refine (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hτ1)).trans ?_
      refine (ih _ hζ' _ (by simpa using (hy a).1) (hy a).2).trans ?_
      rw [map_pow]
      exact norm_pow_sub_pow_le hτ1 hζ1 _
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hy a).2).trans (norm_pow_sub_pow_le hτ1 hζ1 _)

theorem exists_gal_pow (K : FinExt l) (i m : ℕ) {ζ : Om l} (hζ : ζ ^ l ^ i = 1) :
    ∃ τ ∈ Gj K 1, τ ζ = ζ ^ (1 + l * m) := by
  have hl : l.Prime := Fact.out
  obtain ⟨χ, hχ⟩ := exists_isCyc l
  have hlt : ‖((l * m : ℕ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
    have := (Padic.norm_int_le_pow_iff_dvd (p := l) ((l * m : ℕ) : ℤ) 1).2 (by simp)
    simpa using this
  have hlt1 : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 :=
    zpow_lt_one_of_neg₀ (by exact_mod_cast hl.one_lt) (by simp)
  have hu : ‖((1 + l * m : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Nat.cast_add, Nat.cast_one, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_one,
      max_eq_left (hlt.trans hlt1.le)]
    rw [norm_one]
    exact (hlt.trans_lt hlt1).ne'
  obtain ⟨g, hg, hgu⟩ := (GlobalTheory.T.finrank_cyclotomicExt_and_cyclotomicChar_surjective l K).2 χ hχ _ hu
  refine ⟨g, (((cyc_basic l χ hχ).2.2 K g hg).1 1).2 ?_, ?_⟩
  · rw [hgu, Nat.cast_add, Nat.cast_one, add_sub_cancel_left]
    exact hlt
  · obtain ⟨a, ha, hga⟩ := hχ g i ζ hζ
    rw [hga]
    rw [hgu] at ha
    have hd : ((l : ℤ) ^ i) ∣ ((1 + l * m : ℕ) : ℤ) - (a : ℤ) := by
      rw [← Padic.norm_int_le_pow_iff_dvd]
      simpa using ha
    have hmod : a ≡ 1 + l * m [MOD l ^ i] := (Nat.modEq_iff_dvd).2 (by simpa using hd)
    rw [pow_eq_pow_mod a hζ, pow_eq_pow_mod (1 + l * m) hζ, hmod]

theorem prod_norm_one_sub {ω : Om l} {n : ℕ} (hn : 0 < n) (hω : IsPrimitiveRoot ω n) :
    ∏ k ∈ Finset.range (n - 1), ‖1 - ω ^ (k + 1)‖ = ‖(n : Om l)‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← norm_prod, Nat.add_sub_cancel, hω.prod_one_sub_pow_eq_order]
  simp

theorem norm_l_le (j : ℕ) : ∀ η : Om l, η ^ l ^ j = 1 → η ≠ 1 → ‖(l : Om l)‖ ≤ ‖1 - η‖ := by
  have hl : l.Prime := Fact.out
  induction j with
  | zero => intro η h h1; simp at h; exact absurd h h1
  | succ j ih =>
    intro η h h1
    have hη : ‖η‖ ≤ 1 := (norm_root (pow_ne_zero _ hl.ne_zero) h).le
    have hb : ∀ a : ℕ, ‖1 - η ^ a‖ ≤ ‖1 - η‖ := fun a => by
      simpa using norm_pow_sub_pow_le (u := (1 : Om l)) (by simp) hη a
    by_cases h2 : η ^ l = 1
    · have hp : IsPrimitiveRoot η l := by
        have := orderOf_eq_prime h2 h1
        have h3 := IsPrimitiveRoot.orderOf η
        rwa [this] at h3
      rw [← prod_norm_one_sub hl.pos hp]
      obtain ⟨m, hm⟩ : ∃ m, l - 1 = m + 1 := ⟨l - 2, by have := hl.two_le; omega⟩
      rw [hm, Finset.prod_range_succ]
      refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb _)
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ =>
        (hb _).trans (norm_sub_le_one (by simp) hη)
    · exact (ih (η ^ l) (by rw [← pow_mul, ← h]; ring) h2).trans (hb _)

theorem prod_lift_le (F E : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ F.fixingSubgroup)
    (hu : ∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ E.fixingSubgroup)
    {x : Om l} (hxE : x ∈ E) (hx : ‖x‖ ≤ 1) (τ : GQ l) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hτ : ∀ z ∈ F, ‖z‖ ≤ 1 → ‖τ z - z‖ ≤ ρ) : ∏ s ∈ S, ‖x - τ (s x)‖ ≤ ρ := by
  classical
  have hfix : ∀ s t : GQ l, s⁻¹ * t ∈ E.fixingSubgroup → t x = s x := by
    intro s t h
    have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 h x hxE
    have h2 := congrArg s this
    simpa using h2
  set f : (Om l)[X] := ∏ s ∈ S, (X - C (s x)) with hf
  have hfi : f ∈ intPoly l := prod_mem fun t _ =>
    sub_mem X_mem_intPoly (C_mem_intPoly (by rwa [norm_gal]))
  have hmap : ∀ g : GQ l, f.map (g : Om l →+* Om l) = ∏ s ∈ S, (X - C (g (s x))) := by
    intro g
    simp [hf, Polynomial.map_prod]
  have hinv : ∀ h ∈ F.fixingSubgroup, f.map (h : Om l →+* Om l) = f := by
    intro h hh
    rw [hmap, hf]
    have hex := fun s (hs : s ∈ S) => hu (h * s) (mul_mem hh (hS s hs))
    choose φ hφ hφu using hex
    refine Finset.prod_bij φ (fun s hs => (hφ s hs).1) ?_ ?_ ?_
    · intro s hs t ht hst
      have h1 : s⁻¹ * t ∈ E.fixingSubgroup := by
        have := mul_mem (inv_mem (hφ s hs).2) (hφ t ht).2
        rw [hst] at this
        simpa [mul_assoc] using this
      exact (hu t (hS t ht)).unique ⟨hs, h1⟩ ⟨ht, by simp⟩
    · intro t ht
      obtain ⟨s, ⟨hs, h1⟩, -⟩ := hu (h⁻¹ * t) (mul_mem (inv_mem hh) (hS t ht))
      refine ⟨s, hs, (hφu s hs t ⟨ht, ?_⟩).symm⟩
      simpa [mul_assoc] using inv_mem h1
    · intro s hs
      rw [← hfix _ _ (hφ s hs).2]
      rfl
  have hcoef : ∀ n, f.coeff n ∈ F := by
    intro n
    rw [← InfiniteGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff]
    intro h hh
    conv_rhs => rw [← hinv h hh, coeff_map]
    rfl
  have h0 : f.eval x = 0 := by
    obtain ⟨s, ⟨hs, h1⟩, -⟩ := hu 1 (one_mem _)
    rw [hf, eval_prod]
    refine Finset.prod_eq_zero hs ?_
    rw [← hfix _ _ h1]
    simp
  have h1 : ∏ s ∈ S, (x - τ (s x)) = (f.map (τ : Om l →+* Om l) - f).eval x := by
    rw [eval_sub, h0, sub_zero, hmap, eval_prod]
    simp
  rw [← norm_prod, h1, eval_eq_sum_range]
  refine norm_sum_le_of_le _ _ hρ fun n _ => ?_
  rw [norm_mul, norm_pow, coeff_sub, coeff_map]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)).trans
    (hτ _ (hcoef n) (mem_intPoly.1 hfi n))

theorem finite_orbit (y : Om l) : (Set.range fun g : GQ l => g y).Finite := by
  have hy : IsIntegral ℚ_[l] y := Algebra.IsIntegral.isIntegral y
  refine ((minpoly ℚ_[l] y).rootSet_finite (Om l)).subset ?_
  rintro _ ⟨g, rfl⟩
  rw [mem_rootSet]
  refine ⟨minpoly.ne_zero hy, ?_⟩
  change aeval ((g : Om l →ₐ[ℚ_[l]] Om l) y) _ = 0
  rw [aeval_algHom_apply, minpoly.aeval, map_zero]

theorem exists_lower_bound {y : Om l} (hy : ‖y‖ ≤ 1) : ∃ c : ℝ, 0 < c ∧
    ∀ (x : Om l) (p : ℤ_[l][X]), ‖x‖ ≤ 1 → aeval x p = y → ∀ (T : Finset ℕ) (g : ℕ → GQ l),
      Set.InjOn (fun k => g k x) T → (∀ k ∈ T, g k y ≠ y) → c ≤ ∏ k ∈ T, ‖x - g k x‖ := by
  classical
  set R := (finite_orbit y).toFinset with hR
  refine ⟨∏ r ∈ R.erase y, ‖y - r‖, Finset.prod_pos fun r hr => ?_, ?_⟩
  · exact norm_pos_iff.2 (sub_ne_zero.2 (Finset.ne_of_mem_erase hr).symm)
  intro x p hx hp T g hinj hne
  set Q : (Om l)[X] := ∏ r ∈ R.erase y, (p.map (algebraMap ℤ_[l] (Om l)) - C r) with hQ
  have hev : ∀ z, Q.eval z = ∏ r ∈ R.erase y, (aeval z p - r) := by
    intro z
    simp [hQ, eval_prod, eval_map_algebraMap]
  have := norm_eval_le_prod T (fun k => g k x) hinj (fun k _ => by rwa [norm_gal]) hx Q
    (prod_mem fun r hr => sub_mem (map_mem_intPoly p) (C_mem_intPoly ?_)) fun k hk => ?_
  · rwa [hev, hp, norm_prod] at this
  · have := Finset.mem_of_mem_erase hr
    rw [hR, Set.Finite.mem_toFinset] at this
    obtain ⟨g, rfl⟩ := this
    rwa [norm_gal]
  · rw [hev, ← gal_aeval, hp]
    refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne k hk, ?_⟩) (sub_self _)
    rw [hR, Set.Finite.mem_toFinset]
    exact ⟨g k, rfl⟩

theorem norm_l_lt_one : ‖(l : Om l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)) l, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_l_pos : 0 < ‖(l : Om l)‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem mem_Ks (K : FinExt l) {i : ℕ} {ζ : Om l} (h : ζ ^ l ^ i = 1) : ζ ∈ Ks K i :=
  (le_sup_right : _ ≤ Ks K i) (IntermediateField.subset_adjoin _ _ h)

theorem exists_moved (K : FinExt l) {y : Om l} (hy : ‖y‖ ≤ 1) (n : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) : ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ (E : IntermediateField ℚ_[l] (Om l))
      [FiniteDimensional ℚ_[l] E], Ks K i ≤ E → y ∈ E → ∀ S : Finset (GQ l), S.card ≤ n →
      (∀ s ∈ S, s ∈ Gj K i) → (∀ h ∈ Gj K i, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ E.fixingSubgroup) →
      ∃ x ∈ E, ‖x‖ ≤ 1 ∧ ∀ σ ∈ Gj K i, σ y ≠ y → δ ≤ ‖x - σ x‖ := by
  have hl : l.Prime := Fact.out
  obtain ⟨c, hc0, hc⟩ := exists_lower_bound hy
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one (norm_l_pos (l := l)) hδ
  set N := N₀ + n with hN
  have hδN : δ ^ N ≤ ‖(l : Om l)‖ := (pow_le_pow_of_le_one hδ0 hδ.le (by omega)).trans hN₀.le
  obtain ⟨j₀, hj₀⟩ := exists_pow_lt_of_lt_one (pow_pos hc0 N) (norm_l_lt_one (l := l))
  refine ⟨j₀ + 1, fun i hi E _ hKE hyE S hSn hS hu => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨x, hxE, hx, hgen⟩ := exists_generator E
  refine ⟨x, hxE, hx, fun σ hσ hσy => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  haveI : NeZero (l ^ (j + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ (j + 1))
  have hζ1 : ‖ζ‖ = 1 := norm_root (pow_ne_zero _ hl.ne_zero) hζ.pow_eq_one
  have hζK : ζ ∈ Ks K (j + 1) := mem_Ks K hζ.pow_eq_one
  have hω : IsPrimitiveRoot (ζ ^ l) (l ^ j) := hζ.pow (pow_pos hl.pos _) (by ring)
  have hfixζ : ∀ s ∈ Gj K (j + 1), s ζ = ζ := fun s hs =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ hζK
  have hSne : S.Nonempty := by
    obtain ⟨s, ⟨hs, -⟩, -⟩ := hu 1 (one_mem _)
    exact ⟨s, hs⟩
  have key : ∀ k : ℕ, ∃ g : GQ l, k ∈ Finset.range (l ^ j - 1) →
      g y ≠ y ∧ g ζ = ζ * (ζ ^ l) ^ (k + 1) ∧ ‖x - g x‖ ^ N ≤ ‖1 - (ζ ^ l) ^ (k + 1)‖ := by
    intro k
    by_cases hk : k ∈ Finset.range (l ^ j - 1)
    swap
    · exact ⟨1, fun h => absurd h hk⟩
    rw [Finset.mem_range] at hk
    obtain ⟨τ, hτ, hτζ⟩ := exists_gal_pow K (j + 1) (k + 1) hζ.pow_eq_one
    have hτζ' : τ ζ = ζ * (ζ ^ l) ^ (k + 1) := by rw [hτζ]; ring
    have hnorm : ‖τ ζ - ζ‖ = ‖1 - (ζ ^ l) ^ (k + 1)‖ := by
      rw [hτζ', norm_sub_rev, ← mul_one_sub, norm_mul, hζ1, one_mul]
    have hprod := prod_lift_le (Ks K (j + 1)) E S hS hu hxE hx τ (norm_nonneg _)
      (norm_move_le K hτ (j + 1) (by omega) ζ hζ)
    rw [hnorm] at hprod
    obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image S (fun s => ‖x - τ (s x)‖) hSne
    have hle1 : ‖x - τ (s x)‖ ≤ 1 := norm_sub_le_one hx (by rwa [norm_gal, norm_gal])
    have hA : ‖x - τ (s x)‖ ^ N ≤ ‖1 - (ζ ^ l) ^ (k + 1)‖ := by
      refine (pow_le_pow_of_le_one (norm_nonneg _) hle1 (show S.card ≤ N by omega)).trans ?_
      refine le_trans ?_ hprod
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hmin
    by_cases hm : τ (s y) = y
    · refine ⟨σ * τ * s, fun _ => ⟨?_, ?_, ?_⟩⟩
      · simpa [hm] using hσy
      · simp only [AlgEquiv.mul_apply]
        rw [hfixζ s (hS s hs), hτζ', map_mul, map_pow, map_pow, hfixζ σ hσ]
      · have hB : ‖x - σ x‖ ^ N ≤ ‖1 - (ζ ^ l) ^ (k + 1)‖ := by
          refine (pow_le_pow_left₀ (norm_nonneg _) hlt.le N).trans (hδN.trans ?_)
          refine norm_l_le j _ ?_ (hω.pow_ne_one_of_pos_of_lt (by omega) (by omega))
          rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
        have hC : ‖x - (σ * τ * s) x‖ ≤ max ‖x - σ x‖ ‖x - τ (s x)‖ := by
          have : x - (σ * τ * s) x = (x - σ x) + σ (x - τ (s x)) := by
            simp only [AlgEquiv.mul_apply, map_sub]; ring
          rw [this, ← norm_gal σ (x - τ (s x))]
          exact IsUltrametricDist.norm_add_le_max _ _
        refine (pow_le_pow_left₀ (norm_nonneg _) hC N).trans ?_
        rcases max_choice ‖x - σ x‖ ‖x - τ (s x)‖ with h | h <;> rw [h]
        exacts [hB, hA]
    · refine ⟨τ * s, fun _ => ⟨hm, ?_, hA⟩⟩
      simp only [AlgEquiv.mul_apply]
      rw [hfixζ s (hS s hs), hτζ']
  choose g hg using key
  obtain ⟨p, hp⟩ := hgen y hyE hy
  obtain ⟨q, hq⟩ := hgen ζ (hKE hζK) hζ1.le
  have hinj : Set.InjOn (fun k => g k x) (Finset.range (l ^ j - 1) : Finset ℕ) := by
    intro a ha b hb hab
    have h1 : g a ζ = g b ζ := by
      rw [← hq, gal_aeval, gal_aeval]
      exact congrArg (fun z => aeval z q) hab
    rw [(hg a ha).2.1, (hg b hb).2.1] at h1
    have h2 := mul_left_cancel₀ (hζ.ne_zero (pow_ne_zero _ hl.ne_zero)) h1
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    have := hω.pow_inj (by omega) (by omega) h2
    omega
  have h1 := hc x p hx hp _ g hinj fun k hk => (hg k hk).1
  have h2 : c ^ N ≤ ‖(l : Om l)‖ ^ j := by
    refine (pow_le_pow_left₀ hc0.le h1 N).trans ?_
    rw [← Finset.prod_pow, ← norm_pow, ← Nat.cast_pow, ← prod_norm_one_sub (pow_pos hl.pos j) hω]
    exact Finset.prod_le_prod (fun _ _ => by positivity) fun k hk => (hg k hk).2.2
  have h3 : ‖(l : Om l)‖ ^ j ≤ ‖(l : Om l)‖ ^ j₀ :=
    pow_le_pow_of_le_one (norm_nonneg _) norm_l_lt_one.le (by omega)
  linarith

theorem finite_Ks (K : FinExt l) (i : ℕ) : FiniteDimensional ℚ_[l] (Ks K i) := by
  classical
  have hl : l.Prime := Fact.out
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  haveI : Finite {x : Om l | x ^ (l ^ i) = 1} := by
    refine ((Polynomial.nthRoots (l ^ i) (1 : Om l)).toFinset.finite_toSet.subset ?_).to_subtype
    intro x hx
    simpa [mem_nthRoots (pow_pos hl.pos i)] using hx
  haveI := IntermediateField.finiteDimensional_adjoin (K := ℚ_[l]) (S := {x : Om l | x ^ (l ^ i) = 1})
    fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _

theorem exists_primitive (L : FinExt l) : ∃ y ∈ L.1, ‖y‖ ≤ 1 ∧
    ∀ g : GQ l, g y = y → g ∈ L.1.fixingSubgroup := by
  haveI := L.2
  obtain ⟨x, hxL, hx, hgen⟩ := exists_generator L.1
  refine ⟨x, hxL, hx, fun g hg => (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz => ?_⟩
  have h1 : ∀ z ∈ L.1, ‖z‖ ≤ 1 → g z = z := fun z hz hn => by
    obtain ⟨p, rfl⟩ := hgen z hz hn
    rw [gal_aeval, hg]
  by_cases hn : ‖z‖ ≤ 1
  · exact h1 z hz hn
  · have := h1 z⁻¹ (inv_mem hz) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_le.1 hn).le)
    rwa [map_inv₀, inv_inj] at this

end DiffSmall

open DiffSmall in

theorem exists_trace_norm_ge : ∀ (l : ℕ) [Fact l.Prime] (K L' : FinExt l) (ε : ℝ), 0 < ε → ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ S : Finset (GQ l), (∀ s ∈ S, s ∈ Gj K i) → (∀ h ∈ Gj K i, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup) → ∃ b : Om l, b ∈ L'.1 ⊔ Ks K i ∧ ‖b‖ ≤ 1 ∧ 1 - ε ≤ ‖∑ s ∈ S, s b‖ := by
  classical
  intro l _ K L' ε hε
  obtain ⟨y, hyL, hy, hyg⟩ := exists_primitive L'
  set n := (finite_orbit y).toFinset.card with hn
  set a : ℝ := min 1 (ε / (n + 1)) with ha
  have ha0 : 0 < a := lt_min one_pos (by positivity)
  have ha1 : a ≤ 1 := min_le_left _ _
  have hδ : 1 - ε ≤ (1 - a) ^ n := by
    have h1 := one_add_mul_le_pow (a := -a) (by linarith) n
    have h2 : a * (n + 1) ≤ ε := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    rw [sub_eq_add_neg 1 a]
    nlinarith
  obtain ⟨i₀, hi₀⟩ := exists_moved K hy n (δ := 1 - a) (by linarith) (by linarith)
  refine ⟨i₀, fun i hi S hS hu => ?_⟩
  haveI := L'.2
  haveI := finite_Ks K i
  have hsep : ∀ s ∈ S, ∀ t ∈ S, (s⁻¹ * t) y = y → s = t := by
    intro s hs t ht h
    refine (hu t (hS t ht)).unique ⟨hs, ?_⟩ ⟨ht, by simp⟩
    rw [IntermediateField.fixingSubgroup_sup]
    have h2 : s⁻¹ * t ∈ Gj K i := mul_mem (inv_mem (hS s hs)) (hS t ht)
    exact ⟨hyg _ h, h2⟩
  have hcard : S.card ≤ n := by
    refine Finset.card_le_card_of_injOn (fun s => s y) (fun s _ => ?_) fun s hs t ht h => ?_
    · simp
    · refine hsep s hs t ht ?_
      have h' : s y = t y := h
      rw [AlgEquiv.mul_apply, ← h']
      simp
  obtain ⟨x, hxE, hx, hmove⟩ := hi₀ i hi (L'.1 ⊔ Ks K i) le_sup_right
    ((le_sup_left : L'.1 ≤ _) hyL) S hcard hS hu
  obtain ⟨s₀, ⟨h₀, -⟩, -⟩ := hu 1 (one_mem _)
  obtain ⟨k, hk⟩ := exists_power_sum S (fun s => s x) (fun s _ => by rwa [norm_gal]) h₀
  refine ⟨x ^ k, pow_mem hxE k, by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx, ?_⟩
  simp only [map_pow]
  refine hδ.trans (le_trans ?_ hk)
  refine (pow_le_pow_of_le_one (by linarith) (by linarith)
    ((Finset.card_erase_le (a := s₀)).trans hcard)).trans ?_
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => by linarith) fun t ht => ?_
  have ht' := Finset.mem_of_mem_erase ht
  have := hmove (s₀⁻¹ * t) (mul_mem (inv_mem (hS s₀ h₀)) (hS t ht'))
    fun h => Finset.ne_of_mem_erase ht (hsep s₀ h₀ t ht' h).symm
  rw [← norm_gal s₀] at this
  simpa using this

end GlobalTheory.Cyc
