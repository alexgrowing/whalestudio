import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK Filter Topology
open scoped Formalism.Per

namespace GlobalTheory.BKReal

section Ext

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (l : ℕ) [hl : Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

omit [IsUltrametricDist K] in

theorem eq_sum_monomial_add (x : K⟦X⟧) (N : ℕ) : x = ∑ n ∈ Finset.range N, monomial n (coeff n x) +
    X ^ N * PowerSeries.mk fun n => coeff (n + N) x := by
  ext n
  simp only [map_add, map_sum, coeff_monomial, coeff_X_pow_mul', coeff_mk, Finset.sum_ite_eq,
    Finset.mem_range]
  split_ifs with h1 h2 h2
  · omega
  · simp
  · simp [Nat.sub_add_cancel h2]
  · omega

omit [NeZero e] in

theorem exists_sum_monomial_add {x : K⟦X⟧} (hx : x ∈ S O K e) (m : ℕ) : ∃ N₀, ∀ N ≥ N₀, ∃ h ∈ S O K e,
    x = ∑ n ∈ Finset.range N, monomial n (coeff n x) + (l : K⟦X⟧) ^ m * h := by
  have h0 : (l : K) ^ m ≠ 0 := pow_ne_zero _ (BK.l_ne_zero l)
  obtain ⟨N₀, hN⟩ := eventually_atTop.1 (hx.2.eventually (ge_mem_nhds (norm_pos_iff.2 h0)))
  refine ⟨N₀, fun N hN' => ⟨mk fun n => if n < N then 0 else ((l : K) ^ m)⁻¹ * coeff n x,
    ⟨fun n => ?_, ?_⟩, ?_⟩⟩
  · rw [coeff_mk]
    split_ifs with h
    · simp
    · rw [norm_mul, norm_inv, mul_assoc, inv_mul_le_one₀ (norm_pos_iff.2 h0)]
      exact hN n (by omega)
  · have := hx.2.const_mul ‖((l : K) ^ m)⁻¹‖
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [coeff_mk, if_neg (by omega), norm_mul, mul_assoc]
  · ext n
    rw [← map_natCast (C : K →+* K⟦X⟧), ← map_pow]
    simp only [map_add, map_sum, coeff_monomial, coeff_C_mul, coeff_mk, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with h
    · simp
    · rw [zero_add, mul_inv_cancel_left₀ h0]

omit [NeZero e] in

theorem monomial_mem_invL (n : ℕ) (c : K) : monomial n c ∈ invL l (A O K) := by
  rw [monomial_eq_C_mul_X_pow]
  exact mul_mem (HasK.C_mem c) (pow_mem HasU.X_mem n)

variable (O K) in

abbrev Sb : Subalgebra O K⟦X⟧ := S O K e ⊓ invL l (A O K)

omit [NeZero e] in

theorem sameJets_Sb : SameJets (Subalgebra.inclusion (inf_le_left : Sb O K l e ≤ S O K e)).toRingHom
    (l : Sb O K l e) where
  div m x := by
    obtain ⟨N, hN⟩ := exists_sum_monomial_add l e x.2 m
    obtain ⟨h, hh, hx⟩ := hN N le_rfl
    refine ⟨⟨_, Subalgebra.sum_mem _ fun n (_ : n ∈ Finset.range N) =>
      ⟨monomial_mem_S (x.2.1 n), monomial_mem_invL l n _⟩⟩, ⟨h, hh⟩, Subtype.ext ?_⟩
    rw [map_natCast]
    simpa using hx
  dvd m g h hg := by
    rw [map_natCast] at hg
    have h1 : (g : K⟦X⟧) = (l : K⟦X⟧) ^ m * h := by simpa using congrArg Subtype.val hg
    obtain ⟨k, hk⟩ := g.2.2
    refine ⟨⟨h, h.2, k + m, ?_⟩, Subtype.ext (by simpa using h1)⟩
    rw [h1, ← mul_assoc] at hk
    simpa [pow_add] using hk

variable {R : Type} [CommRing R]

theorem ringHom_ext_S (htf : ∀ x : R, (l : R) * x = 0 → x = 0) (hs : ∀ x : R, (∀ n, (l : R) ^ n ∣ x) → x = 0)
    (g g' : S O K e →+* R) (h : ∀ x : A O K, g ⟨x, A_le_S l e x.2⟩ = g' ⟨x, A_le_S l e x.2⟩) : g = g' := by
  have htf' : ∀ (k : ℕ) (x : R), (l : R) ^ k * x = 0 → x = 0 := fun k => by
    induction k with
    | zero => simp
    | succ k ih => exact fun x hx => htf x (ih _ (by rw [← mul_assoc, ← pow_succ, hx]))
  ext x
  rw [← sub_eq_zero]
  refine hs _ fun m => ?_
  obtain ⟨p, q, rfl⟩ := (sameJets_Sb l e).div m x
  obtain ⟨k, hk⟩ := p.2.2
  have h1 := h ⟨_, hk⟩
  have h2 : (⟨((l : A O K) : K⟦X⟧) ^ k * p, A_le_S l e hk⟩ : S O K e) = (l : S O K e) ^ k *
      (Subalgebra.inclusion (inf_le_left : Sb O K l e ≤ S O K e)).toRingHom p := Subtype.ext (by simp)
  rw [h2, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, ← sub_eq_zero, ← mul_sub] at h1
  simp only [map_add, map_mul, map_pow, map_natCast, sub_eq_zero.1 (htf' _ _ h1)]
  exact ⟨g q - g' q, by ring⟩

variable [Algebra O R]

theorem exists_extend_S (htf : ∀ x : R, (l : R) * x = 0 → x = 0) [IsAdicComplete (Ideal.span {(l : R)}) R]
    (f : A O K →ₐ[O] R) (hd : ∀ q : ℕ, ∃ d, (q.factorial : R) * d = f (uIn _) ^ (e * q)) :
    ∃ g : S O K e →ₐ[O] R, ∀ x : A O K, g ⟨x, A_le_S l e x.2⟩ = f x := by
  let j := algebraMap R (Localization.Away (l : R))
  have hj : Function.Injective j := IsLocalization.injective _ (Submonoid.powers_le.2
    (mem_nonZeroDivisors_iff.2 ⟨htf, fun x hx => htf x (by rw [mul_comm, hx])⟩))
  have hu : IsUnit ((j.comp f.toRingHom) (l : A O K)) := by
    rw [map_natCast, ← map_natCast j]; exact IsLocalization.Away.algebraMap_isUnit _
  let F : invL l (A O K) →+* Localization.Away (l : R) := IsLocalization.Away.lift (l : A O K) hu
  have hF : ∀ (x : K⟦X⟧) (h : x ∈ A O K) (h' : x ∈ invL l (A O K)), F ⟨x, h'⟩ = j (f ⟨x, h⟩) :=
    fun x h _ => IsLocalization.Away.lift_eq (S := invL l (A O K)) (l : A O K) hu ⟨x, h⟩
  have hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : Localization.Away (l : R)) := fun n hn => by
    simpa only [map_natCast] using
      ((natCast_ne_zero' (K := K) l hn).isUnit.map (algebraMap K (invL l (A O K)))).map F
  have hu' : F (uIn _) = j (f (uIn _)) := hF _ _ _
  have h1 : ∀ (n : ℕ) (c : K), ‖c‖ * wS K e n ≤ 1 → F ⟨_, monomial_mem_invL l n c⟩ ∈ j.range := by
    intro n c hc
    obtain ⟨b, hb⟩ := (IsUnitBall.mem_range_iff (O := O) (c * ((n / e).factorial : K))).2 (by
      rwa [norm_mul])
    obtain ⟨d, hd⟩ := hd (n / e)
    refine ⟨algebraMap O R b * f (uIn _) ^ (n % e) * d, (hn _ (n / e).factorial_ne_zero).mul_left_cancel ?_⟩
    have h2 : ((n / e).factorial : invL l (A O K)) * ⟨_, monomial_mem_invL l n c⟩ =
        ⟨algebraMap O (A O K) b, le_away _ _ (algebraMap O (A O K) b).2⟩ * uIn _ ^ n := Subtype.ext (by
      change ((((n / e).factorial : ℕ) : invL l (A O K)) : K⟦X⟧) * monomial n c = algebraMap O K⟦X⟧ b * X ^ n
      rw [algebraMap_eq_C, hb, monomial_eq_C_mul_X_pow]
      simp only [SubringClass.coe_natCast, map_mul, map_natCast]
      ring)
    have h3 := congrArg F h2
    rw [map_mul, map_natCast, map_mul, map_pow, hu', hF _ (algebraMap O (A O K) b).2] at h3
    rw [h3, ← map_natCast j, ← map_pow j, ← map_mul j, ← map_mul j, mul_left_comm, hd, mul_assoc, ← pow_add,
      Nat.mod_add_div]
    exact congrArg (fun y => j (y * _)) (f.commutes b).symm
  have h2 : ∀ x : Sb O K l e, ∃ r, j r =
      (F.comp (Subalgebra.inclusion (inf_le_right : Sb O K l e ≤ invL l (A O K))).toRingHom) x := by
    rintro ⟨x, hx, k, hk⟩
    have hk' : ((l : A O K) : K⟦X⟧) ^ k * (mk fun n => coeff (n + e * l ^ k) x) ∈ A O K := fun n => by
      have h3 : ((l : A O K) : K⟦X⟧) ^ k = C ((l : K) ^ k) := by simp
      have := hk (n + e * l ^ k)
      rw [h3, coeff_C_mul] at this ⊢
      rwa [coeff_mk]
    have h3 : (⟨x, k, hk⟩ : invL l (A O K)) =
        ∑ n ∈ Finset.range (e * l ^ k), ⟨_, monomial_mem_invL l n (coeff n x)⟩ +
          uIn _ ^ (e * l ^ k) * ⟨_, k, hk'⟩ := Subtype.ext (by
      simpa using eq_sum_monomial_add x (e * l ^ k))
    change F ⟨x, k, hk⟩ ∈ j.range
    rw [h3, map_add, map_sum]
    refine add_mem (sum_mem fun n _ => h1 n _ (hx.1 n)) ?_
    obtain ⟨d, hd⟩ := hd (l ^ k)
    obtain ⟨m, hm⟩ := Nat.dvd_factorial (pow_pos hl.out.pos k) le_rfl
    refine ⟨m * d * f ⟨_, hk'⟩, ((hn l hl.out.ne_zero).pow k).mul_left_cancel ?_⟩
    have h4 : (l : invL l (A O K)) ^ k * ⟨_, k, hk'⟩ = ⟨_, le_away _ _ hk'⟩ := Subtype.ext (by simp)
    have h5 := congrArg F h4
    rw [map_mul, map_pow, map_natCast, hF _ hk'] at h5
    rw [map_mul F, map_pow, hu', mul_left_comm, h5, ← map_pow, ← hd, hm]
    simp only [map_mul, map_natCast, Nat.cast_mul, Nat.cast_pow, map_pow]
    ring
  let g₀ := liftInj _ j hj h2
  have hle : Ideal.span {(l : Sb O K l e)} ≤ (Ideal.span {(l : R)}).comap g₀ := by simp [Ideal.span_le]
  let g : S O K e →+* R := (AdicCompletion.ofAlgEquiv (Ideal.span {(l : R)})).symm.toRingEquiv.toRingHom.comp
    ((GlobalTheory.AdicMaps.adicMap _ _ g₀ hle).comp (sameJets_Sb l e).toCompl)
  have hg : ∀ x : A O K, g ⟨x, A_le_S l e x.2⟩ = f x := fun x => by
    have h3 := (sameJets_Sb (O := O) (K := K) l e).toCompl_ι ⟨x, A_le_S l e x.2, le_away _ _ x.2⟩
    have h4 : g₀ ⟨x, A_le_S l e x.2, le_away _ _ x.2⟩ = f x := hj ((liftInj_spec _ _ _ _ _).trans (hF _ x.2 _))
    refine (congrArg (fun y => (AdicCompletion.ofAlgEquiv (Ideal.span {(l : R)})).symm
      (GlobalTheory.AdicMaps.adicMap _ _ g₀ hle y)) h3).trans ?_
    rw [GlobalTheory.AdicMaps.adicMap_alg, h4]
    exact (AdicCompletion.ofAlgEquiv (Ideal.span {(l : R)})).symm.commutes _
  exact ⟨{ toRingHom := g, commutes' := fun o => (hg (algebraMap O _ o)).trans (f.commutes o) }, hg⟩

variable (K) in

def descN (i : ℕ) : Module.End K K⟦X⟧ := Polynomial.aeval (N K).toLinearMap (descPochhammer K i)

omit [IsUltrametricDist K] in

theorem coeff_descN (i : ℕ) (f : K⟦X⟧) (n : ℕ) :
    coeff n (descN K i f) = (n.descFactorial i : K) * coeff n f := by
  induction i generalizing f with
  | zero => simp [descN]
  | succ i ih =>
    rw [descN, descPochhammer_succ_right, map_mul, Module.End.mul_apply, ← descN, ih,
      ← descPochhammer_eval_eq_descFactorial K n (i + 1), descPochhammer_succ_eval,
      descPochhammer_eval_eq_descFactorial, map_sub, Polynomial.aeval_X, map_natCast, LinearMap.sub_apply,
      map_sub, Module.End.natCast_apply, map_nsmul, nsmul_eq_mul, Derivation.coeFn_coe, coeff_N]
    ring

omit [NeZero e] in

theorem descN_mem_S (i : ℕ) {f : K⟦X⟧} (hf : f ∈ S O K e) : descN K i f ∈ S O K e := by
  have key : ∀ n, ‖coeff n (descN K i f)‖ * wS K e n ≤ ‖coeff n f‖ * wS K e n := fun n => by
    rw [coeff_descN, norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _)
      (IsUltrametricDist.norm_natCast_le_one K _)) (wS_nonneg e n)
  exact ⟨fun n => (key n).trans (hf.1 _),
    squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) key hf.2⟩

end Ext

variable {l : ℕ} [hl : Fact l.Prime]

theorem phiA_eq_frobA_pt (w : Ainf l) : Per.φA l w = GlobalTheory.Cyc.IoMap.frobA l w :=
  (GlobalTheory.RingBasics.φA_apply l w).trans (GlobalTheory.Cyc.IoMap.frobA_apply l w).symm

theorem phiA_zl_pt (z : ℤ_[l]) : Per.φA l (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z :=
  (phiA_eq_frobA_pt _).trans ((GlobalTheory.Cyc.IoMap.frobA l).commutes z)

scoped instance algZlAcris : Algebra ℤ_[l] (Per.Acris l) :=
  ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))).toAlgebra

scoped instance algZlBcris : Algebra ℤ_[l] (Per.Bcris l) :=
  ((Per.aB l).comp (algebraMap ℤ_[l] (Ainf l))).toAlgebra

variable (l) in

def ainfToAcris : Ainf l →ₐ[ℤ_[l]] Per.Acris l where
  toRingHom := algebraMap (Ainf l) (Per.Acris l)
  commutes' _ := rfl

variable (l) in

def acrisToBcris : Per.Acris l →ₐ[ℤ_[l]] Per.Bcris l where
  toRingHom := algebraMap (Per.Acris l) (Per.Bcris l)
  commutes' _ := (GlobalTheory.RingIface.aB_eq_alg l _).symm

variable (l) in

def frobC : Per.Acris l →ₐ[ℤ_[l]] Per.Acris l where
  toRingHom := GlobalTheory.MemLoc.phiA l
  commutes' z := ((GlobalTheory.CrisMaps.phiA_extends l).alg _).trans (congrArg (algebraMap (Ainf l) _) (phiA_zl_pt z))

def galC (g : GQ l) : Per.Acris l →ₐ[ℤ_[l]] Per.Acris l where
  toRingHom := GlobalTheory.MemLoc.sigA g
  commutes' z := ((GlobalTheory.CrisMaps.sigA_extends g).alg _).trans (congrArg (algebraMap (Ainf l) _) ((galA g).commutes z))

variable (l) in

def frobB : Per.Bcris l →ₐ[ℤ_[l]] Per.Bcris l where
  toRingHom := Per.φB l
  commutes' z := ((GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.1 _).trans (congrArg (Per.aB l) (phiA_zl_pt z))

def galB (g : GQ l) : Per.Bcris l →ₐ[ℤ_[l]] Per.Bcris l where
  toRingHom := Per.σB g
  commutes' z := ((GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.1 g _).trans
    (congrArg (Per.aB l) ((galA g).commutes z))

theorem acris_nat_cancel {n : ℕ} (hn : n ≠ 0) {x : Per.Acris l} (h : (n : Per.Acris l) * x = 0) : x = 0 := by
  have h0 : ((n : ℕ) : ℤ_[l]) ≠ 0 := by exact_mod_cast hn
  have h1 := congrArg (algebraMap ℤ_[l] (Per.Acris l)) (PadicInt.unitCoeff_spec h0)
  rw [map_natCast, map_mul, map_pow, map_natCast] at h1
  rw [h1, mul_assoc, ((PadicInt.unitCoeff h0).isUnit.map _).mul_right_eq_zero] at h
  generalize ((n : ℕ) : ℤ_[l]).valuation = k at h
  induction k generalizing x with
  | zero => simpa using h
  | succ k ih =>
    exact (GlobalTheory.MemLoc.acris_torsionFree_complete l).1 x (ih (by rw [← mul_assoc, ← pow_succ, h]))

theorem exists_dpow {x : Ainf l} (hx : Per.θ l x = 0) (n : ℕ) :
    ∃ y : Per.Acris l, (n.factorial : Per.Acris l) * y = ainfToAcris l x ^ n := by
  obtain ⟨g, hg, h⟩ := GlobalTheory.MemLoc.exists_dividedPower_mem_Acris0 l x hx n
  have h1 : (n.factorial : Per.Acris0 l) * ⟨g, hg⟩ = algebraMap (Per.Ainf l) (Per.Acris0 l) x ^ n :=
    Subtype.ext (by simpa using h)
  have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) h1
  rw [map_mul, map_natCast, map_pow, ← GlobalTheory.RingIface.tower] at h2
  exact ⟨_, h2⟩

def dpow (x : Ainf l) (hx : Per.θ l x = 0) (n : ℕ) : Per.Acris l := (exists_dpow hx n).choose

theorem factorial_mul_dpow (x : Ainf l) (hx : Per.θ l x = 0) (n : ℕ) :
    (n.factorial : Per.Acris l) * dpow x hx n = ainfToAcris l x ^ n := (exists_dpow hx n).choose_spec

theorem eq_dpow {x : Ainf l} (hx : Per.θ l x = 0) {n : ℕ} {y : Per.Acris l}
    (h : (n.factorial : Per.Acris l) * y = ainfToAcris l x ^ n) : y = dpow x hx n :=
  sub_eq_zero.1 (acris_nat_cancel n.factorial_ne_zero (by rw [mul_sub, h, factorial_mul_dpow, sub_self]))

theorem dpow_zero (x : Ainf l) (hx : Per.θ l x = 0) : dpow x hx 0 = 1 := (eq_dpow hx (by simp)).symm

theorem dpow_one (x : Ainf l) (hx : Per.θ l x = 0) : dpow x hx 1 = ainfToAcris l x :=
  (eq_dpow hx (by simp)).symm

theorem PiSys.exists_dpow_teich {e : ℕ} (ϖ : PiSys l e) (q : ℕ) :
    ∃ d : Per.Acris l, (q.factorial : Per.Acris l) * d = ainfToAcris l ϖ.teich ^ (e * q) := by
  have hE : Per.θ l (ϖ.teich ^ e + l) = 0 := by
    rw [map_add, map_pow, ϖ.theta_teich, ϖ.seqO_zero, map_natCast, neg_add_cancel]
  choose c hc using GlobalTheory.RingBasics.exists_pow_div_factorial l
  have hc' : ∀ n : ℕ, (n.factorial : Per.Acris l) * algebraMap ℤ_[l] _ (c n) = (l : Per.Acris l) ^ n :=
    fun n => by simpa only [map_mul, map_natCast, map_pow] using congrArg (algebraMap ℤ_[l] (Per.Acris l)) (hc n)
  have h1 : ainfToAcris l ϖ.teich ^ e = ainfToAcris l (ϖ.teich ^ e + l) + -(l : Per.Acris l) := by
    rw [map_add, map_pow, map_natCast, add_neg_cancel_right]
  refine ⟨∑ k ∈ Finset.range (q + 1), dpow _ hE k * ((-1) ^ (q - k) * algebraMap ℤ_[l] _ (c (q - k))), ?_⟩
  rw [pow_mul, h1, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Nat.choose_mul_factorial_mul_factorial (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)),
    ← factorial_mul_dpow _ hE, neg_pow (l : Per.Acris l), ← hc']
  push_cast
  ring

section Coeff

variable {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O)

variable (l O) in

abbrev OCr : Type := O ⊗[ℤ_[l]] Per.Acris l

variable (l O) in

abbrev OB : Type := O ⊗[ℤ_[l]] Per.Bcris l

variable (l O) in

def toOCr : OA l O →ₐ[O] OCr l O := Algebra.TensorProduct.map (AlgHom.id _ _) (ainfToAcris l)

variable (l O) in

def toOB : OCr l O →ₐ[O] OB l O := Algebra.TensorProduct.map (AlgHom.id _ _) (acrisToBcris l)

variable (l O) in

def frobOCr : OCr l O →ₐ[O] OCr l O := Algebra.TensorProduct.map (AlgHom.id _ _) (frobC l)

variable (O) in

def galOCr (g : GQ l) : OCr l O →ₐ[O] OCr l O := Algebra.TensorProduct.map (AlgHom.id _ _) (galC g)

variable (l O) in

def frobOB : OB l O →ₐ[O] OB l O := Algebra.TensorProduct.map (AlgHom.id _ _) (frobB l)

variable (O) in

def galOB (g : GQ l) : OB l O →ₐ[O] OB l O := Algebra.TensorProduct.map (AlgHom.id _ _) (galB g)

theorem toOCr_tmul (o : O) (w : Ainf l) : toOCr l O (o ⊗ₜ w) = o ⊗ₜ ainfToAcris l w := rfl

theorem frobOCr_toOCr (x : OA l O) : frobOCr l O (toOCr l O x) = toOCr l O (frobOA l O x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.Acris l => o ⊗ₜ[ℤ_[l]] y) (((GlobalTheory.CrisMaps.phiA_extends l).alg w).trans
      (congrArg (algebraMap (Per.Ainf l) (Per.Acris l)) (phiA_eq_frobA_pt w)))
  | add x y hx hy => simp only [map_add, hx, hy]

theorem galOCr_toOCr (g : GQ l) (x : OA l O) : galOCr O g (toOCr l O x) = toOCr l O (galOA O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.Acris l => o ⊗ₜ[ℤ_[l]] y) ((GlobalTheory.CrisMaps.sigA_extends g).alg w)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem frobOB_toOB (x : OCr l O) : frobOB l O (toOB l O x) = toOB l O (frobOCr l O x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.Bcris l => o ⊗ₜ[ℤ_[l]] y)
      ((GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 w)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem galOB_toOB (g : GQ l) (x : OCr l O) : galOB O g (toOB l O x) = toOB l O (galOCr O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.Bcris l => o ⊗ₜ[ℤ_[l]] y)
      ((GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 g w)
  | add x y hx hy => simp only [map_add, hx, hy]

def constC : (ZMod a → O) →ₐ[O] OCr l O := (toOCr l O).comp (constA t)

def constB : (ZMod a → O) →ₐ[O] OB l O := (toOB l O).comp (constC t)

theorem isUnit_l_OB : IsUnit (l : OB l O) := by
  simpa only [map_natCast] using (GlobalTheory.MemLoc.isUnit_l_Bcris l).map
    (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem complete_OCr : IsAdicComplete (Ideal.span {(l : OCr l O)}) (OCr l O) := by
  have h := GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis ℤ_[l] O) (l : Per.Acris l)
    (h := (GlobalTheory.MemLoc.acris_torsionFree_complete l).2)
  rwa [show ((1 : O) ⊗ₜ[ℤ_[l]] (l : Per.Acris l)) = (l : OCr l O) from
    map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) l] at h

theorem sep_OCr (x : OCr l O) (h : ∀ n, (l : OCr l O) ^ n ∣ x) : x = 0 :=
  have := complete_OCr (l := l) (O := O)
  GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (h n)

theorem nat_cancel_OCr {n : ℕ} (hn : n ≠ 0) {x : OCr l O} (h : (n : OCr l O) * x = 0) : x = 0 := by
  refine GlobalTheory.Decompl.ext_crd (Module.Free.chooseBasis ℤ_[l] O) fun i => ?_
  rw [map_zero]
  refine acris_nat_cancel hn ?_
  rw [← GlobalTheory.Decompl.crd_natCast_mul, h, map_zero]

namespace PiSys

variable {e : ℕ} [NeZero e] (O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e)

theorem exists_iS : ∃ g : S O K e →ₐ[O] OCr l O,
    ∀ x : A O K, g ⟨x, A_le_S l e x.2⟩ = toOCr l O (ϖ.iA O K x) := by
  have := complete_OCr (l := l) (O := O)
  refine exists_extend_S l e (fun _ => nat_cancel_OCr hl.out.ne_zero) ((toOCr l O).comp (ϖ.iA O K)) fun q => ?_
  obtain ⟨d, hd⟩ := ϖ.exists_dpow_teich q
  refine ⟨1 ⊗ₜ d, ?_⟩
  have h := congrArg (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) hd
  rw [map_mul, map_natCast, map_pow] at h
  rw [AlgHom.comp_apply, iA_u]
  exact h

def iS : S O K e →ₐ[O] OCr l O := (ϖ.exists_iS O K).choose

theorem iS_of_mem {f : K⟦X⟧} (h : f ∈ A O K) (h' : f ∈ S O K e) :
    ϖ.iS O K ⟨f, h'⟩ = toOCr l O (ϖ.iA O K ⟨f, h⟩) := (ϖ.exists_iS O K).choose_spec ⟨f, h⟩

theorem iS_u : ϖ.iS O K (uIn _) = toOCr l O (ϖ.teichR O) :=
  (ϖ.iS_of_mem O K HasU.X_mem _).trans (congrArg _ (ϖ.iA_u O K))

theorem iS_frob (f : S O K e) : ϖ.iS O K ⟨frob K l f, frob_mem_S l f.2⟩ = frobOCr l O (ϖ.iS O K f) := by
  refine RingHom.congr_fun (ringHom_ext_S l e (fun _ => nat_cancel_OCr hl.out.ne_zero) sep_OCr
    ((ϖ.iS O K).toRingHom.comp (((frob K l).toRingHom.restrict (S O K e) (S O K e) fun _ h => frob_mem_S l h)))
    ((frobOCr l O).toRingHom.comp (ϖ.iS O K).toRingHom) fun x => ?_) f
  change ϖ.iS O K ⟨frob K l x, _⟩ = frobOCr l O (ϖ.iS O K ⟨x, _⟩)
  rw [ϖ.iS_of_mem O K (frob_mem_A l x.2), ϖ.iS_of_mem O K x.2, iA_frob, frobOCr_toOCr]

def iSl : invL l (S O K e) →ₐ[O] OB l O where
  toRingHom := IsLocalization.Away.lift (l : S O K e) (g := ((toOB l O).comp (ϖ.iS O K)).toRingHom)
    (by rw [map_natCast]; exact isUnit_l_OB)
  commutes' o := (IsLocalization.Away.lift_eq (S := invL l (S O K e)) (l : S O K e) _
    (algebraMap _ _ o)).trans (((toOB l O).comp (ϖ.iS O K)).commutes o)

theorem iSl_of_mem {f : K⟦X⟧} (h : f ∈ S O K e) (h' : f ∈ invL l (S O K e)) :
    ϖ.iSl O K ⟨f, h'⟩ = toOB l O (ϖ.iS O K ⟨f, h⟩) :=
  IsLocalization.Away.lift_eq (S := invL l (S O K e)) (l : S O K e)
    (g := ((toOB l O).comp (ϖ.iS O K)).toRingHom) (by rw [map_natCast]; exact isUnit_l_OB) ⟨f, h⟩

variable {O}

def iC : (ZMod a → S O K e) →ₐ[O] OCr l O := glue (constC t) (ϖ.iS O K)

def iB : (ZMod a → invL l (S O K e)) →ₐ[O] OB l O := glue (constB t) (ϖ.iSl O K)

theorem iC_of_mem (f : ZMod a → A O K) :
    ϖ.iC t K (fun τ => ⟨f τ, A_le_S l e (f τ).2⟩) = toOCr l O (ϖ.iTot t K f) :=
  (map_glue (toOCr l O).toRingHom 0 (fun τ => by rw [add_zero]; rfl) fun τ => by
    rw [sub_zero]; exact (ϖ.iS_of_mem O K _ _).symm).symm

theorem iB_of_mem (f : ZMod a → S O K e) :
    ϖ.iB t K (fun τ => ⟨f τ, le_away _ _ (f τ).2⟩) = toOB l O (ϖ.iC t K f) :=
  (map_glue (toOB l O).toRingHom 0 (fun τ => by rw [add_zero]; rfl) fun τ => by
    rw [sub_zero]; exact (ϖ.iSl_of_mem O K _ _).symm).symm

variable (O a) in

def muDiv (g : ↥(GK (ϖ.field a))) (n : ℕ) : OCr l O :=
  1 ⊗ₜ dpow (ϖ.mu g) (ϖ.theta_mu (ϖ.gal_pi a g)) n

variable (O) in

theorem galOCr_iS_monomial (g : GQ l) (n : ℕ) (c : K) (h : monomial n c ∈ S O K e) :
    galOCr O g (ϖ.iS O K ⟨_, h⟩) = (1 ⊗ₜ ainfToAcris l (ϖ.mu g) + 1) ^ n * ϖ.iS O K ⟨_, h⟩ := by
  obtain ⟨k, b, hb⟩ := exists_pow_mul_mem (O := O) l c
  have h1 : ((l ^ k : ℕ) : S O K e) * ⟨_, h⟩ = b • uIn _ ^ n := Subtype.ext (by
    change (((l ^ k : ℕ) : S O K e) : K⟦X⟧) * monomial n c = b • (X : K⟦X⟧) ^ n
    rw [Algebra.smul_def, algebraMap_eq_C, ← hb, monomial_eq_C_mul_X_pow]
    simp [mul_assoc])
  have h2 := congrArg (ϖ.iS O K) h1
  rw [map_mul, map_natCast, map_smul, map_pow, iS_u] at h2
  have h3 := congrArg (galOCr O g) h2
  rw [map_mul, map_natCast, map_smul, map_pow, galOCr_toOCr, galOA_teichR, map_mul, map_add, map_one,
    toOCr_tmul, mul_pow, add_comm] at h3
  refine sub_eq_zero.1 (nat_cancel_OCr (pow_pos hl.out.pos k).ne' ?_)
  rw [mul_sub, h3, mul_left_comm, h2, mul_smul_comm, sub_self]

variable (O a) in
omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in

theorem sum_muDiv_descFactorial (g : ↥(GK (ϖ.field a))) {n M : ℕ} (h : n < M) :
    ∑ i ∈ Finset.range M, ϖ.muDiv a O g i * (n.descFactorial i : OCr l O) =
      (1 ⊗ₜ ainfToAcris l (ϖ.mu g) + 1) ^ n := by
  rw [add_pow, ← Finset.sum_subset (Finset.range_mono h) fun i _ hi => by
    rw [Nat.descFactorial_of_lt (by simpa using hi), Nat.cast_zero, mul_zero]]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := congrArg (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O)
    (factorial_mul_dpow (ϖ.mu g) (ϖ.theta_mu (ϖ.gal_pi a g)) i)
  rw [map_mul, map_natCast, map_pow] at h1
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc, mul_comm (ϖ.muDiv a O g i),
    one_pow, mul_one]
  exact congrArg (· * (n.choose i : OCr l O)) h1

variable (O a) in

theorem taylor_S (g : ↥(GK (ϖ.field a))) (f : S O K e) (r : ℕ) : ∃ M₀, ∀ M ≥ M₀, (l : OCr l O) ^ r ∣
    galOCr O g (ϖ.iS O K f) -
      ∑ i ∈ Finset.range M, ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i f, descN_mem_S e i f.2⟩ := by
  obtain ⟨N, hN⟩ := exists_sum_monomial_add l e f.2 r
  obtain ⟨h, hh, hf⟩ := hN N le_rfl
  refine ⟨N, fun M hM => ?_⟩
  let m : ℕ → S O K e := fun n => ⟨monomial n (coeff n (f : K⟦X⟧)), monomial_mem_S (f.2.1 n)⟩
  have h1 : f = ∑ n ∈ Finset.range N, m n + (l : S O K e) ^ r * ⟨h, hh⟩ := Subtype.ext (by simpa using hf)
  have h2 : ∀ i, (⟨descN K i f, descN_mem_S e i f.2⟩ : S O K e) =
      ∑ n ∈ Finset.range N, (n.descFactorial i : S O K e) * m n +
        (l : S O K e) ^ r * ⟨descN K i h, descN_mem_S e i hh⟩ := fun i => Subtype.ext (by
    have h3 : (l : K⟦X⟧) ^ r = C ((l : K) ^ r) := by simp
    have h4 : ∀ n : ℕ, (n : K⟦X⟧) = C (n : K) := fun n => by simp
    change descN K i f = _
    conv_lhs => rw [hf, map_add, map_sum, h3, ← smul_eq_C_mul, map_smul, smul_eq_C_mul, ← h3]
    simp only [AddMemClass.coe_add, MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast,
      AddSubmonoidClass.coe_finset_sum, m]
    congr 1
    refine Finset.sum_congr rfl fun n _ => PowerSeries.ext fun k => ?_
    rw [coeff_descN, h4, coeff_C_mul, coeff_monomial]
    split_ifs with hk
    · rw [hk]
    · simp)
  refine ⟨galOCr O g (ϖ.iS O K ⟨h, hh⟩) -
    ∑ i ∈ Finset.range M, ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i h, descN_mem_S e i hh⟩, ?_⟩
  have h5 : galOCr O g (ϖ.iS O K (∑ n ∈ Finset.range N, m n)) = ∑ i ∈ Finset.range M, ϖ.muDiv a O g i *
      ϖ.iS O K (∑ n ∈ Finset.range N, (n.descFactorial i : S O K e) * m n) := by
    simp only [map_sum, map_mul, map_natCast, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [galOCr_iS_monomial, ← ϖ.sum_muDiv_descFactorial a O g ((Finset.mem_range.1 hn).trans_le hM),
      Finset.sum_mul]
    simp only [mul_assoc, m]
  simp only [h2]
  conv_lhs => rw [h1]
  simp only [map_add, h5, mul_add, Finset.sum_add_distrib, map_mul, map_pow, map_natCast, mul_sub,
    Finset.mul_sum, mul_left_comm ((l : OCr l O) ^ r)]
  ring

end PiSys

end Coeff

end GlobalTheory.BKReal
