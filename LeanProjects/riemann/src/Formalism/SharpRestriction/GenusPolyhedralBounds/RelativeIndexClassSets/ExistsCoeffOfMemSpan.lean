import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IntegralFormsEqSpan
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HasseJidPow

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

section Abstract

open MvPolynomial

variable {k K L : Type*} [CommRing k] [Field K] [CommRing L] [Algebra k L] [Algebra K L]
  {n δ : ℕ} (y : Fin n → L) (θ : Fin δ → L) (J : ℕ → Submodule K L) (Δ : Fin n → Derivation k L L)

theorem ind_mono (hy : ∀ l l', Δ l (y l') = if l = l' then 1 else 0) (l : Fin n) (m : Fin n →₀ ℕ) :
    Δ l (aeval y (monomial m (1 : K))) = aeval y (pderiv l (monomial m (1 : K))) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [show monomial (f + g) (1 : K) = monomial f 1 * monomial g 1 by rw [monomial_mul, one_mul], map_mul,
      Derivation.leibniz, Derivation.leibniz, hf, hg, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul]
  | single i a =>
    rw [← X_pow_eq_monomial, map_pow, aeval_X, Derivation.leibniz_pow, Derivation.leibniz_pow, hy, pderiv_X,
      map_nsmul, smul_eq_mul, smul_eq_mul, map_mul, map_pow, aeval_X]
    by_cases h : l = i
    · subst h; simp
    · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h), map_zero]

theorem aeval_monomial_eq_smul (m : Fin n →₀ ℕ) (c : K) :
    aeval y (monomial m c) = c • aeval y (monomial m (1 : K)) := by
  rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]

theorem ind_hom_mem (hY : ∀ (m : Fin n →₀ ℕ) i, aeval y (monomial m (1 : K)) * θ i ∈ J m.degree) {a : ℕ}
    {p : MvPolynomial (Fin n) K} (hp : p.IsHomogeneous a) (i : Fin δ) : aeval y p * θ i ∈ J a := by
  rw [← support_sum_monomial_coeff p, map_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hd : m.degree = a := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero h)
  rw [aeval_monomial_eq_smul, smul_mul_assoc, ← hd]
  exact Submodule.smul_mem _ _ (hY m i)

theorem ind_der_mem (hy : ∀ l l', Δ l (y l') = if l = l' then 1 else 0) (hθ : ∀ l i, Δ l (θ i) = 0)
    (hK : ∀ l (c : K), ∃ c' : K, Δ l (algebraMap K L c) = algebraMap K L c')
    (hY : ∀ (m : Fin n →₀ ℕ) i, aeval y (monomial m (1 : K)) * θ i ∈ J m.degree) {a : ℕ}
    {p : MvPolynomial (Fin n) K} (hp : p.IsHomogeneous a) (l : Fin n) (i : Fin δ) :
    Δ l (aeval y p * θ i) - aeval y (pderiv l p) * θ i ∈ J a := by
  rw [← support_sum_monomial_coeff p]
  simp only [map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hd : m.degree = a := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero h)
  obtain ⟨c', hc'⟩ := hK l (coeff m p)
  have e1 : Δ l (aeval y (monomial m (coeff m p)) * θ i) =
      c' • (aeval y (monomial m (1 : K)) * θ i) + aeval y (pderiv l (monomial m (coeff m p))) * θ i := by
    have e2 : pderiv l (monomial m (coeff m p)) = coeff m p • pderiv l (monomial m (1 : K)) := by
      rw [← Derivation.map_smul, smul_monomial, smul_eq_mul, mul_one]
    rw [e2, map_smul, aeval_monomial_eq_smul, Algebra.smul_def, Derivation.leibniz, hθ, smul_zero, zero_add,
      Derivation.leibniz, hc', ind_mono y Δ hy]
    simp only [smul_eq_mul, Algebra.smul_def]
    ring
  rw [e1, add_sub_cancel_right, ← hd]
  exact Submodule.smul_mem _ _ (hY m i)

variable [CharZero K]

theorem ind_claim (hy : ∀ l l', Δ l (y l') = if l = l' then 1 else 0) (hθ : ∀ l i, Δ l (θ i) = 0)
    (hK : ∀ l (c : K), ∃ c' : K, Δ l (algebraMap K L c) = algebraMap K L c')
    (hJ : ∀ l a x, x ∈ J (a + 1) → Δ l x ∈ J a) (hanti : ∀ a, J (a + 1) ≤ J a)
    (hY : ∀ (m : Fin n →₀ ℕ) i, aeval y (monomial m (1 : K)) * θ i ∈ J m.degree)
    (hbase : ∀ c : Fin δ → K, ∑ i, c i • θ i ∈ J 1 → c = 0) (a : ℕ) :
    ∀ c : Fin δ → MvPolynomial (Fin n) K, (∀ i, ∀ m ∈ (c i).support, m.degree < a) →
      ∑ i, aeval y (c i) * θ i ∈ J a → c = 0 := by
  induction a with
  | zero =>
    intro c hc _
    funext i
    rw [Pi.zero_apply, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
    intro m hm
    exact absurd (hc i m hm) (Nat.not_lt_zero _)
  | succ a ih =>
    intro c hc hmem
    rcases Nat.eq_zero_or_pos a with rfl | ha
    ·
      have hC : ∀ i, c i = C (coeff 0 (c i)) := by
        intro i
        ext m
        rw [coeff_C]
        split_ifs with h
        · rw [← h]
        · by_contra h'
          have := hc i m (MvPolynomial.mem_support_iff.mpr h')
          exact h ((Finsupp.degree_eq_zero_iff m).mp (by omega)).symm
      have h0 := hbase (fun i => coeff 0 (c i)) (by
        have e : ∑ i, aeval y (c i) * θ i = ∑ i, coeff 0 (c i) • θ i :=
          Finset.sum_congr rfl fun i _ => by
            conv_lhs => rw [hC i]
            rw [aeval_C, Algebra.smul_def]
        rw [← e]; exact hmem)
      funext i
      have h0i : coeff 0 (c i) = 0 := congrFun h0 i
      rw [hC i, h0i, map_zero]
      rfl
    ·
      have hlow : (fun i => c i - homogeneousComponent a (c i)) = 0 := by
        apply ih
        · intro i m hm
          rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hm
          by_cases hd : m.degree = a
          · rw [if_pos hd, sub_self] at hm; exact absurd rfl hm
          · rw [if_neg hd, sub_zero] at hm
            have := hc i m (MvPolynomial.mem_support_iff.mpr hm)
            omega
        · have e : ∑ i, aeval y (c i - homogeneousComponent a (c i)) * θ i =
              ∑ i, aeval y (c i) * θ i - ∑ i, aeval y (homogeneousComponent a (c i)) * θ i := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by rw [map_sub, sub_mul]
          rw [e]
          exact Submodule.sub_mem _ (hanti a hmem)
            (Submodule.sum_mem _ fun i _ => ind_hom_mem y θ J hY (homogeneousComponent_isHomogeneous a (c i)) i)
      have hhom : ∀ i, (c i).IsHomogeneous a := by
        intro i
        have := congrFun hlow i
        rw [Pi.zero_apply, sub_eq_zero] at this
        rw [this]; exact homogeneousComponent_isHomogeneous a (c i)

      have hpd : ∀ l, (fun i => pderiv l (c i)) = 0 := by
        intro l
        apply ih
        · intro i m hm
          have hd : m.degree = a - 1 := by
            by_contra h
            exact (MvPolynomial.mem_support_iff.mp hm) ((hhom i).pderiv.coeff_eq_zero h)
          omega
        · have h1 := hJ l a _ hmem
          rw [map_sum] at h1
          have h2 : ∑ i, (Δ l (aeval y (c i) * θ i) - aeval y (pderiv l (c i)) * θ i) ∈ J a :=
            Submodule.sum_mem _ fun i _ => ind_der_mem y θ J Δ hy hθ hK hY (hhom i) l i
          rw [Finset.sum_sub_distrib] at h2
          have := Submodule.sub_mem _ h1 h2
          rwa [sub_sub_cancel] at this
      funext i
      have hE := (hhom i).sum_X_mul_pderiv
      have h0 : ∑ l, X l * pderiv l (c i) = 0 :=
        Finset.sum_eq_zero fun l _ => by rw [congrFun (hpd l) i, Pi.zero_apply, mul_zero]
      rw [h0] at hE
      rw [Pi.zero_apply]
      exact (smul_eq_zero.mp hE.symm).resolve_left (by omega)

end Abstract

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem der_sum_apply {k L ι : Type*} [CommRing k] [CommRing L] [Algebra k L] (s : Finset ι)
    (f : ι → Derivation k L L) (x : L) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

section Concrete

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

@[instance_reducible] def LwAlgKl : Algebra (X.Kl la) (Lw X la w) := inferInstanceAs (Algebra (X.Kl la) (Localization.Away (sec X la w 0)))

attribute [local instance] LwAlgKl

def pdLw (p : Idx D j N) : Derivation (X.Kl la) (Lw X la w) (Lw X la w) := pdLc X la w p

theorem pdLw_algebraMap (p : Idx D j N) (x : Rp X la N) :
    pdLw X la w p (algebraMap (Rp X la N) (Lw X la w) x) = algebraMap (Rp X la N) (Lw X la w) (pdRp X la N p x) :=
  pdLc_algebraMap X la w p x

theorem pdLw_algebraMap_Kp (p : Idx D j N) (c : Kp X la N) :
    pdLw X la w p (algebraMap (Kp X la N) (Lw X la w) c) = algebraMap (Kp X la N) (Lw X la w) (pdKp X la N p c) := by
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), pdLw_algebraMap, pdRp_algebraMap,
    ← IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w)]

theorem pdLw_mem (p : Idx D j N) (u : WeightFamilies.Wt D j) (a : ℕ) {x : Lw X la w} (hx : x ∈ JHfr X la w u (a + 1)) :
    pdLw X la w p x ∈ JHfr X la w u a := by
  have h := hasse_jid_power X la w u (Finsupp.single p 1) (a + 1) x hx
  rw [Finsupp.sum_single_index rfl, Nat.add_sub_cancel] at h
  exact h

theorem pdLw_w0inv (p : Idx D j N) (hp : p.1 ≠ 0) : pdLw X la w p (w0inv X la w) = 0 := by
  have h := congrArg (pdLw X la w p) (section_mul_inverse_eq_one X la w)
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, pdLw_algebraMap, pdRp_sec, if_neg hp, map_zero, smul_zero,
    add_zero, smul_eq_mul] at h
  calc pdLw X la w p (w0inv X la w)
      = (algebraMap (Rp X la N) (Lw X la w) (sec X la w 0) * w0inv X la w) * pdLw X la w p (w0inv X la w) := by
        rw [section_mul_inverse_eq_one, one_mul]
    _ = w0inv X la w * (algebraMap (Rp X la N) (Lw X la w) (sec X la w 0) * pdLw X la w p (w0inv X la w)) := by ring
    _ = 0 := by rw [h, mul_zero]

def t0 (κ : Fin N) : Kp X la N := algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, κ))

def dSec (l : Fin (WeightFamilies.dimY D j)) : Derivation (X.Kl la) (Lw X la w) (Lw X la w) :=
  ∑ κ, algebraMap (Kp X la N) (Lw X la w) (t0 X la κ) • pdLw X la w (l.succ, κ)

theorem dSec_apply (l : Fin (WeightFamilies.dimY D j)) (x : Lw X la w) :
    dSec X la w l x = ∑ κ, t0 X la κ • pdLw X la w (l.succ, κ) x := by
  unfold dSec
  rw [der_sum_apply]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Derivation.smul_apply, smul_eq_mul, Algebra.smul_def]

def ySec (l : Fin (WeightFamilies.dimY D j)) : Lw X la w := (sfr X la w l.succ : Lw X la w)

theorem dSec_ySec (l l' : Fin (WeightFamilies.dimY D j)) : dSec X la w l (ySec X la w l') = if l = l' then 1 else 0 := by
  have h1 : ∀ κ, pdLw X la w (l.succ, κ) (ySec X la w l') =
      if l = l' then algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wL (w κ))) * w0inv X la w else 0 := by
    intro κ
    unfold ySec
    rw [coe_sfr, frac_apply, pow_one, Derivation.leibniz, pdLw_w0inv X la w _ (Fin.succ_ne_zero l), smul_zero, zero_add,
      pdLw_algebraMap, pdRp_sec, smul_eq_mul]
    by_cases h : l = l'
    · rw [if_pos h, if_pos (by rw [h]), mul_comm]
    · rw [if_neg h, if_neg (fun e => h (Fin.succ_injective _ e)), map_zero, mul_zero]
  rw [dSec_apply]
  simp only [h1]
  by_cases h : l = l'
  · simp only [if_pos h]
    rw [← section_mul_inverse_eq_one X la w]
    unfold sec
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [← smul_mul_assoc]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w)]
    rfl
  · simp only [if_neg h, smul_zero, Finset.sum_const_zero]

theorem dSec_emb (l : Fin (WeightFamilies.dimY D j)) (F : X.Forms) :
    dSec X la w l (algebraMap (Rp X la N) (Lw X la w) (emb X la N F)) = 0 := by
  rw [dSec_apply]
  refine Finset.sum_eq_zero fun κ _ => ?_
  rw [pdLw_algebraMap, pdRp_emb, map_zero, smul_zero]

theorem dSec_algebraMap_Kp (l : Fin (WeightFamilies.dimY D j)) (c : Kp X la N) :
    ∃ c' : Kp X la N, dSec X la w l (algebraMap (Kp X la N) (Lw X la w) c) = algebraMap (Kp X la N) (Lw X la w) c' := by
  refine ⟨∑ κ, t0 X la κ * pdKp X la N (l.succ, κ) c, ?_⟩
  rw [dSec_apply, map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [pdLw_algebraMap_Kp, Algebra.smul_def, map_mul]

theorem dSec_mem (l : Fin (WeightFamilies.dimY D j)) (u : WeightFamilies.Wt D j) (a : ℕ) (x : Lw X la w) (hx : x ∈ JHfr X la w u (a + 1)) :
    dSec X la w l x ∈ JHfr X la w u a := by
  rw [dSec_apply]
  exact Submodule.sum_mem _ fun κ _ => Submodule.smul_mem _ _ (pdLw_mem X la w _ u a hx)

theorem JHfr_succ_le (u : WeightFamilies.Wt D j) (a : ℕ) : JHfr X la w u (a + 1) ≤ JHfr X la w u a := by
  intro x hx
  have h1 : x ∈ JHs X la w u (a + 1) := hx
  rw [← Jid_pow_smul_HK] at h1
  have h2 : x ∈ Jid X la w ^ a • HK X la w u := Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ a)) le_rfl h1
  rw [Jid_pow_smul_HK] at h2
  exact h2

open MvPolynomial in
theorem aeval_ySec_monomial (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) :
    aeval (ySec X la w) (monomial m (1 : Kp X la N)) = frac X la w m.degree (secPow X la w m) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.degree_eq_sum,
    ← coe_prod_sfr]
  show _ = (Frac0 X la w).val (∏ i, sfr X la w i.succ ^ m i)
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow]
  rfl

open MvPolynomial in
theorem ySec_monomial_mul_mem (u : WeightFamilies.Wt D j) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) (F : B.Cusp j u) :
    aeval (ySec X la w) (monomial m (1 : Kp X la N)) * algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc u F)) ∈
      JHfr X la w u m.degree := by
  rw [aeval_ySec_monomial, ← frac_zero, frac_mul, mem_JHfr]
  refine ⟨0, _, secPow_mul_mem_Mon X la w (Finsupp.degree_eq_sum m).symm ?_, by rw [add_comm]⟩
  rw [addL_zero]
  exact emb_mem_Vw X la N u F

end Concrete

section Final

open MvPolynomial

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
  (wF : WeightFamilies.Wt D j) (T : ℕ)

theorem Kp_charZero' : CharZero (Kp X la N) :=
  have := Kl_charZero X la
  charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective

def gN (θ : B.Cusp j wF) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) : Rp X la N :=
  secPow X la w m * sec X la w 0 ^ (T - m.degree) * emb X la N (X.inc wF θ)

def phiN (θ : B.Cusp j wF) : MvPolynomial (Fin (WeightFamilies.dimY D j)) (Kp X la N) →ₗ[Kp X la N] Rp X la N :=
  (basisMonomials (Fin (WeightFamilies.dimY D j)) (Kp X la N)).constr (Kp X la N) (gN X la w wF T θ)

theorem phiN_monomial (θ : B.Cusp j wF) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) (c : Kp X la N) :
    phiN X la w wF T θ (monomial m c) = c • gN X la w wF T θ m := by
  have e : monomial m c = c • basisMonomials (Fin (WeightFamilies.dimY D j)) (Kp X la N) m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  unfold phiN
  rw [e, map_smul, Module.Basis.constr_basis]

theorem frac_gN (θ : B.Cusp j wF) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) (hm : m.degree ≤ T) :
    frac X la w T (gN X la w wF T θ m) = aeval (ySec X la w) (monomial m (1 : Kp X la N)) *
      algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wF θ)) := by
  rw [aeval_ySec_monomial, ← frac_zero, frac_mul, ← frac_pow_mul X la w (m.degree + 0) (T - m.degree)]
  unfold gN
  rw [show m.degree + 0 + (T - m.degree) = T by omega]
  congr 1
  ring

theorem frac_phiN (θ : B.Cusp j wF) (p : MvPolynomial (Fin (WeightFamilies.dimY D j)) (Kp X la N))
    (hp : ∀ m ∈ p.support, m.degree ≤ T) :
    frac X la w T (phiN X la w wF T θ p) =
      aeval (ySec X la w) p * algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wF θ)) := by
  have key : ∀ (s : Finset (Fin (WeightFamilies.dimY D j) →₀ ℕ)) (f : (Fin (WeightFamilies.dimY D j) →₀ ℕ) → Kp X la N),
      (∀ m ∈ s, m.degree ≤ T) → frac X la w T (phiN X la w wF T θ (∑ m ∈ s, monomial m (f m))) =
        aeval (ySec X la w) (∑ m ∈ s, monomial m (f m)) *
          algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wF θ)) := by
    intro s f hs
    simp only [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [phiN_monomial, map_smul, frac_gN X la w wF T θ m (hs m hm), aeval_monomial_eq_smul (ySec X la w) m (f m),
      smul_mul_assoc]
  have := key p.support (fun m => coeff m p) hp
  rwa [support_sum_monomial_coeff] at this

end Final

section Main

open MvPolynomial

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO))

theorem exists_coeff_of_mem_span {x : ↥(Vw X la G.N (addL wF wL T))}
    (hx : x ∈ Submodule.span (Kp X la G.N) (sectionMonomialGenerators G la)) :
    ∃ c : Fin G.del → MvPolynomial (Fin (WeightFamilies.dimY D j)) (Kp X la G.N),
      (∀ i, ∀ m ∈ (c i).support, m.degree < a0 D j T) ∧
        (x : Rp X la G.N) = ∑ i, phiN X la G.w wF T (G.th' i) (c i) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨al, i, hal, hx⟩ := hx
    refine ⟨fun i' => if i' = i then monomial (Finsupp.equivFunOnFinite.symm al) 1 else 0, ?_, ?_⟩
    · intro i' m hm
      dsimp only at hm
      by_cases h : i' = i
      · rw [if_pos h] at hm
        have := Finset.mem_singleton.mp (support_monomial_subset hm)
        rw [this, Finsupp.degree_eq_sum]
        exact hal
      · rw [if_neg h, support_zero] at hm
        exact absurd hm (Finset.notMem_empty _)
    · rw [Finset.sum_eq_single i]
      · dsimp only
        rw [if_pos rfl, phiN_monomial, one_smul, hx]
        unfold gN
        rw [Finsupp.degree_eq_sum]
        rfl
      · intro i' _ h
        dsimp only
        rw [if_neg h, map_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  | zero => exact ⟨0, fun i m hm => by simp at hm, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hxc⟩ := hx
    obtain ⟨c', hc', hyc⟩ := hy
    refine ⟨c + c', fun i m hm => ?_, ?_⟩
    · rcases Finset.mem_union.mp (support_add hm) with h | h
      · exact hc i m h
      · exact hc' i m h
    · rw [Submodule.coe_add, hxc, hyc, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, map_add]
  | smul a x _ hx =>
    obtain ⟨c, hc, hxc⟩ := hx
    refine ⟨a • c, fun i m hm => hc i m (support_smul hm), ?_⟩
    rw [Submodule.coe_smul, hxc, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, map_smul]

attribute [local instance] LwAlgKl

theorem in64 (hB : InBasis G la) : ∀ x ∈ Submodule.span (Kp X la G.N) (sectionMonomialGenerators G la),
    rhoK X la G.w wF (a0 D j T) T x = 0 → x = 0 := by
  intro x hx h0
  have := Kp_charZero' X la (N := G.N)
  obtain ⟨c, hc, hxc⟩ := exists_coeff_of_mem_span G la hx

  have hbase : ∀ b : Fin G.del → Kp X la G.N,
      ∑ i, b i • algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) ∈ JHfr X la G.w wF 1 →
        b = 0 := by
    intro b hb
    have hlin : ∑ i, b i • tL G la i = 0 := by
      have e : ∑ i, b i • tL G la i = rho0 X la G.w wF
          (∑ i, b i • (⟨emb X la G.N (X.inc wF (G.th' i)), emb_mem_Vw X la G.N wF (G.th' i)⟩ : ↥(Vw X la G.N wF))) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
      rw [e, restriction_apply_eq_reduction, reduction_eq_zero_iff_mem_ideal_smul, ← pow_one (Jid X la G.w), mem_Jid_pow_smul_top, ← mem_JHfr, coe_toHK0]
      have e2 : algebraMap (Rp X la G.N) (Lw X la G.w) ((∑ i, b i • (⟨emb X la G.N (X.inc wF (G.th' i)),
          emb_mem_Vw X la G.N wF (G.th' i)⟩ : ↥(Vw X la G.N wF)) : ↥(Vw X la G.N wF)) : Rp X la G.N) =
          ∑ i, b i • algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) := by
        rw [AddSubmonoidClass.coe_finsetSum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, Algebra.smul_def, map_mul,
          ← IsScalarTower.algebraMap_apply (Kp X la G.N) (Rp X la G.N) (Lw X la G.w), ← Algebra.smul_def]
      rw [e2]
      exact hb
    funext i
    exact Fintype.linearIndependent_iff.mp hB.1 b hlin i
  have hmem : ∑ i, aeval (ySec X la G.w) (c i) *
      algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) ∈ JHfr X la G.w wF (a0 D j T) := by
    rw [rhoK_apply, toWK_eq_zero_iff, mem_Jid_pow_smul_top, ← mem_JHfr, coe_toHK, hxc, map_sum] at h0
    have e : ∀ i, frac X la G.w T (phiN X la G.w wF T (G.th' i) (c i)) = aeval (ySec X la G.w) (c i) *
        algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) := fun i =>
      frac_phiN X la G.w wF T (G.th' i) (c i) fun m hm => ((hc i m hm).le.trans (Nat.sub_le _ _))
    simp only [e] at h0
    exact h0
  have hc0 := ind_claim (ySec X la G.w)
    (fun i => algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i)))) (JHfr X la G.w wF)
    (dSec X la G.w) (dSec_ySec X la G.w) (fun l i => dSec_emb X la G.w l _) (dSec_algebraMap_Kp X la G.w)
    (fun l a x hx => dSec_mem X la G.w l wF a x hx) (JHfr_succ_le X la G.w wF)
    (fun m i => ySec_monomial_mul_mem X la G.w wF m (G.th' i)) hbase (a0 D j T) c hc hmem
  apply Subtype.ext
  rw [hxc, hc0]
  simp

end Main

end Formalism.MainNotions.Gaps.EtaleWeightGaps
