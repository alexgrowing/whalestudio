import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
import Formalism.PadicSubsetSums.StableGradedCounts.PropertyWOfEstimates
import Formalism.PadicSubsetSums.StableGradedCounts.LocalEstimateIVOfTypeSetWeight

open Finset Polynomial

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ConcNWeight

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN

local instance factG {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG {D : D7} (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def TieVecW {D : D7} (A : AllRows D) : Prop :=
  ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧
    ∀ (k : Fin 2) (v : D.nd.PlG k), A.eVec k v = eUk D k (ψ₀ k) ∨ A.eVec k v = eJk D k (ψ₀ k)

def RangeW (D : D7) : Prop := 100 ≤ D.R.r ∧ ∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k

section Weights

variable {D : D7}

theorem wtOf_eq_zero_of_not_label {k : Fin 2} (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    {f : (ZMod (D.host.g k))[X]} (hf : ¬ IsLabel D k f) : wtOf D k a f = 0 := by
  unfold wtOf
  rw [D.ntypes.eSer_zero k f hf, mul_zero]
  simp

theorem sum_eSer (k : Fin 2) :
    ∑ c : Fin D.R.r → ZMod (D.host.g k), D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf c) = 1 := by
  classical
  obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum k
  have hcoeff : ∀ (c : Fin D.R.r → ZMod (D.host.g k)) (i : Fin D.R.r),
      (Formalism.CyclotomicNorms.monicOf c).coeff (i : ℕ) = c i := by
    intro c i
    unfold Formalism.CyclotomicNorms.monicOf
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg i.isLt.ne, zero_add,
      Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg]
      exact fun h => hj (Fin.ext h).symm
    · simp
  have hinj : Function.Injective (fun c : Fin D.R.r → ZMod (D.host.g k) => Formalism.CyclotomicNorms.monicOf c) := by
    intro c c' h
    funext i
    have := congrArg (fun p => Polynomial.coeff p (i : ℕ)) h
    simpa [hcoeff] using this
  have hsurj : ∀ f ∈ S, f = Formalism.CyclotomicNorms.monicOf (fun i : Fin D.R.r => f.coeff (i : ℕ)) := by
    intro f hf
    obtain ⟨hm, hdeg, -⟩ := (hS f).1 hf
    conv_lhs => rw [hm.as_sum, hdeg]
    unfold Formalism.CyclotomicNorms.monicOf
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (f.coeff i) * Polynomial.X ^ i) _).symm
  have himg : ∑ f ∈ Finset.univ.image (fun c : Fin D.R.r → ZMod (D.host.g k) => Formalism.CyclotomicNorms.monicOf c),
      D.ntypes.eSer k f = ∑ c, D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf c) :=
    Finset.sum_image (fun a _ b _ h => hinj h)
  rw [← himg, ← hsum]
  symm
  apply Finset.sum_subset
  · intro f hf
    rw [Finset.mem_image]
    exact ⟨_, Finset.mem_univ _, (hsurj f hf).symm⟩
  · intro f _ hf
    exact D.ntypes.eSer_zero k f (fun h => hf ((hS f).2 h))

theorem sum_wtOf (k : Fin 2) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (ha : (a.coeff 1).re ≠ 0) :
    ∑ c : Fin D.R.r → ZMod (D.host.g k), wtOf D k a (Formalism.CyclotomicNorms.monicOf c) = 1 := by
  have h := sum_eSer (D := D) k
  let L : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) →+ ℝ :=
    AddMonoidHom.mk' (fun x => (x.coeff 1).re) (fun x y => by simp)
  have hL : ∀ x, L x = (x.coeff 1).re := fun x => rfl
  have hs := map_sum L (fun c : Fin D.R.r → ZMod (D.host.g k) => a * D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf c)) Finset.univ
  simp only [hL] at hs
  rw [← Finset.mul_sum, h, mul_one] at hs
  unfold wtOf
  rw [← Finset.sum_div, ← hs, div_self ha]

end Weights

section Value

theorem entN_one_ne {A : Type} [Zero A] [One A] {N : ℕ} {a b : ℕ} (h : a ≠ b) :
    entN (1 : Matrix (Fin N) (Fin N) A) a b = 0 := by
  unfold entN
  split_ifs with h'
  · exact Matrix.one_apply_ne (fun he => h (congrArg Fin.val he))
  · rfl

theorem eDat_coeff_one_re_pos (g N : ℕ) [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
    (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ) (hP : P 1) (hφ : φ 1 = 0) :
    0 < ((eDat g N P φ ψ₀).coeff 1).re := by
  classical
  have h1 : (ψ₀ (φ 1))⁻¹ = 1 := by rw [hφ, AddChar.map_zero_eq_one, inv_one]
  have hc : 0 < (Finset.univ.filter
      (fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g)))).card :=
    Finset.card_pos.mpr ⟨1, by simp [hP]⟩
  unfold eDat
  simp [h1, hP]
  rw [Finset.sum_eq_single (1 : GL (Fin N) (ZMod g))]
  · simp [h1, hφ]
    first
      | exact hc
      | positivity
      | exact inv_pos.mpr (by exact_mod_cast hc)
      | exact Finset.card_pos.mp hc
      | exact ⟨1, by simp [hP]⟩
      | exact (rfl : (0:ℕ) = 0)
  · intro b _ hb
    simp [Finsupp.single_apply, hb]
  · intro h
    exact absurd (by simp [hP]) h

theorem eU_coeff_one_re_pos (g N : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) :
    0 < ((eU g N ψ₀).coeff 1).re := by
  unfold eU
  refine eDat_coeff_one_re_pos g N _ _ ψ₀ ?_ ?_
  · intro a b
    exact ⟨fun hab => Matrix.one_apply_ne hab.ne', fun hab => by subst hab; exact Matrix.one_apply_eq a⟩
  · beta_reduce
    exact Finset.sum_eq_zero fun i _ => entN_one_ne (by omega)

theorem eJ_coeff_one_re_pos (g N kk s : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) :
    0 < ((eJ g N kk s ψ₀).coeff 1).re := by
  unfold eJ
  have e : ∀ a b : ℕ, a ≠ b → entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) a b = 0 :=
    fun a b h => entN_one_ne h
  refine eDat_coeff_one_re_pos g N _ _ ψ₀ ?_ ?_
  · refine ⟨?_, fun a _ h2 => e _ _ (by omega)⟩
    intro a b
    exact ⟨fun hab => Matrix.one_apply_ne hab.ne', fun hab => by subst hab; exact Matrix.one_apply_eq a⟩
  · unfold phiJ
    have h1 : ∑ i ∈ Finset.range (s - 1), entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) = 0 :=
      Finset.sum_eq_zero fun i _ => e _ _ (by omega)
    have h2 : ∑ i ∈ Finset.range (s - 1),
        entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) (s + kk + 1 + i) (s + kk + 2 + i) = 0 :=
      Finset.sum_eq_zero fun i _ => e _ _ (by omega)
    have h3 : ∑ a ∈ Finset.range (kk - 1), entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) (s + a) (s + a + 1) = 0 :=
      Finset.sum_eq_zero fun a _ => e _ _ (by omega)
    rw [h1, h2, h3]
    split_ifs with hs
    · rw [e (s - 1) (s + kk) (by omega), e (s + kk) (s + kk + 1) (by omega)]
      simp
    · simp

theorem eUk_coeff_one_re_pos {D : D7} (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    0 < ((eUk D k ψ₀).coeff 1).re := by
  exact eU_coeff_one_re_pos (D.host.g k) D.R.r ψ₀

theorem eJk_coeff_one_re_pos {D : D7} (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    0 < ((eJk D k ψ₀).coeff 1).re := by
  exact eJ_coeff_one_re_pos (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ₀

end Value

section PropWRec

variable {D : D7}

theorem host_facts (hA : TieAdmG D) (k : Fin 2) :
    D.host.q.Prime ∧ D.host.d.Prime ∧ D.host.q ≠ D.host.d ∧ D.host.q ≠ 2 ∧ D.host.d ≠ 2 ∧
      16 ≤ max D.host.q D.host.d ∧ 16 ∣ D.host.g k - 1 ∧ D.host.q ∣ D.host.g k - 1 ∧
      D.host.d ∣ D.host.g k - 1 := by
  have hadm := hA k
  unfold Formalism.BasicNotions.NTypes.admissible at hadm
  have hmod : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := hadm.2.2.2
  have hM : D.host.QS * D.host.q * D.host.d ∣ D.host.g k - 1 := by
    have h := Nat.dvd_sub_mod (n := D.host.QS * D.host.q * D.host.d) (D.host.g k)
    rwa [hmod] at h
  have h16 : 16 ∣ D.host.QS := by
    have h := (Nat.pow_dvd_pow 2 (show 4 ≤ D.R.toFrame.e + 2 by have := D.host.two_le_e; omega)).trans
      D.host.tower_dvd
    simpa using h
  have h2 : 2 ∣ D.host.QS := (show 2 ∣ 16 by norm_num).trans h16
  have hc : Nat.Coprime 2 (D.host.q * D.host.d) := Nat.Coprime.coprime_dvd_left h2 D.host.QS_coprime
  have hq2 : D.host.q ≠ 2 := by
    intro h
    have := Nat.Coprime.coprime_dvd_right (dvd_mul_right D.host.q D.host.d) hc
    rw [h] at this
    exact absurd this (by decide)
  have hd2 : D.host.d ≠ 2 := by
    intro h
    have := Nat.Coprime.coprime_dvd_right (dvd_mul_left D.host.d D.host.q) hc
    rw [h] at this
    exact absurd this (by decide)
  have hbig : 16 ≤ max D.host.q D.host.d := by
    have hq := D.host.qd_big.1
    have hr : 6 ≤ D.R.r := by
      have e1 : D.R.r = D.R.k + D.R.m - 1 := rfl
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      omega
    have ht : 11 ≤ D.R.t := by
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      have := D.R.rank_add_five_le
      omega
    have hTR : 11 * 6 ≤ D.R.t * D.R.r := Nat.mul_le_mul ht hr
    have e2 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := Nat.mul_assoc _ _ _
    rw [e2] at hq
    exact le_max_of_le_left (by omega)
  refine ⟨?_, ?_, ?_, hq2, hd2, hbig, (h16.trans (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)).trans hM,
    (dvd_mul_of_dvd_left (dvd_mul_left _ _) _).trans hM, (dvd_mul_left _ _).trans hM⟩
  · obtain ⟨x1, -, -⟩ := D.host.hyp
    exact x1
  · obtain ⟨-, x2, -⟩ := D.host.hyp
    exact x2
  · obtain ⟨-, -, x3, x4, -⟩ := D.host.hyp
    intro h
    rw [h] at x3
    omega

theorem rangeW_of_sizes {x ε Cs : ℝ} (h : SizesRec D x ε Cs) (hx : 3 / 2 ≤ x ^ ε) : RangeW D := by
  unfold Formalism.L2.GlobalTheoryTheory.ConcN.SizesRec Formalism.L2.GlobalTheoryTheory.ConcN.SizesAt at h
  unfold RangeW
  refine ⟨(h 0).2.2.2.2.1, fun k => ?_⟩
  have hg := (h k).1
  have h2 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have h12 : Real.exp 1 ^ 12 ≤ Real.exp (8 * x ^ ε) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have h3 : (2:ℝ) ^ 12 ≤ Real.exp 1 ^ 12 := by gcongr
  have h4 : ((2 ^ 12 : ℕ) : ℝ) ≤ (D.host.g k : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h4

theorem locShare_le_Wg (A : AllRows D) (hL : admLq D) (hA : TieAdmG D) (hR : RangeW D) (hV : TieVecW A)
    (k : Fin 2) (S : Finset (Tup D k)) (hS : ∀ t ∈ S, ¬ goodAt D k t) :
    locShare D A.eVec k S ≤ Wg D.R.f D.R.m D.R.r (D.host.g k) D.host.q D.host.d := by
  classical
  obtain ⟨ψ₀, hψ, hv⟩ := hV
  obtain ⟨hnn, hsq, hcmp, -⟩ := hL k (ψ₀ k) (hψ k)
  obtain ⟨hq, hd, hqd, hq2, hd2, h16m, h16, hqg, hdg⟩ := host_facts hA k
  let wJ : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) → ℝ :=
    fun v c => wtOf D k (A.eVec k v) (Formalism.CyclotomicNorms.monicOf c)
  let P : (Fin D.R.r → ZMod (D.host.g k)) → ℝ := fun c => wtOf D k (eUk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c)
  have hJnn : ∀ v f, 0 ≤ wtOf D k (A.eVec k v) f := by
    intro v f
    rcases hv k v with h | h <;> rw [h]
    · exact (hnn f).1
    · exact (hnn f).2
  have hPnn : ∀ c, 0 ≤ P c := fun c => (hnn _).1
  have hJsum : ∀ v, ∑ c, wJ v c = 1 := by
    intro v
    rcases hv k v with h | h
    · simp only [wJ]; rw [h]; exact sum_wtOf k _ (eUk_coeff_one_re_pos k _).ne'
    · simp only [wJ]; rw [h]; exact sum_wtOf k _ (eJk_coeff_one_re_pos k _).ne'
  have hPsum : ∑ c, P c = 1 := sum_wtOf k _ (eUk_coeff_one_re_pos k _).ne'
  have hg1 : (1 : ℝ) ≤ (D.host.g k : ℝ) := by exact_mod_cast (D.host.g_prime k).one_lt.le
  have hcmpv : ∀ v c, (1 - 1 / (D.host.g k : ℝ)) * P c ≤ wJ v c := by
    intro v c
    have hle : 1 - 1 / (D.host.g k : ℝ) ≤ 1 := sub_le_self _ (by positivity)
    rcases hv k v with h | h
    · have : wJ v c = P c := by simp only [wJ, P]; rw [h]
      rw [this]
      exact mul_le_of_le_one_left (hPnn c) hle
    · have : wJ v c = wtOf D k (eJk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c) := by simp only [wJ]; rw [h]
      rw [this]
      by_cases hlab : IsLabel D k (Formalism.CyclotomicNorms.monicOf c)
      · exact hcmp _ hlab
      · simp only [P]
        rw [wtOf_eq_zero_of_not_label _ hlab, wtOf_eq_zero_of_not_label _ hlab, mul_zero]

  have hred : locShare D A.eVec k S ≤
      ∑ x ∈ (Finset.univ : Finset (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k))).filter
        (fun x => ¬ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GoodAt (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) D.R.r
          (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (x v)) (D.nd.chiT k)), ∏ v, wJ v (x v) := by
    unfold locShare
    let cv : Tup D k → (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k)) := fun t v i => (t v).coeff i
    have hS' : ∑ t ∈ S, ∏ v, wtOf D k (A.eVec k v) (t v) =
        ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, wtOf D k (A.eVec k v) (t v) := by
      rw [Finset.sum_filter_of_ne]
      intro t _ hne v
      by_contra hv'
      exact hne (Finset.prod_eq_zero (Finset.mem_univ v) (wtOf_eq_zero_of_not_label _ hv'))
    have hcv : ∀ t : Tup D k, (∀ v, IsLabel D k (t v)) → ∀ v, Formalism.CyclotomicNorms.monicOf (cv t v) = t v :=
      fun t ht v => Formalism.CyclotomicNorms.Sqf.monicOf_coeffs (t v) (ht v).1 (ht v).2.1
    rw [hS']
    calc ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, wtOf D k (A.eVec k v) (t v)
        = ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, wJ v (cv t v) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          have ht := (Finset.mem_filter.1 ht).2
          refine Finset.prod_congr rfl fun v _ => ?_
          simp only [wJ]
          rw [hcv t ht v]
      _ = ∑ x ∈ (S.filter (fun t => ∀ v, IsLabel D k (t v))).image cv, ∏ v, wJ v (x v) := by
          rw [Finset.sum_image]
          intro t ht t' ht' h
          have ht := (Finset.mem_filter.1 ht).2
          have ht' := (Finset.mem_filter.1 ht').2
          funext v
          rw [← hcv t ht v, ← hcv t' ht' v]
          exact congrArg Formalism.CyclotomicNorms.monicOf (congrFun h v)
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun x _ _ => Finset.prod_nonneg fun v _ => hJnn v _
          intro x hx
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨htS, htl⟩ := Finset.mem_filter.1 ht
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hgood => hS t htS ?_⟩
          have hfun : (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (cv t v)) = t := funext fun v => hcv t htl v
          rw [hfun] at hgood
          exact Formalism.MainNotions.N.PlaceLabelTeichmuller.good_of D.R.r t (D.nd.chiT k) hgood

  have hT := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.comparison_transfer_holds (D.nd.PlG k) (fun _ => Fin D.R.r → ZMod (D.host.g k))
    (fun _ => P) wJ (D.host.g k : ℝ)
    ((Finset.univ : Finset (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k))).filter
        (fun x => ¬ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GoodAt (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) D.R.r
          (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (x v)) (D.nd.chiT k)))
    hg1 (fun _ => hPnn) (fun _ => hPsum) hJsum hcmpv
  have hW := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.property_W_of_estimates (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (D.nd.PlG k)
    (Fin D.R.m) D.R.r D.host.q D.host.d (D.nd.chiT k) P hR.1 (by rw [ZMod.card]; exact hR.2 k) hq hd hqd hq2
    hd2 h16m (by rw [ZMod.card]; exact h16) (by rw [ZMod.card]; exact hqg) (by rw [ZMod.card]; exact hdg)
    hPnn hPsum (by
      intro c hc
      have hc' : c ∈ (Finset.univ : Finset (Fin D.R.r → ZMod (D.host.g k))).filter
          (fun c => Squarefree (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧ (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).coeff 0 ≠ 0) := by
        unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqSet at hc
        convert hc
      obtain ⟨-, hsqf, h0⟩ := Finset.mem_filter.1 hc'
      have hlab : IsLabel D k (Formalism.CyclotomicNorms.monicOf c) :=
        ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf c, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf c, h0⟩
      show wtOf D k (eUk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c) = _
      rw [hsq _ hlab hsqf, Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqWeight, ZMod.card, one_div, ← Multiset.prod_map_inv]
      convert rfl <;> rfl)
  refine le_trans hred (le_trans hT ?_)
  refine le_trans (add_le_add hW le_rfl) (le_of_eq ?_)
  rw [ZMod.card, D.nd.card_PlG k, Fintype.card_fin]
  unfold Wg
  ring

end PropWRec

theorem weightAllRows_of {D : D7} (A : AllRows D) (hL : admLq D) (hA : TieAdmG D) (hR : RangeW D)
    (hV : TieVecW A) : WeightAllRows A := by
  unfold WeightAllRows
  refine ⟨fun k v f => ?_, fun k S hS => locShare_le_Wg A hL hA hR hV k S hS⟩
  obtain ⟨ψ₀, hne, hv⟩ := hV
  unfold admLq at hL
  rcases hv k v with h | h
  · rw [h]
    exact ((hL k (ψ₀ k) (hne k)).1 f).1
  · rw [h]
    exact ((hL k (ψ₀ k) (hne k)).1 f).2

end Formalism.L2.GlobalTheoryTheory.ConcNWeight
