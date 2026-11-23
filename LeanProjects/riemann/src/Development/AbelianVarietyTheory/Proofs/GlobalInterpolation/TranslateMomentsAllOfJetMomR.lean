import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WopAddLattice
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCoprimeMulIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRatNear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousCharacter
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlgEntireTranslate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceOne
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.MomentCombSplitting

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.PlaceComponents GlobalTheory.QuadSubfield
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

namespace GlobalTheory.MomT.FromComb

variable {D : D7} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem mem_of_coprime {A : Type*} [AddCommGroup A] (H : AddSubgroup A) {x : A} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : a • x ∈ H) (hb : b • x ∈ H) : x ∈ H := by
  obtain ⟨u, v, h⟩ := Nat.isCoprime_iff_coprime.2 hab
  have : x = u • a • x + v • b • x := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, h, one_smul]
  rw [this]
  exact add_mem (zsmul_mem ha _) (zsmul_mem hb _)

theorem norm_p_pow (n : ℕ) : ‖(p : ℂ_[p]) ^ n‖ = (p : ℝ) ^ (-(n : ℤ)) := by
  have h : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
  rw [norm_pow, h, norm_algebraMap', Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]

theorem norm_coprime {s : ℕ} (h : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 := norm_algebraMap' ℂ_[p] (s : ℚ_[p])
  rw [Padic.norm_natCast_eq_one_iff.2 h.symm] at h1
  simpa using h1

theorem exists_eq_pow_mul (n : ℕ) (u : 𝓞 D.host.K) (h1 : ‖homP D lam (u : D.host.K)‖ ≤ (p : ℝ) ^ (-(n : ℤ)))
    (h2 : ‖homPbar D lam (u : D.host.K)‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    ∃ v : 𝓞 D.host.K, (u : D.host.K) = (p : D.host.K) ^ n * (v : D.host.K) := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : D.host.K) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast hp.pos) _
  obtain ⟨s, hs, z, hz⟩ := GlobalTheory.IntegralAtBothPrimes.exists_coprime_mul_integral D p lam ((u : D.host.K) / (p : D.host.K) ^ n)
    (by rw [atP₂, map_div₀, map_pow, map_natCast, norm_div, norm_p_pow, div_le_one hpos]; exact h1)
    (by rw [atPbar_eq, map_div₀, map_pow, map_natCast, norm_div, norm_p_pow, div_le_one hpos]; exact h2)
  obtain ⟨a, b, h⟩ := Nat.isCoprime_iff_coprime.2 (hs.pow_right n)
  have h' : (a : D.host.K) * s + b * (p : D.host.K) ^ n = 1 := by exact_mod_cast h
  refine ⟨a * z + b * u, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap] at hz
  simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast] at hz ⊢
  rw [← hz]
  field_simp
  linear_combination (-(u : D.host.K)) * h'

theorem phi_conj (x : D.host.E) : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := by
  rw [← CU.star_conj]
  exact host_star_emb D _ x

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
  {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}

theorem hfInt_goodLifts (hI : IO.HfInt (tor0 D cc δ) (La D (tor0 D cc δ) L L')) (N₀ n : ℕ) :
    IO.HfInt (tor0 D cc δ) (goodLifts D (tor0 D cc δ) lam N₀ n L L') := by
  refine IO.HfInt_closure _ _ ?_
  rintro _ ⟨κ, hκ, x, hx, rfl⟩ _ ⟨κ', hκ', x', hx', rfl⟩
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  change ‖atPbar D lam _‖ ≤ _ at hκ hκ'
  rw [atPbar_eq] at hκ hκ'
  obtain ⟨v, hv⟩ := exists_eq_pow_mul lam (2 * n) (κ * conjO D κ')
    (by
      push_cast
      rw [map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le D _ κ)).trans hκ')
    (by
      push_cast
      rw [map_mul, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_int_le D _ _)).trans hκ)
  have hv' : D.host.φ₀ ((κ : D.host.K) : D.host.E) * starRingEnd ℂ (D.host.φ₀ ((κ' : D.host.K) : D.host.E)) =
      (p : ℂ) ^ (2 * n) * D.host.φ₀ ((v : D.host.K) : D.host.E) := by
    have := congrArg (fun c : D.host.K => D.host.φ₀ (c : D.host.E)) hv
    push_cast at this
    simp only [map_mul, map_pow, map_natCast] at this
    rw [← this, ← phi_conj]
    rfl
  have := hI _ (int_smul_mem_La D cc δ L L' v (nsmul_mem hx N₀)) _ (nsmul_mem hx' N₀)
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, IO.Hf_smul] at this
  rw [IO.Hf_smul]
  change IO.Good D _ at this
  convert this using 2
  simp only [map_mul, map_div₀, map_pow, map_natCast]
  field_simp
  linear_combination (N₀ : ℂ) ^ 2 * hv'

abbrev mulSub (n₀ : ℕ) (Λ : AddSubgroup (VC D N N')) : AddSubgroup (VC D N N') := Λ.map (nsmulAddMonoidHom n₀)

theorem mulSub_le (n₀ : ℕ) (Λ : AddSubgroup (VC D N N')) : mulSub n₀ Λ ≤ Λ := by
  rintro _ ⟨x, hx, rfl⟩
  exact nsmul_mem hx n₀

theorem pow_smul_goodLifts {N₀ n : ℕ} {y : VC D N N'} (hy : y ∈ goodLifts D (tor0 D cc δ) lam N₀ n L L') :
    p ^ n • y ∈ mulSub N₀ (La D (tor0 D cc δ) L L') := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨κ, -, x, hx, rfl⟩ := hz
    refine ⟨_, int_smul_mem_La D cc δ L L' κ hx, ?_⟩
    rw [nsmulAddMonoidHom_apply, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem U_mem_ThSp (T : Tor D) {Λ : AddSubgroup (VC D N N')} (hI : IO.HfInt T Λ) {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T Λ)
    {n₀ : ℕ} {t : VC D N N'} (ht : n₀ • t ∈ Λ) : U D T t G ∈ ThSp D T (mulSub n₀ Λ) := by
  refine ⟨IO.U_diff T t hG.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ z
  rw [nsmulAddMonoidHom_apply]
  obtain ⟨a, b, -, h⟩ := hI x hx _ ht
  have h1 : (Hf D T (n₀ • x) t).im = b := by rw [GlobalTheory.CommutatorCharacter.Hf_nsmul_swap, h]; simp
  have h2 : (Hf D T t (n₀ • x)).im = ((-b : ℤ) : ℝ) := by rw [IO.Hf_herm, Complex.conj_im, h1]; simp
  have h3 : U D T t G z = al D T (n₀ • x) * IO.cf T t (n₀ • x) * U D T (t + n₀ • x) G z := by
    conv_lhs => rw [← IO.fix_eq T hG (nsmul_mem hx n₀)]
    rw [IO.U_smul, IO.U_U]; ring
  rw [h3, IO.U_U, IO.cf_int T _ _ _ h1, IO.cf_int T _ _ _ h2, add_comm t,
    IO.neg_one_zpow_congr (n := -b) (m := - -b) ⟨-b, by ring⟩]
  ring

theorem exists_coords {r : ℕ} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : LocBasis D p (YYl D L L') b)
    {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') : ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : Fin r → 𝓞 D.host.K,
      (s : ℂ) • x = ∑ i, D.host.φ₀ ((c i : D.host.K) : D.host.E) • vecOf D cc δ (b i) := by
  have hx' := IO.La_le_gen cc δ L L' hx
  clear hx
  induction hx' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c₀, -, A, hA, rfl⟩ := hz
    obtain ⟨s, hs, c, hc⟩ := hb.2.2 A hA
    refine ⟨s, hs, fun i => c₀ * c i, ?_⟩
    have h1 := congrArg (GlobalTheory.CommutatorCharacter.vecHom cc δ) hc
    rw [map_sum, Nat.cast_smul_eq_nsmul, map_nsmul] at h1
    simp only [GlobalTheory.CommutatorCharacter.vecHom_apply, vecOf_smul] at h1
    have h2 : (δ * D.host.φ₀ ((c₀ : D.host.K) : D.host.E)) • embV D (tor0 D cc δ) A =
        D.host.φ₀ ((c₀ : D.host.K) : D.host.E) • vecOf D cc δ A := by rw [vecOf, smul_smul, mul_comm]
    rw [h2, smul_comm, Nat.cast_smul_eq_nsmul, h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← map_mul]
    rfl
  | zero => exact ⟨1, by simp, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, c, hc⟩ := hx
    obtain ⟨s', hs', c', hc'⟩ := hy
    refine ⟨s * s', Nat.Coprime.mul_left hs hs', fun i => s' * c i + s * c' i, ?_⟩
    have : ((s * s' : ℕ) : ℂ) • (x + y) = (s' : ℂ) • (s : ℂ) • x + (s : ℂ) • (s' : ℂ) • y := by
      push_cast; module
    rw [this, hc, hc', Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul, ← add_smul]
    simp
  | neg x _ hx =>
    obtain ⟨s, hs, c, hc⟩ := hx
    refine ⟨s, hs, fun i => - c i, ?_⟩
    rw [smul_neg, hc, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp

def liftZ (p n : ℕ) (ε : 𝓞 D.host.K) {r : ℕ} (v : Fin r → VC D N N') : (Fin r → ℤ) →+ VC D N N' :=
  AddMonoidHom.mk' (fun z => (D.host.φ₀ ((ε : D.host.K) : D.host.E) / (p : ℂ) ^ n) • ∑ i, z i • v i) fun z z' => by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

theorem liftZ_apply (p n : ℕ) (ε : 𝓞 D.host.K) {r : ℕ} (v : Fin r → VC D N N') (z : Fin r → ℤ) :
    liftZ p n ε v z = (D.host.φ₀ ((ε : D.host.K) : D.host.E) / (p : ℂ) ^ n) • ∑ i, z i • v i := rfl

theorem liftY_eq (p n : ℕ) (ε : 𝓞 D.host.K) {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Fin r → Fin (p ^ n)) :
    liftY D (tor0 D cc δ) δ p n ε b y = liftZ p n ε (fun i => vecOf D cc δ (b i)) fun i => ((y i : ℕ) : ℤ) := by
  have h := vecOf_smul D cc δ ((ε : D.host.K) / (p : D.host.K) ^ n) (∑ i, (((y i : ℕ) : D.host.E)) • b i)
  push_cast at h
  refine h.trans ?_
  rw [liftZ_apply, ← GlobalTheory.CommutatorCharacter.vecHom_apply, map_sum, map_div₀, map_pow, map_natCast]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, natCast_zsmul]
  rfl

theorem exists_congr (hE : ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) {r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : NNBasis D (tor0 D cc δ) δ p L L' b) {M n m : ℕ} (hM : Nat.Coprime M p)
    (hm : n ≤ m) {ε : 𝓞 D.host.K} (hε : IsIdem D lam m ε) (κ : 𝓞 D.host.K)
    (hκ : ‖homPbar D lam (κ : D.host.K)‖ ≤ (p : ℝ) ^ (-(n : ℤ))) {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') :
    ∃ z : Fin r → ℤ, (D.host.φ₀ ((κ : D.host.K) : D.host.E) / (p : ℂ) ^ n) • x -
      liftZ p n ε (fun i => M • vecOf D cc δ (b i)) z ∈ La D (tor0 D cc δ) L L' := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨h1, h2⟩ := (isIdem_iff D lam n ε).1 (I3.JetMomEq.isIdem_mono lam ε hε hm)
  obtain ⟨s, hs, c, hc⟩ := exists_coords hb.1 hx
  have hMs : ‖((M * s : ℕ) : ℂ_[p])‖ = 1 := norm_coprime (Nat.Coprime.mul_left hM hs)
  have hMs0 : ((M * s : ℕ) : ℂ_[p]) ≠ 0 := fun h => by simp [h] at hMs
  have key : ∀ i, ∃ (k : ℕ) (v : 𝓞 D.host.K), (κ : D.host.K) * (c i : D.host.K) - (ε : D.host.K) * k * ((M * s : ℕ) : D.host.K) =
      (p : D.host.K) ^ n * (v : D.host.K) := by
    intro i
    have hκc : ‖homP D lam (κ : D.host.K) * homP D lam (c i : D.host.K)‖ ≤ 1 := by
      rw [norm_mul]
      exact mul_le_one₀ (norm_int_le D _ _) (norm_nonneg _) (norm_int_le D _ _)
    obtain ⟨k, -, hk⟩ := (GlobalTheory.PlaceApprox.approx D p lam hE ((κ : D.host.K) * (c i : D.host.K) / ((M * s : ℕ) : D.host.K))).1
      (by rw [atP₂, map_div₀, map_natCast, norm_div, hMs, div_one, map_mul]; exact hκc) n
    rw [atP₂, map_div₀, map_natCast, map_mul] at hk
    have hk1 : ‖(k : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    obtain ⟨v, hv⟩ := exists_eq_pow_mul lam n (κ * c i - ε * (k : 𝓞 D.host.K) * ((M * s : ℕ) : 𝓞 D.host.K))
      (by
        simp only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_mul, map_natCast] at hk h1 ⊢
        set a := homP D lam (algebraMap _ _ κ) * homP D lam (algebraMap _ _ (c i))
        set e := homP D lam (algebraMap _ _ ε)
        have : a - e * k * ((M * s : ℕ) : ℂ_[p]) =
            ((M * s : ℕ) : ℂ_[p]) * (a / ((M * s : ℕ) : ℂ_[p]) - k) + -((e - 1) * k * ((M * s : ℕ) : ℂ_[p])) := by
          field_simp
          ring
        rw [this]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
        · rw [norm_mul, hMs, one_mul]; exact hk
        · rw [norm_neg, norm_mul, hMs, mul_one, norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) hk1).trans h1)
      (by
        simp only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_mul, map_natCast] at hκ h2 ⊢
        rw [sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
        · rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) (norm_int_le D _ _)).trans hκ
        · rw [norm_neg, norm_mul, hMs, mul_one, norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) hk1).trans h2)
    refine ⟨k, v, ?_⟩
    simpa only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_mul, map_natCast] using hv
  choose k v hv using key
  have hv' : ∀ i, D.host.φ₀ ((κ : D.host.K) : D.host.E) * D.host.φ₀ ((c i : D.host.K) : D.host.E) -
      D.host.φ₀ ((ε : D.host.K) : D.host.E) * k i * (M * s) = (p : ℂ) ^ n * D.host.φ₀ ((v i : D.host.K) : D.host.E) := by
    intro i
    have := congrArg (fun c : D.host.K => D.host.φ₀ (c : D.host.E)) (hv i)
    push_cast at this
    simpa only [map_sub, map_mul, map_pow, map_natCast] using this
  refine ⟨fun i => k i, mem_of_coprime _ (hs.pow_right n) ?_ ?_⟩
  · have : s • ((D.host.φ₀ ((κ : D.host.K) : D.host.E) / (p : ℂ) ^ n) • x -
        liftZ p n ε (fun i => M • vecOf D cc δ (b i)) fun i => (k i : ℤ)) =
        ∑ i, D.host.φ₀ ((v i : D.host.K) : D.host.E) • vecOf D cc δ (b i) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_comm, hc, liftZ_apply, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]
      simp only [smul_smul, ← sub_smul]
      congr 1
      field_simp
      linear_combination hv' i
    rw [this]
    exact sum_mem fun i _ => int_smul_mem_La D cc δ L L' _ (hb.2 i)
  · rw [← Nat.cast_smul_eq_nsmul ℂ, smul_sub, liftZ_apply, smul_smul, smul_smul, Nat.cast_pow,
      mul_div_cancel₀ _ (pow_ne_zero n hp0), mul_div_cancel₀ _ (pow_ne_zero n hp0)]
    exact sub_mem (int_smul_mem_La D cc δ L L' _ hx)
      (int_smul_mem_La D cc δ L L' _ (sum_mem fun i _ => zsmul_mem (nsmul_mem (hb.2 i) M) _))

theorem liftZ_nsmul (p n : ℕ) (ε : 𝓞 D.host.K) {r : ℕ} (v : Fin r → VC D N N') (z : Fin r → ℤ) (n₀ : ℕ) :
    liftZ p n ε (fun i => n₀ • v i) z = n₀ • liftZ p n ε v z := by
  rw [liftZ_apply, liftZ_apply, smul_comm n₀, Finset.smul_sum (r := n₀)]
  simp only [smul_comm n₀]

theorem exists_liftY (hE : ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) {r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : NNBasis D (tor0 D cc δ) δ p L L' b) {M n n₀ : ℕ} (hM : Nat.Coprime M p)
    {ε : 𝓞 D.host.K} (hε : IsIdem D lam (2 * n + 2) ε) {y : VC D N N'} (hy : y ∈ goodLifts D (tor0 D cc δ) lam n₀ n L L') :
    ∃ yt : Fin r → Fin (p ^ n),
      liftY D (tor0 D cc δ) δ p n ε (fun i => ((n₀ * M : ℕ) : D.host.E) • b i) yt ∈ goodLifts D (tor0 D cc δ) lam n₀ n L L' ∧
      y - liftY D (tor0 D cc δ) δ p n ε (fun i => ((n₀ * M : ℕ) : D.host.E) • b i) yt ∈ mulSub n₀ (La D (tor0 D cc δ) L L') := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  set w : Fin r → VC D N N' := fun i => M • vecOf D cc δ (b i) with hw
  have hwm : ∀ z : Fin r → ℤ, ∑ i, z i • w i ∈ La D (tor0 D cc δ) L L' := fun z =>
    sum_mem fun i _ => zsmul_mem (nsmul_mem (hb.2 i) M) _
  have hv : (fun i => vecOf D cc δ (((n₀ * M : ℕ) : D.host.E) • b i)) = fun i => n₀ • w i := by
    funext i
    rw [← GlobalTheory.CommutatorCharacter.vecHom_apply, Nat.cast_smul_eq_nsmul, map_nsmul, mul_smul]
    rfl
  have h1 : ∃ z : Fin r → ℤ, y - n₀ • liftZ p n ε w z ∈ mulSub n₀ (La D (tor0 D cc δ) L L') := by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨κ, hκ, x, hx, rfl⟩ := hy
      change ‖atPbar D lam _‖ ≤ _ at hκ
      rw [atPbar_eq] at hκ
      obtain ⟨z, hz⟩ := exists_congr lam hE hb hM (by omega : n ≤ 2 * n + 2) hε κ
        (hκ.trans (zpow_le_zpow_right₀ hp1 (by omega))) hx
      refine ⟨z, _, hz, ?_⟩
      rw [nsmulAddMonoidHom_apply, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ n₀ (_ • x), smul_smul]
      congr 2
      ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨z, hz⟩ := hx
      obtain ⟨z', hz'⟩ := hy
      exact ⟨z + z', by rw [map_add, smul_add, add_sub_add_comm]; exact add_mem hz hz'⟩
    | neg x _ hx =>
      obtain ⟨z, hz⟩ := hx
      exact ⟨-z, by rw [map_neg, smul_neg, neg_sub_neg, ← neg_sub]; exact neg_mem hz⟩
  have hg : ∀ z : Fin r → ℤ, n₀ • liftZ p n ε w z ∈ goodLifts D (tor0 D cc δ) lam n₀ n L L' := by
    intro z
    refine AddSubgroup.subset_closure ⟨ε, hε.2.trans (zpow_le_zpow_right₀ hp1 (by omega)), _, hwm z, ?_⟩
    rw [liftZ_apply, ← Nat.cast_smul_eq_nsmul ℂ n₀, smul_smul]
    congr 1
    ring
  obtain ⟨z, hz⟩ := h1
  have hq : (0 : ℤ) < ((p ^ n : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.pos n
  refine ⟨fun i => ⟨(z i % ((p ^ n : ℕ) : ℤ)).toNat, by
    have := Int.emod_lt_of_pos (z i) hq
    have := Int.emod_nonneg (z i) hq.ne'
    omega⟩, ?_, ?_⟩
  · rw [liftY_eq, hv, liftZ_nsmul]
    exact hg _
  · rw [liftY_eq, hv, liftZ_nsmul]
    have hd : z = (fun i => (((z i % ((p ^ n : ℕ) : ℤ)).toNat : ℕ) : ℤ)) + p ^ n • fun i => z i / ((p ^ n : ℕ) : ℤ) := by
      funext i
      rw [Pi.add_apply, Pi.smul_apply, Int.toNat_of_nonneg (Int.emod_nonneg (z i) hq.ne'), nsmul_eq_mul, Int.emod_add_mul_ediv]
    have hl : p ^ n • liftZ p n ε w (fun i => z i / ((p ^ n : ℕ) : ℤ)) ∈ La D (tor0 D cc δ) L L' := by
      rw [liftZ_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_pow, mul_div_cancel₀ _ (pow_ne_zero n hp0)]
      exact int_smul_mem_La D cc δ L L' _ (hwm _)
    rw [hd, map_add, map_nsmul, smul_add, ← sub_sub] at hz
    simpa using add_mem hz (AddSubgroup.mem_map_of_mem (nsmulAddMonoidHom n₀) hl)

theorem chi_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) {𝔞 : IdE D} (ha : N1 D 𝔞) : χ 𝔞 ∈ Qbar := by
  let _ := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := CU.pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  have h := hχ.2 ⟨z, hzu⟩
  simp only at h
  rw [← hspan, CU.chi_pow D χ hχ ha k hk] at h
  refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by omega : 0 < k) (mem_algebraicClosure_iff.1 ?_))
  rw [h]
  exact prod_mem fun τ _ => inv_mem (emb_mem D _ _)

theorem chiFac_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) (hA : admitted D N N' L L') : Base.chiFac χ N N' L L' ∈ Qbar :=
  mul_mem (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N _ L hA.1 (GlobalTheory.FourthRootStd.stdL_isSD D N) hA.2.2.1)) _)
    (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N' _ L' hA.2.1 (GlobalTheory.FourthRootStd.stdL_isSD D N') hA.2.2.2)) _)

theorem eNat_mem (B : Base D cc δ) (χ : IdE D → ℂ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : admitted D N N' L L') :
    B.eNat χ N N' L L' ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := by
  have h0 := GlobalTheory.NormalisedTranslate.delta_ne_zero B
  have h1 : B.thMoved N N' L L' ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L L') :=
    IO.Iop_mem_ThSp _ (IO.semiChar_of_HfInt _ (hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA))
      (IO.Iop_mem_ThSp _ (IO.semiChar_of_HfInt _ (hermitian_form_integral_values D cc hcc δ hδ h0 N N' L _
        ⟨hA.1, hA.2.1, hA.2.2.1, GlobalTheory.FourthRootStd.stdL_isSD D N'⟩))
        (GlobalTheory.Mem.Col2.WeilVac.thZero_mem B (GlobalTheory.FourthRootStd.stdOK B hcc hδ) N N'))
  refine ⟨h1.1.const_mul _, fun x hx z => ?_⟩
  change _ * U D _ x (fun w => _ * B.thMoved N N' L L' w) z = _ * B.thMoved N N' L L' z
  rw [IO.U_smul, mul_left_comm, h1.2 x hx z]

theorem coefIn_Wop (B : Base D cc δ) {χ : IdE D → ℂ} (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : IsChi D χ)
    (hA : admitted D N N' L L') {t y : VC D N N'} {n₀ n : ℕ} (h0 : 0 < n₀) (ht : n₀ • t ∈ La D (tor0 D cc δ) L L')
    (hy : p ^ n • y ∈ La D (tor0 D cc δ) L L') :
    CoefIn D (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (B.eNat χ N N' L L'))) Qbar := by
  have hp := (Fact.out : p.Prime)
  have hC : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hs := GlobalTheory.Mem.Col2.JetAlgebraic.la_le_sat hC hA.2.2.1 hA.2.2.2
  have hT := (GlobalTheory.Mem.Col2.JetAlgebraic.ta_thMoved B hC hA.2.2.1 hA.2.2.2).transl hC
    (GlobalTheory.ThetaAlgebraic.sat_of_nsmul h0 (hs ht))
  have e : Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (B.eNat χ N N' L L')) =
      fun z => (wPh D (tor0 D cc δ) p y * Base.chiFac χ N N' L L') *
        U D (tor0 D cc δ) y (U D (tor0 D cc δ) t (B.thMoved N N' L L')) z := by
    funext z
    simp only [Wop, U, Base.eNat]
    ring
  intro α
  rw [e, GlobalTheory.ThetaConj.taylor_mul D _ (IO.U_diff _ _ hT.1)]
  exact mul_mem (mul_mem (GlobalTheory.NormalisedTranslate.wPh_mem _
    (hermitian_form_integral_values D cc hcc δ hδ (GlobalTheory.NormalisedTranslate.delta_ne_zero B) N N' L L' hA) hp hy) (chiFac_mem hχ hA))
    (hT.2 y (GlobalTheory.ThetaAlgebraic.sat_of_nsmul (pow_pos hp.pos n) (hs hy)) α)

def scale (p : ℕ) [Fact p.Prime] (r M : ℕ) : C(Fin r → ℤ_[p], Fin r → ℤ_[p]) := ⟨fun a i => (M : ℤ_[p]) * a i, by fun_prop⟩

theorem exists_image {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y] (f : C(X, Y))
    (μ : C(X, ℂ_[p]) →L[ℂ_[p]] ℂ_[p]) (hμ : ‖μ‖ ≤ 1) :
    ∃ ν : C(Y, ℂ_[p]) →L[ℂ_[p]] ℂ_[p], ‖ν‖ ≤ 1 ∧ ∀ g, ν g = μ (g.comp f) := by
  let l : C(Y, ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] :=
    { toFun := fun g => μ (g.comp f)
      map_add' := fun g g' => by rw [ContinuousMap.add_comp, map_add]
      map_smul' := fun c g => by rw [ContinuousMap.smul_comp, map_smul]; rfl }
  have hl : ∀ g, ‖l g‖ ≤ 1 * ‖g‖ := fun g => (μ.le_opNorm _).trans
    (mul_le_mul hμ ((ContinuousMap.norm_le _ (norm_nonneg g)).2 fun x => g.norm_coe_le_norm _) (norm_nonneg _) zero_le_one)
  exact ⟨l.mkContinuous 1 hl, LinearMap.mkContinuous_norm_le _ zero_le_one _, fun g => rfl⟩

theorem pairN_smul (Ω : ℂ_[p]) {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (M : ℕ)
    (y : Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[p]) :
    pairN D lam Ω (fun i => (M : D.host.E) • b i) y a = pairN D lam Ω b y fun i => (M : ℤ_[p]) * a i := by
  unfold pairN
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : hYY D y ((M : D.host.E) • b i) = M • hYY D y (b i) := by
    unfold hYY
    rw [← map_nsmul]
    congr 1
    simp only [Finset.smul_sum, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [h, lamC_emb, lamC_emb]
  simp only [zc, nsmul_eq_mul]
  push_cast
  simp only [map_mul, map_natCast]
  ring

theorem kap_add_right (T : Tor D) {Λ : AddSubgroup (VC D N N')} (hI : IO.HfInt T Λ) {w l : VC D N N'} (x : VC D N N')
    (hw : w ∈ Λ) (hl : l ∈ Λ) : kap D T w (x + l) = kap D T w x := by
  obtain ⟨a, b, -, h⟩ := hI w hw l hl
  have him : (Hf D T w l).im = b := by rw [h]; simp
  unfold kap
  rw [IO.Hf_add_right, Complex.add_im, him, Complex.exp_eq_exp_iff_exists_int]
  exact ⟨-b, by push_cast; ring⟩

theorem momentsAt_of_momComb (B : Base D cc δ) {χ : IdE D → ℂ} (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : IsChi D χ)
    (hs : SplitK D p) {Ω : ℂ_[p]} (h : I3.JetMomEq.MomComb D cc δ B χ p lam Ω) : MomentsAt D cc δ (B.eNat χ) lam Ω := by
  have hp := (Fact.out : p.Prime)
  have hE := GlobalTheory.ApproxIdem.exists_isIdem D p lam hs
  intro N N' L L' hA t ht
  have hI := hermitian_form_integral_values D cc hcc δ hδ (GlobalTheory.NormalisedTranslate.delta_ne_zero B) N N' L L' hA
  obtain ⟨s, -, hsp, hh⟩ := h N N' L L' hA 1 (fun _ => t) (fun _ => L) (fun _ => L') (fun _ => ht)
    (fun _ => ⟨hA, ⟨1, by simp, by simp, by simp⟩, ⟨1, by simp, by simp, by simp⟩⟩)
  obtain ⟨n₀, h0, hn₀, ht⟩ := ht
  refine ⟨n₀, hn₀, fun r b hb => ?_⟩
  obtain ⟨hb', hm⟩ := GlobalTheory.IndefiniteRowSideFullHecke.MomentCombSplitting.goodBasis_smul D cc δ L L' (Nat.Coprime.mul_left hn₀ hsp) b hb
  obtain ⟨μ, hμ, -, h1, -⟩ := hh (fun _ => 1) (fun _ => ⟨one_mem _, by rw [I3.JetMomEq.lamC_one]; simp⟩) r _ hb' fun i => by
    obtain ⟨x, hx, e⟩ := hm i
    exact ⟨n₀ • x, nsmul_mem hx _, e.trans (by rw [mul_comm, mul_smul])⟩
  simp only [one_mul, Finset.univ_unique, Finset.sum_singleton] at h1
  obtain ⟨ν, hν, hνμ⟩ := exists_image (scale p r (n₀ * s)) μ hμ
  refine ⟨ν, hν, fun n y hy => ⟨coefIn_Wop B hcc hδ hχ hA h0 ht (mulSub_le _ _ (pow_smul_goodLifts lam hy)), ?_⟩⟩
  intro m y' g hg
  obtain ⟨ε, hε⟩ := hE (2 * n + 2)
  obtain ⟨yt, hx, hl⟩ := exists_liftY lam hE hb hsp hε hy
  set x := liftY D (tor0 D cc δ) δ p n ε (fun i => ((n₀ * s : ℕ) : D.host.E) • b i) yt with hxd
  obtain ⟨l, rfl⟩ : ∃ l, y = x + l := ⟨y - x, by abel⟩
  have hlg : l ∈ goodLifts D (tor0 D cc δ) lam n₀ n L L' := by simpa using sub_mem hy hx
  rw [add_sub_cancel_left] at hl
  rw [GlobalTheory.ThetaShift.Wop_add_lattice D _ N N' _ p hp (IO.HfInt_mono _ (mulSub_le n₀ _) hI) _
    (U_mem_ThSp _ hI (eNat_mem B χ hcc hδ hA) ht) x l hl ⟨n, pow_smul_goodLifts lam hx⟩
    (hfInt_goodLifts lam hI n₀ n x hx l hlg), hνμ]
  refine h1 n ε hε yt m y' _ ?_
  obtain ⟨ψ, hψ, hψ'⟩ := GlobalTheory.CommutatorCharacter.exists_continuous_character D cc δ p lam N N' _ hI n r _ x hb'.2
    (mulSub_le _ _ (pow_smul_goodLifts lam hx))
  have hd : DenseRange fun (a : Fin r → ℕ) (i : Fin r) => (a i : ℤ_[p]) :=
    DenseRange.piMap fun _ : Fin r => PadicInt.denseRange_natCast (p := p)
  have key : g.comp (scale p r (n₀ * s)) = ψ * ∏ j, pairC D lam Ω (fun i => ((n₀ * s : ℕ) : D.host.E) • b i) (y' j) := by
    refine ContinuousMap.coe_injective (hd.equalizer (by fun_prop) (by fun_prop) (funext fun a => ?_))
    have e1 := hg fun i => n₀ * s * a i
    have e2 := hψ' fun i => (a i : ℤ)
    have e3 : ∑ i, ((n₀ * s * a i : ℕ) : D.host.E) • b i = ∑ i, (a i : D.host.E) • ((n₀ * s : ℕ) : D.host.E) • b i :=
      Finset.sum_congr rfl fun i _ => by rw [smul_smul, Nat.cast_mul _ (a i), mul_comm]
    have hw : vecOf D cc δ (∑ i, (a i : D.host.E) • ((n₀ * s : ℕ) : D.host.E) • b i) ∈ La D (tor0 D cc δ) L L' := by
      rw [← GlobalTheory.CommutatorCharacter.vecHom_apply, map_sum]
      exact sum_mem fun i _ => by rw [Nat.cast_smul_eq_nsmul, map_nsmul]; exact nsmul_mem (hb'.2 i) _
    rw [e3] at e1
    change _ = lamC lam (kap D _ (vecOf D cc δ _) _) * _ at e1
    rw [kap_add_right _ hI x hw (mulSub_le _ _ hl)] at e1
    simp only [Int.cast_natCast] at e2
    simp only [Nat.cast_mul _ (a _)] at e1
    simp only [Function.comp_apply, ContinuousMap.mul_apply, ContinuousMap.prod_apply, ContinuousMap.comp_apply, e2]
    refine e1.trans ?_
    congr 1
    exact Finset.prod_congr rfl fun j _ => (pairN_smul lam Ω b _ _ _).symm
  intro a
  rw [key, ContinuousMap.mul_apply, hψ, ContinuousMap.prod_apply]
  rfl

theorem translateMomentsAll_of_jetMomR : Formalism.L2.Ker.I3.JetMomEq.JetMomR → GlobalTheory.MomT.TranslateMomentsAll := by
  intro h D cc δ B χ hcc hδ hχ p _ lam hs hc
  obtain ⟨-, ⟨Ω, hΩ, -, hC⟩, -⟩ := h D cc δ B hcc hδ χ hχ p hs hc lam
  exact ⟨Ω, hΩ, momentsAt_of_momComb lam B hcc hδ hχ hs hC⟩

end GlobalTheory.MomT.FromComb
