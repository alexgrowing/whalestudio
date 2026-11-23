import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AxSenTateComplexPadicFixedClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubOnePowTotient
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.TateTwist
variable {l : ℕ} [Fact l.Prime]

abbrev Fz (z : Om l) : IntermediateField ℚ_[l] (Om l) := IntermediateField.adjoin ℚ_[l] {z}

def Vz (z : Om l) (N : ℕ) : Submodule (Fz (z ^ N)) (Om l) :=
  Submodule.span _ {w | ∃ k, ¬ N ∣ k ∧ w = z ^ k}

theorem pow_mem_Fz (z : Om l) (k : ℕ) : z ^ k ∈ Fz z :=
  pow_mem (IntermediateField.mem_adjoin_simple_self _ _) k

theorem Vz_repr (z : Om l) (N : ℕ) (hN : 0 < N) (w : Om l) (hw : w ∈ Vz z N) :
    ∃ a : Fin N → Om l, (∀ i, a i ∈ Fz (z ^ N)) ∧ a ⟨0, hN⟩ = 0 ∧ w = ∑ i, a i * z ^ (i : ℕ) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, hk, rfl⟩ := hw
    refine ⟨Pi.single ⟨k % N, Nat.mod_lt _ hN⟩ ((z ^ N) ^ (k / N)), fun i => ?_, ?_, ?_⟩
    · rw [Pi.single_apply]
      split_ifs
      · exact pow_mem_Fz _ _
      · exact zero_mem _
    · apply Pi.single_eq_of_ne
      intro h
      exact hk (Nat.dvd_of_mod_eq_zero (congrArg Fin.val h).symm)
    · rw [Finset.sum_eq_single ⟨k % N, Nat.mod_lt _ hN⟩]
      · rw [Pi.single_eq_same, ← pow_mul, ← pow_add, Nat.div_add_mod]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, zero_mul]
      · simp
  | zero => exact ⟨0, fun _ => zero_mem _, rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha0, rfl⟩ := hx
    obtain ⟨b, hb, hb0, rfl⟩ := hy
    exact ⟨a + b, fun i => add_mem (ha i) (hb i), by simp [ha0, hb0],
      by simp [add_mul, Finset.sum_add_distrib]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, ha0, rfl⟩ := hx
    refine ⟨fun i => c * a i, fun i => mul_mem c.2 (ha i), by simp [ha0], ?_⟩
    change (c : Om l) * _ = _
    simp [Finset.mul_sum, mul_assoc]

theorem bound (n m : ℕ) (z : Om l) (hn : 1 ≤ n) (hz : IsPrimitiveRoot z (l ^ (n + m)))
    (b w : Om l) (hb : b ∈ Fz (z ^ l ^ m)) (hw : w ∈ Vz z (l ^ m)) :
    ‖(l : Om l)‖ * ‖b‖ ≤ ‖b + w‖ := by
  have hN : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  obtain ⟨a, ha, ha0, rfl⟩ := Vz_repr z _ hN w hw
  have := GlobalTheory.CycTrace.normalised_trace_bound l n m z hn hz (Pi.single ⟨0, hN⟩ b + a) (fun i => by
    refine add_mem ?_ (ha i)
    rw [Pi.single_apply]
    split_ifs
    · exact hb
    · exact zero_mem _)
  simp only [Pi.add_apply, Pi.single_eq_same, ha0, add_zero, add_mul, Finset.sum_add_distrib] at this
  rw [Finset.sum_eq_single ⟨0, hN⟩] at this
  · simpa using this
  · intro c _ hc
    rw [Pi.single_eq_of_ne hc, zero_mul]
  · simp

theorem decomp (z : Om l) (N : ℕ) (y : Om l) (hy : y ∈ Fz z) :
    ∃ b ∈ Fz (z ^ N), ∃ w ∈ Vz z N, y = b + w := by
  have hz : IsAlgebraic ℚ_[l] z := Algebra.IsAlgebraic.isAlgebraic z
  have hy' : y ∈ Algebra.adjoin ℚ_[l] {z} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hz]
    exact hy
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
  obtain ⟨p, rfl⟩ := hy'
  clear hy
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha, w, hw, h⟩ := hp
    obtain ⟨b, hb, v, hv, h'⟩ := hq
    refine ⟨a + b, add_mem ha hb, w + v, add_mem hw hv, ?_⟩
    rw [map_add, h, h']
    ring
  | monomial k c =>
    have e : (Polynomial.aeval z : Polynomial ℚ_[l] →ₐ[ℚ_[l]] Om l).toRingHom (Polynomial.monomial k c)
        = algebraMap _ _ c * z ^ k := Polynomial.aeval_monomial z
    rw [e]
    by_cases hk : N ∣ k
    · obtain ⟨q, rfl⟩ := hk
      refine ⟨_, ?_, 0, zero_mem _, (add_zero _).symm⟩
      rw [pow_mul]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (pow_mem_Fz _ _)
    · refine ⟨0, zero_mem _, _, ?_, (zero_add _).symm⟩
      exact (Vz z N).smul_mem ⟨_, IntermediateField.algebraMap_mem _ c⟩
        (Submodule.subset_span ⟨k, hk, rfl⟩)

theorem Vz_stable (n m : ℕ) (z : Om l) (hz : IsPrimitiveRoot z (l ^ (n + m)))
    (g : GQ l) (hg : g ∈ (Fz (z ^ l ^ m)).fixingSubgroup) (w : Om l) (hw : w ∈ Vz z (l ^ m)) :
    g w ∈ Vz z (l ^ m) := by
  have : NeZero (l ^ (n + m)) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  obtain ⟨a, -, hac, ha⟩ := (hz.isPrimitiveRoot_iff (ξ := g z)).1 (hz.map_of_injective g.injective)
  have hac' : (l ^ m).Coprime a := (Nat.Coprime.coprime_dvd_right (pow_dvd_pow l (Nat.le_add_left m n)) hac).symm
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, hk, rfl⟩ := hw
    refine Submodule.subset_span ⟨a * k, fun h => hk (hac'.dvd_of_dvd_mul_left h), ?_⟩
    rw [map_pow, ← ha, pow_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    change g ((c : Om l) * x) ∈ _
    rw [map_mul, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg c c.2]
    exact (Vz z (l ^ m)).smul_mem c hx

theorem zeta_pow (C : Core l) (n m : ℕ) : C.ζ (n + m) ^ l ^ m = C.ζ n := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, ← add_assoc, C.ζ_succ, ih]

theorem zeta_prim (C : Core l) (n : ℕ) : IsPrimitiveRoot (C.ζ n) (l ^ n) := by
  cases n with
  | zero => simp [C.ζ_zero]
  | succ n =>
    have h := orderOf_eq_prime_pow (x := C.ζ (n + 1)) (p := l) (n := n)
      (by rw [add_comm n 1, zeta_pow]; exact C.ζ_one)
      (by have := zeta_pow C 0 (n + 1); rwa [zero_add, C.ζ_zero] at this)
    rw [← h]
    exact IsPrimitiveRoot.orderOf _

theorem Fz_mono (C : Core l) : Monotone fun n => Fz (C.ζ n) := by
  intro a b hab
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [IntermediateField.adjoin_simple_le_iff, ← zeta_pow C a m]
  exact pow_mem_Fz _ _

theorem chi_eq_one (C : Core l) (g : GQ l) (hg : g ∈ (⨆ n, Fz (C.ζ n)).fixingSubgroup) : C.χ g = 1 := by
  ext
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  have : NeZero (l ^ n) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  have h1 := C.χ_cyc g n _ (zeta_prim C n).pow_eq_one
  have h2 : g (C.ζ n) = C.ζ n := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
    ((le_iSup (fun n => Fz (C.ζ n)) n) (IntermediateField.mem_adjoin_simple_self _ _))
  rw [h2] at h1
  have h3 : (PadicInt.toZModPow n (C.χ g : ℤ_[l])).val ≡ 1 [MOD l ^ n] := by
    have h5 := (isOfFinOrder_iff_pow_eq_one.2 ⟨_, NeZero.pos (l ^ n), (zeta_prim C n).pow_eq_one⟩).pow_eq_pow_iff_modEq.1
      (h1.symm.trans (pow_one _).symm)
    rwa [← (zeta_prim C n).eq_orderOf] at h5
  have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h3
  simpa using h4

theorem le_natDegree (n m : ℕ) (z : Om l) (hn : 1 ≤ n) (hz : IsPrimitiveRoot z (l ^ (n + m))) :
    l ^ m ≤ (minpoly (Fz (z ^ l ^ m)) z).natDegree := by
  by_contra hlt
  rw [not_le] at hlt
  have hint : IsIntegral (Fz (z ^ l ^ m)) z := Algebra.IsIntegral.isIntegral z
  have hz0 : z ≠ 0 := hz.ne_zero (pow_pos (Fact.out : l.Prime).pos _).ne'
  have h0 := minpoly.aeval (Fz (z ^ l ^ m)) z
  rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
  have h := GlobalTheory.CycTrace.normalised_trace_bound l n m z hn hz (fun i => ((minpoly (Fz (z ^ l ^ m)) z).coeff i : Om l))
    (fun i => Subtype.property _)
  have e : ∑ i : Fin (l ^ m), ((minpoly (Fz (z ^ l ^ m)) z).coeff i : Om l) * z ^ (i : ℕ) = 0 := h0
  rw [e, norm_zero] at h
  have hl : 0 < ‖(l : Om l)‖ := norm_pos_iff.2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have h1 : ‖((minpoly (Fz (z ^ l ^ m)) z).coeff 0 : Om l)‖ ≤ 0 := nonpos_of_mul_nonpos_right h hl
  exact minpoly.coeff_zero_ne_zero hint hz0 (Subtype.ext (norm_le_zero_iff.1 h1))

theorem exists_gamma (C : Core l) (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : j ≠ 0) :
    ∃ g ∈ (Fz (C.ζ n)).fixingSubgroup, (C.χ g : ℤ_[l]) ^ j ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have h1 := le_natDegree n j _ hn (zeta_prim C (n + j))
  rw [zeta_pow] at h1
  set z := C.ζ (n + j) with hz
  set F := Fz (C.ζ n)
  have hint : IsIntegral F z := Algebra.IsIntegral.isIntegral z
  have hsep : (minpoly F z).Separable := (minpoly.irreducible hint).separable
  rw [← Polynomial.card_rootSet_eq_natDegree (K := Om l) hsep (IsAlgClosed.splits _)] at h1
  have h2 : (minpoly F z).rootSet (Om l) ⊆
      ((Polynomial.nthRoots j (1 : ℤ_[l])).toFinset.image
        fun t => z ^ (PadicInt.toZModPow (n + j) t).val : Finset (Om l)) := by
    intro r hr
    obtain ⟨s, hs⟩ := minpoly.exists_algEquiv_of_root' hint.isAlgebraic (Polynomial.aeval_eq_zero_of_mem_rootSet hr)
    have hg : s.restrictScalars ℚ_[l] ∈ F.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => s.commutes ⟨x, hx⟩
    rw [Finset.coe_image]
    refine ⟨C.χ (s.restrictScalars ℚ_[l]), ?_, ?_⟩
    · simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hj)] using hcon _ hg
    · exact (C.χ_cyc _ _ _ (zeta_prim C (n + j)).pow_eq_one).symm.trans hs
  have h3 := Set.ncard_le_ncard h2 (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h3
  have h4 := h1.trans (h3.trans (Finset.card_image_le.trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _))))
  exact absurd h4 (not_le.2 (Nat.lt_pow_self (Fact.out : l.Prime).one_lt))

theorem estimate (C : Core l) (n : ℕ) (hn : 1 ≤ n) (g : GQ l) (hg : g ∈ (Fz (C.ζ n)).fixingSubgroup)
    (c : ℚ_[l]) (y₀ y : Om l) (h₀ : y₀ ∈ Fz (C.ζ n)) (hy : y ∈ ⨆ k, Fz (C.ζ k)) :
    ∃ b : Om l, ‖(l : Om l)‖ * ‖b - y₀‖ ≤ ‖y - y₀‖ ∧
      ‖(l : Om l)‖ * (‖c - 1‖ * ‖b‖) ≤ ‖g y * algebraMap _ _ c - y‖ := by
  have hy' : y ∈ ((⨆ k, Fz (C.ζ k) : IntermediateField _ _) : Set (Om l)) := hy
  rw [IntermediateField.coe_iSup_of_directed (Fz_mono C).directed_le, Set.mem_iUnion] at hy'
  obtain ⟨m, hm⟩ := hy'
  have hm' : y ∈ Fz (C.ζ (n + m)) := Fz_mono C (Nat.le_add_left m n) hm
  rw [← zeta_pow C n m] at hg h₀
  obtain ⟨b, hb, w, hw, rfl⟩ := decomp _ (l ^ m) y hm'
  have hz := zeta_prim C (n + m)
  refine ⟨b, ?_, ?_⟩
  · have := bound n m _ hn hz (b - y₀) w (sub_mem hb h₀) hw
    rwa [sub_add_eq_add_sub] at this
  · have hc : ∀ d : ℚ_[l], algebraMap _ (Om l) d ∈ Fz (C.ζ (n + m) ^ l ^ m) := fun d =>
      IntermediateField.algebraMap_mem _ d
    have := bound n m _ hn hz (algebraMap _ _ (c - 1) * b) (algebraMap _ _ c * g w - w)
      (mul_mem (hc _) hb) (sub_mem ((Vz _ _).smul_mem ⟨_, hc c⟩ (Vz_stable n m _ hz g hg w hw)) hw)
    rw [norm_mul, norm_algebraMap'] at this
    convert this using 2
    rw [map_add, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg b hb, map_sub, map_one]
    ring

theorem full (C : Core l) (i : ℤ) (x : ℂ_[l]) (hi : i ≠ 0)
    (hx : ∀ g : GQ l, Per.σC g x * (algebraMap ℚ_[l] ℂ_[l] ((C.χ g : ℤ_[l]) : ℚ_[l])) ^ i = x) : x = 0 := by
  have hcl := GlobalTheory.MemLoc.ax_sen_tate l (⨆ k, Fz (C.ζ k)).fixingSubgroup x fun g hg => by
    simpa [chi_eq_one C g hg] using hx g
  have happ : ∀ ε > 0, ∃ y ∈ ⨆ k, Fz (C.ζ k), ‖x - (y : ℂ_[l])‖ < ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := Metric.mem_closure_iff.1 hcl ε hε
    refine ⟨y, ?_, by rwa [dist_eq_norm] at h⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup (⨆ k, Fz (C.ζ k))]
    exact (IntermediateField.mem_fixedField_iff _ _).2 hy
  have hl : 0 < ‖(l : Om l)‖ := norm_pos_iff.2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  set L := ‖(l : Om l)‖
  have key : ∀ ε > 0, L * ‖x‖ ≤ (L + 3) * ε := by
    intro ε hε
    obtain ⟨y₀, hy₀, hxy₀⟩ := happ ε hε
    have hy' : y₀ ∈ ((⨆ k, Fz (C.ζ k) : IntermediateField _ _) : Set (Om l)) := hy₀
    rw [IntermediateField.coe_iSup_of_directed (Fz_mono C).directed_le, Set.mem_iUnion] at hy'
    obtain ⟨m, hm⟩ := hy'
    have hm' : y₀ ∈ Fz (C.ζ (m + 1)) := Fz_mono C (Nat.le_succ m) hm
    obtain ⟨g, hg, hgc⟩ := exists_gamma C (m + 1) (Nat.le_add_left 1 m) i.natAbs (Int.natAbs_ne_zero.2 hi)
    set c : ℚ_[l] := ((C.χ g : ℤ_[l]) : ℚ_[l]) ^ i with hc
    have hc1 : c ≠ 1 := by
      intro h
      apply hgc
      apply Subtype.ext
      have : ((C.χ g : ℤ_[l]) : ℚ_[l]) ^ i.natAbs = 1 := by
        rw [← zpow_natCast]
        rcases Int.natAbs_eq_iff.1 (rfl : i.natAbs = _) with h' | h'
        · rw [← h', ← hc, h]
        · rw [← neg_eq_iff_eq_neg] at h'
          rw [← h', zpow_neg, ← hc, h, inv_one]
      simpa using this
    have hcn : ‖c‖ = 1 := by
      rw [hc, norm_zpow, PadicInt.padic_norm_e_of_padicInt, PadicInt.norm_units, one_zpow]
    have hd : 0 < ‖c - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hc1)
    obtain ⟨y, hy, hxy⟩ := happ (min ε (‖c - 1‖ * ε / 2)) (lt_min hε (by positivity))
    obtain ⟨b, hb1, hb2⟩ := estimate C (m + 1) (Nat.le_add_left 1 m) g hg c y₀ y hm' hy
    have hca : ((algebraMap ℚ_[l] (Om l) c : Om l) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] c := rfl
    have hcC : ‖algebraMap ℚ_[l] ℂ_[l] c‖ = 1 := by
      rw [← hca, PadicComplex.norm_extends, norm_algebraMap', hcn]
    have e1 : ‖y - y₀‖ ≤ 2 * ε := by
      rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub]
      have := norm_sub_le (x - (y₀ : ℂ_[l])) (x - (y : ℂ_[l]))
      rw [sub_sub_sub_cancel_left] at this
      linarith [min_le_left ε (‖c - 1‖ * ε / 2)]
    have e2 : ‖g y * algebraMap _ _ c - y‖ ≤ ‖c - 1‖ * ε := by
      rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_mul,
        hca, ← GlobalTheory.RingBasics.σC_coe]
      have hxg := hx g
      rw [← map_zpow₀, ← hc] at hxg
      have := norm_sub_le (x - (y : ℂ_[l])) (Per.σC g (x - (y : ℂ_[l])) * algebraMap ℚ_[l] ℂ_[l] c)
      rw [norm_mul, GlobalTheory.RingBasics.norm_σC, hcC, map_sub, sub_mul, hxg, sub_sub_sub_cancel_left] at this
      linarith [min_le_right ε (‖c - 1‖ * ε / 2)]
    have e3 : L * ‖b‖ ≤ ε := by
      have : ‖c - 1‖ * (L * ‖b‖) ≤ ‖c - 1‖ * ε := by linarith
      exact le_of_mul_le_mul_left this hd
    have e4 : ‖y₀‖ ≤ ‖b‖ + ‖b - y₀‖ := by
      have := norm_sub_le b (b - y₀)
      rwa [sub_sub_cancel] at this
    have e5 : ‖x‖ ≤ ε + ‖y₀‖ := by
      have := norm_add_le (x - (y₀ : ℂ_[l])) (y₀ : ℂ_[l])
      rw [sub_add_cancel, PadicComplex.norm_extends] at this
      linarith
    nlinarith [mul_le_mul_of_nonneg_left e4 hl.le, mul_le_mul_of_nonneg_left e5 hl.le]
  have : L * ‖x‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key (ε / (L + 3)) (by positivity)
    rwa [mul_div_cancel₀ _ (by positivity), ← zero_add ε] at this
  exact norm_le_zero_iff.1 (by by_contra h; nlinarith [mul_pos hl (not_le.1 h)])

theorem σC_algebraMap (g : GQ l) (c : ℚ_[l]) :
    Per.σC g (algebraMap ℚ_[l] ℂ_[l] c) = algebraMap ℚ_[l] ℂ_[l] c := by
  have hca : algebraMap ℚ_[l] ℂ_[l] c = ((algebraMap ℚ_[l] (Om l) c : Om l) : ℂ_[l]) := rfl
  rw [hca, GlobalTheory.RingBasics.σC_coe, g.commutes]

end GlobalTheory.MemLoc.TateTwist

namespace GlobalTheory.MemLoc
open TateTwist in

theorem tate_twist_invariants : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (i : ℤ) (x : ℂ_[l]), i ≠ 0 → (∀ g ∈ GK K, Per.σC g x * (algebraMap ℚ_[l] ℂ_[l] ((C.χ g : ℤ_[l]) : ℚ_[l])) ^ i = x) → x = 0 := by
  intro l _ C K i x hi hx
  have hK := K.2
  have hidx : (GK K).index ≠ 0 := by
    rw [GK, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  have hfin : Fintype (GQ l ⧸ GK K) := Subgroup.fintypeOfIndexNeZero hidx
  set a : GQ l → ℂ_[l] := fun g => (algebraMap ℚ_[l] ℂ_[l] ((C.χ g : ℤ_[l]) : ℚ_[l])) ^ i with ha
  have amul : ∀ g h, a (g * h) = a g * a h := fun g h => by
    simp only [ha, map_mul, Units.val_mul, PadicInt.coe_mul, mul_zpow]
  have afix : ∀ g h, Per.σC g (a h) = a h := fun g h => by
    simp only [ha, map_zpow₀, σC_algebraMap]
  have ane : ∀ g, a g ≠ 0 := fun g => by
    have h1 : a 1 = 1 := by simp [ha]
    have := amul g g⁻¹
    rw [mul_inv_cancel, h1] at this
    exact left_ne_zero_of_mul_eq_one this.symm
  set f : GQ l → ℂ_[l] := fun g => Per.σC g x * a g with hf
  have fmul : ∀ g h, f (g * h) = Per.σC g (f h) * a g := fun g h => by
    simp only [hf, GlobalTheory.RingBasics.σC_mul, amul, map_mul, afix]
    ring
  have fout : ∀ g : GQ l, f (g : GQ l ⧸ GK K).out = f g := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    rw [hh, fmul]
    exact congrArg (fun t => Per.σC g t * a g) (hx h h.2)
  have hprod := full C (i * Fintype.card (GQ l ⧸ GK K)) (∏ q : GQ l ⧸ GK K, f q.out)
    (mul_ne_zero hi (by exact_mod_cast Fintype.card_ne_zero)) fun g => by
      rw [zpow_mul, zpow_natCast, map_prod, ← Finset.card_univ, ← Finset.prod_const,
        ← Finset.prod_mul_distrib, ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ GK K => f q.out]
      refine Finset.prod_congr rfl fun q _ => ?_
      have e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ GK K) := by
        rw [MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
      rw [e, fout, fmul]
  obtain ⟨q, -, hq⟩ := Finset.prod_eq_zero_iff.1 hprod
  exact (map_eq_zero _).1 ((mul_eq_zero.1 hq).resolve_right (ane _))
end GlobalTheory.MemLoc
