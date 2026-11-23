import Formalism.PieriBlockIdeals.ExponentBoundCounterexample
import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
import Formalism.PieriBlockIdeals.PieriColumnMinors.CountLeftInvSeqAlternatingWordEven
import Formalism.PieriBlockIdeals.PieriColumnMinors.MaxValEqZeroOfLt
import Formalism.RankGapBounds.RankGapProofs.FormsTensorLocalization

open MvPolynomial CategoryTheory TensorProduct

noncomputable section

namespace Formalism.CohomologicalDescent.SL2BinomialLattices

open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA

universe u v u' v'

theorem maxVal_le_log_alt (l n : ℕ) : Formalism.RankGapBounds.JumpSetsAlt.maxVal l n ≤ Nat.log l n :=
  Finset.sup_le fun _ _ => Nat.factorization_choose_le_log

theorem flat_baseChange_injective : FlatBaseChangeInj := by
  intro R O _ _ _ _ M _ _ N
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype

theorem log_le_log_bound : LgLog := by
  intro l y
  by_cases h0 : Nat.log l y = 0
  · rw [h0]
    simpa using Real.log_natCast_nonneg y
  · obtain ⟨hl, hy⟩ : 1 < l ∧ l ≤ y := by
      by_contra hcon
      apply h0
      rw [Nat.log_eq_zero_iff]
      omega
    have h1 : l ^ Nat.log l y ≤ y := Nat.pow_log_le_self l (by omega)
    have h2 : ((l : ℝ)) ^ Nat.log l y ≤ (y : ℝ) := by exact_mod_cast h1
    have h3 : (0 : ℝ) < (l : ℝ) ^ Nat.log l y := by positivity
    have h4 := Real.log_le_log h3 h2
    rwa [Real.log_pow] at h4

theorem sum_maxVal_le_card_mul_log {N : ℕ} (U : Fin N → ℤ) (l M : ℕ) (hl : 0 < l) (s : Finset (Fin N × Fin N))
    (h : ∀ p ∈ s, U p.1 - U p.2 ≤ (M : ℤ)) :
    ∑ p ∈ s, Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat ≤ s.card * Nat.log l M ∧
      (M ≤ l → ∑ p ∈ s, Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat = 0) := by
  constructor
  · rw [← smul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    have := h p hp
    exact (maxVal_le_log_alt l _).trans (Nat.log_mono_right (by omega))
  · intro hM
    apply Finset.sum_eq_zero
    intro p hp
    apply Formalism.CohomologicalDescent.max_val_eq_zero_of_lt
    have := h p hp
    omega

theorem card_posPairs (N : ℕ) : (posPairs N).card = N.choose 2 := by
  have h1 : (posPairs N).card = ∑ b : Fin N, (Finset.Iio b).card := by
    unfold posPairs
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.card_filter]
    congr 1
    ext a
    simp
  rw [h1]
  simp only [Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id, Nat.choose_two_right]

theorem raising_exponent_interval : EExpInterval := by
  intro l N h U lo hl hU hr
  have h1 := sum_maxVal_le_card_mul_log U l h hl.pos (posPairs N) (by
    intro p _
    have h2 := hr p.1
    have h3 := hr p.2
    omega)
  rw [card_posPairs] at h1
  exact h1

theorem nat_le_mul_log_real (ex c l y : ℕ) (h : ex ≤ c * Nat.log l y) :
    (ex : ℝ) * Real.log l ≤ (c : ℝ) * Real.log y := by
  have h1 : (ex : ℝ) ≤ (c : ℝ) * (Nat.log l y : ℝ) := by exact_mod_cast h
  have h2 : 0 ≤ Real.log l := Real.log_natCast_nonneg l
  calc (ex : ℝ) * Real.log l ≤ (c : ℝ) * (Nat.log l y : ℝ) * Real.log l :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = (c : ℝ) * ((Nat.log l y : ℝ) * Real.log l) := by ring
    _ ≤ (c : ℝ) * Real.log y := mul_le_mul_of_nonneg_left (log_le_log_bound l y) (Nat.cast_nonneg c)

theorem sum_posPairs_split {N : ℕ} (k : ℕ) (g : Fin N × Fin N → ℕ) :
    ∑ p ∈ posPairs N, g p = ∑ p ∈ (posPairs N).filter (fun p => p.2.val < k), g p +
      ∑ p ∈ (posPairs N).filter (fun p => k ≤ p.1.val), g p +
      ∑ p ∈ (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val), g p := by
  have hlt : ∀ p ∈ posPairs N, p.1.val < p.2.val := fun p hp => (Finset.mem_filter.1 hp).2
  have hR : (posPairs N).filter (fun p => ¬ p.2.val < k ∧ k ≤ p.1.val) =
      (posPairs N).filter (fun p => k ≤ p.1.val) :=
    Finset.filter_congr fun p hp => by have := hlt p hp; omega
  have hC : (posPairs N).filter (fun p => ¬ p.2.val < k ∧ ¬ k ≤ p.1.val) =
      (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val) :=
    Finset.filter_congr fun p hp => by have := hlt p hp; omega
  rw [← Finset.sum_filter_add_sum_filter_not (posPairs N) (fun p => p.2.val < k),
    ← Finset.sum_filter_add_sum_filter_not ((posPairs N).filter (fun p => ¬ p.2.val < k))
      (fun p => k ≤ p.1.val), Finset.filter_filter, Finset.filter_filter, hR, hC, add_assoc]

theorem raising_split_three : ESplit3 := by
  intro N k l U
  exact sum_posPairs_split k _

def embedFinFirst {N k : ℕ} (hk : k ≤ N) : Fin k ↪ Fin N := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩

def embedFinLast (N k : ℕ) : Fin (N - k) ↪ Fin N :=
  ⟨fun a => ⟨k + a.val, by have := a.isLt; omega⟩, fun a b h => by
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)⟩

theorem posPairs_filter_lt {N k : ℕ} (hk : k ≤ N) :
    (posPairs N).filter (fun p => p.2.val < k) =
      (posPairs k).map ((embedFinFirst hk).prodMap (embedFinFirst hk)) := by
  ext ⟨a, b⟩
  simp only [posPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · rintro ⟨hab, hb⟩
    have hab' : a.val < b.val := hab
    exact ⟨(⟨a.val, by omega⟩, ⟨b.val, hb⟩), hab, rfl⟩
  · rintro ⟨⟨a', b'⟩, hab, h2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact ⟨hab, b'.isLt⟩

theorem posPairs_filter_ge {N k : ℕ} (hk : k ≤ N) :
    (posPairs N).filter (fun p => k ≤ p.1.val) =
      (posPairs (N - k)).map ((embedFinLast N k).prodMap (embedFinLast N k)) := by
  ext ⟨a, b⟩
  simp only [posPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · rintro ⟨hab, ha⟩
    have hab' : a.val < b.val := hab
    have ha2 := a.isLt
    have hb2 := b.isLt
    refine ⟨(⟨a.val - k, by omega⟩, ⟨b.val - k, by omega⟩), ?_, ?_⟩
    · show a.val - k < b.val - k
      omega
    · apply Prod.ext
      · apply Fin.ext
        show k + (a.val - k) = a.val
        omega
      · apply Fin.ext
        show k + (b.val - k) = b.val
        omega
  · rintro ⟨⟨a', b'⟩, hab, h2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    have hab' : a'.val < b'.val := hab
    refine ⟨?_, ?_⟩
    · show k + a'.val < k + b'.val
      omega
    · show k ≤ k + a'.val
      omega

theorem posPairs_filter_cross {N k : ℕ} (hk : k ≤ N) :
    (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val) =
      ((Finset.univ : Finset (Fin k)).map (embedFinFirst hk)) ×ˢ
        ((Finset.univ : Finset (Fin (N - k))).map (embedFinLast N k)) := by
  ext ⟨a, b⟩
  simp only [posPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Finset.mem_product]
  constructor
  · rintro ⟨-, ha, hb⟩
    have hb2 := b.isLt
    refine ⟨⟨⟨a.val, ha⟩, rfl⟩, ⟨⟨b.val - k, by omega⟩, ?_⟩⟩
    apply Fin.ext
    show k + (b.val - k) = b.val
    omega
  · rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩
    have := a'.isLt
    refine ⟨?_, ?_, ?_⟩
    · show a'.val < k + b'.val
      omega
    · exact a'.isLt
    · show k ≤ k + b'.val
      omega

theorem choose_split_alt : ChooseSplit := by
  intro N k hk
  have h1 : ((posPairs N).filter (fun p => p.2.val < k)).card = k.choose 2 := by
    rw [posPairs_filter_lt hk, Finset.card_map, card_posPairs]
  have h2 : ((posPairs N).filter (fun p => k ≤ p.1.val)).card = (N - k).choose 2 := by
    rw [posPairs_filter_ge hk, Finset.card_map, card_posPairs]
  have h3 : ((posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val)).card = k * (N - k) := by
    rw [posPairs_filter_cross hk, Finset.card_product, Finset.card_map, Finset.card_map,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  refine ⟨?_, h1, h2, h3⟩
  have h4 := sum_posPairs_split (N := N) k (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h4
  rw [card_posPairs, h1, h2, h3] at h4
  exact h4.symm

theorem three_bounds : ThreeBounds := by
  intro l N k h S eta xm lo U hl sh
  obtain ⟨-, c1, c2, c3⟩ := choose_split_alt N k sh.k_le
  have hlt : ∀ p ∈ posPairs N, p.1.val < p.2.val := fun p hp => (Finset.mem_filter.1 hp).2
  have b1 := sum_maxVal_le_card_mul_log U l S hl.pos ((posPairs N).filter (fun p => p.2.val < k)) (by
    intro p hp
    rw [Finset.mem_filter] at hp
    have h0 := hlt p hp.1
    have h1 := sh.cloudIn p.1 (by omega)
    have h2 := sh.cloudIn p.2 hp.2
    omega)
  have b2 := sum_maxVal_le_card_mul_log U l eta hl.pos ((posPairs N).filter (fun p => k ≤ p.1.val)) (by
    intro p hp
    rw [Finset.mem_filter] at hp
    have h0 := hlt p hp.1
    have h1 := sh.restIn p.1 hp.2
    have h2 := sh.restIn p.2 (by omega)
    omega)
  have b3 := sum_maxVal_le_card_mul_log U l h hl.pos
    ((posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val)) (by
    intro p _
    have h1 := sh.inRange p.1
    have h2 := sh.inRange p.2
    omega)
  rw [c1] at b1
  rw [c2] at b2
  rw [c3] at b3
  exact ⟨b1.1, b1.2, b2.1, b2.2, b3.1, Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))⟩

theorem real_log_mono_of_le (a : ℕ) (b : ℝ) (hab : (a : ℝ) ≤ b) (hb : 0 ≤ Real.log b) :
    Real.log a ≤ Real.log b := by
  by_cases h0 : a = 0
  · rw [h0]
    simpa using hb
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h0) hab

theorem choose_two_le_sq (N : ℕ) : (N.choose 2 : ℝ) ≤ (N : ℝ) ^ 2 := by
  rw [Nat.cast_choose_two]
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

theorem size_large : SizeLarge := by
  intro l N k h S eta ex m t xm lo U hl sh hex heta hmt
  obtain ⟨b1, -, -, b2, b3, -⟩ := three_bounds l N k h S eta xm lo U hl sh
  have h0 := raising_split_three N k l U
  rw [b2 heta] at h0
  constructor
  · have e1 := nat_le_mul_log_real _ _ _ _ b1
    have e3 := nat_le_mul_log_real _ _ _ _ b3
    have hex' : (ex : ℝ) ≤ (eCl U k l : ℝ) + (eCross U k l : ℝ) := by
      have : ex ≤ eCl U k l + eCross U k l := by omega
      exact_mod_cast this
    have hl0 : 0 ≤ Real.log l := Real.log_natCast_nonneg l
    push_cast at e3
    nlinarith [mul_le_mul_of_nonneg_right hex' hl0]
  · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
    have l1 : 0 ≤ Real.log (3 * (h : ℝ)) := by
      have := Real.log_natCast_nonneg (3 * h)
      push_cast at this
      exact this
    have l2 : 0 ≤ Real.log ((S : ℝ) + k) := by
      have := Real.log_natCast_nonneg (S + k)
      push_cast at this
      exact this
    have a1 : Real.log h ≤ Real.log (3 * (h : ℝ)) := real_log_mono_of_le h _ (by linarith) l1
    have a2 : Real.log S ≤ Real.log ((S : ℝ) + k) := real_log_mono_of_le S _ (by linarith) l2
    have a3 : ((N - k : ℕ) : ℝ) ≤ (m : ℝ) + t := by exact_mod_cast hmt
    have a4 : (k : ℝ) * ((N - k : ℕ) : ℝ) ≤ (k : ℝ) * ((m : ℝ) + t) :=
      mul_le_mul_of_nonneg_left a3 hk0
    have a5 := mul_le_mul a4 a1 (Real.log_natCast_nonneg h) (by positivity)
    have a6 := mul_le_mul (choose_two_le_sq k) a2 (Real.log_natCast_nonneg S) (by positivity)
    linarith

theorem maxVal_thirteen_eq_sup (n : ℕ) (hn : n < 169) :
    Formalism.RankGapBounds.JumpSetsAlt.maxVal 13 n =
      (Finset.range (n + 1)).sup fun i => if 13 ≤ i % 13 + (n - i) % 13 then 1 else 0 := by
  unfold Formalism.RankGapBounds.JumpSetsAlt.maxVal
  apply Finset.sup_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hlog : Nat.log 13 n < 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · exact Nat.log_lt_of_lt_pow hpos.ne' (by norm_num; exact hn)
  rw [Nat.factorization_choose (by norm_num : Nat.Prime 13) hi' hlog]
  have h12 : Finset.Ico 1 2 = {1} := by decide
  rw [h12, Finset.filter_singleton]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (by simpa using h1) h2
  · exact absurd (by simpa using h2) h1
  · rfl

theorem witness_thirteen : ExponentBoundCounterexample := by
  constructor
  · unfold eExp
    have h : ∀ p ∈ posPairs 24, Formalism.RankGapBounds.JumpSetsAlt.maxVal 13
        (((46 : ℤ) - 2 * (p.1.val : ℤ)) - ((46 : ℤ) - 2 * (p.2.val : ℤ)) - 1).toNat = _ :=
      fun p _ => maxVal_thirteen_eq_sup _ (by
        have h1 := p.1.isLt
        have h2 := p.2.isLt
        omega)
    rw [Finset.sum_congr rfl h]
    decide +kernel
  · norm_num

theorem polyBC_tmul (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (r n : ℕ) (a : O)
    (f : MvPolynomial (Fin r × Fin n) R) :
    polyBC R O r n (a ⊗ₜ[R] f) = a • map (algebraMap R O) f :=
  MvPolynomial.algebraTensorAlgEquiv_tmul R O a f

theorem map_baseChange_polyBC_eq_span (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (r n : ℕ)
    (q : Submodule R (MvPolynomial (Fin r × Fin n) R)) :
    (q.baseChange O).map (polyBC R O r n).toLinearMap =
      Submodule.span O (map (algebraMap R O) '' (q : Set (MvPolynomial (Fin r × Fin n) R))) := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨f, hf, ?_⟩
    have h := polyBC_tmul R O r n 1 f
    rw [one_smul] at h
    exact h.symm
  · rintro ⟨f, hf, rfl⟩
    refine ⟨_, ⟨f, hf, rfl⟩, ?_⟩
    have h := polyBC_tmul R O r n 1 f
    rw [one_smul] at h
    exact h

theorem map_algebraMap_smul_alt (R O : Type) [CommRing R] [CommRing O] [Algebra R O] {σ : Type} (a : R)
    (f : MvPolynomial σ R) :
    map (algebraMap R O) (a • f) = algebraMap R O a • map (algebraMap R O) f := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, map_C, ← MvPolynomial.smul_eq_C_mul]

theorem map_mem_weyl_alt (R O : Type) [CommRing R] [CommRing O] [Algebra R O] {r n : ℕ} (hn : n ≤ r)
    (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) :
    map (algebraMap R O) f ∈ weyl O r n hn ν := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨w, rfl⟩ := hg
    simp only
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
    exact la_word_mem O hn ν w
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_algebraMap_smul_alt]
    exact Submodule.smul_mem _ _ hx

theorem lattice_tensor : LatticeTensor := by
  intro R O _ _ _ r n hn ν
  constructor
  · rw [map_baseChange_polyBC_eq_span]
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨f, hf, rfl⟩
      exact map_mem_weyl_alt R O hn ν f hf
    · apply Submodule.span_le.2
      rintro _ ⟨w, rfl⟩
      apply Submodule.subset_span
      refine ⟨applyWord R w (hw R hn ν), la_word_mem R hn ν w, ?_⟩
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
  · intro _
    rw [map_baseChange_polyBC_eq_span]
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨f, hf, rfl⟩
      exact dualWeylMap R O (algebraMap R O) r n ν f hf
    · rw [standardMonomialSpanDomain O r n ν]
      apply Submodule.span_le.2
      rintro _ ⟨K, sz, hsz, I, hshape, rfl⟩
      apply Submodule.subset_span
      exact ⟨bideterminant R sz hsz I, hshape ▸ bidetMem R r n K sz hsz I, ldlat_map_bidet _ sz hsz I⟩

theorem lattice_baseChange_alt : LatticeBaseChange := by
  intro R O _ _ _ _ _ r n hn ν t e
  obtain ⟨hW, hD⟩ := lattice_tensor R O r n hn ν
  have hD := hD inferInstance
  rw [map_baseChange_polyBC_eq_span] at hD
  constructor
  · intro h x hx
    rw [← hD] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      rw [← map_pow, ← map_algebraMap_smul_alt]
      exact map_mem_weyl_alt R O hn ν _ (h f hf)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  · intro h
    set p : Submodule R (MvPolynomial (Fin r × Fin n) R) :=
      (dualWeyl R r n ν).map (LinearMap.lsmul R _ (t ^ e)) with hp
    have h1 : p.baseChange O ≤ (weyl R r n hn ν).baseChange O := by
      rw [← Submodule.map_le_map_iff_of_injective (polyBC R O r n).injective, hW,
        map_baseChange_polyBC_eq_span]
      apply Submodule.span_le.2
      rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      have h2 := h _ (dualWeylMap R O (algebraMap R O) r n ν f hf)
      rw [← map_pow, ← map_algebraMap_smul_alt] at h2
      exact h2
    have h3 : p ≤ weyl R r n hn ν := Submodule.baseChange_le_iff.1 h1
    intro x hx
    exact h3 ⟨x, hx, rfl⟩

end Formalism.CohomologicalDescent.SL2BinomialLattices
