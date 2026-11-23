import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm

namespace GlobalTheory.Mem.UnipCocompact

section Abstract

variable {S : Type} [Ring S] {st : S →+ S}

def cay (M : ℕ) (y : S) : S := (1 + y) * ∑ j ∈ Finset.range M, y ^ j

theorem cay_unitary (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) {M : ℕ} {y : S}
    (h0 : y ^ M = 0) (hy : st y = -y) : st (cay M y) * cay M y = 1 ∧ cay M y * st (cay M y) = 1 := by
  have h1 : st 1 = 1 := GlobalTheory.TwoStepUnipotent.st_one hm hi
  unfold cay
  generalize hG : ∑ j ∈ Finset.range M, y ^ j = G
  have a1 : (1 - y) * G = 1 := by rw [← hG, mul_neg_geom_sum, h0, sub_zero]
  have a2 : G * (1 - y) = 1 := by rw [← hG, geom_sum_mul_neg, h0, sub_zero]
  have b1 : st G * (1 + y) = 1 := by
    have := congrArg st a1
    rwa [hm, map_sub, h1, hy, sub_neg_eq_add] at this
  have b2 : (1 + y) * st G = 1 := by
    have := congrArg st a2
    rwa [hm, map_sub, h1, hy, sub_neg_eq_add] at this
  have c1 : st ((1 + y) * G) * ((1 + y) * G) = 1 := by
    rw [hm, map_add, h1, hy]
    calc st G * (1 + -y) * ((1 + y) * G) = (st G * (1 + y)) * ((1 - y) * G) := by noncomm_ring
      _ = 1 := by rw [a1, b1, one_mul]
  have c2 : ((1 + y) * G) * ((1 - y) * st G) = 1 := by
    rw [mul_assoc, ← mul_assoc G, a2, one_mul, b2]
  refine ⟨c1, ?_⟩
  rw [left_inv_eq_right_inv c1 c2, c2]

theorem cay_sub {M : ℕ} {y : S} (h0 : y ^ M = 0) :
    cay M y - 1 - (y + y) = (y + y) * ∑ j ∈ Finset.range M, y ^ (j + 1) := by
  unfold cay
  have e : ∑ j ∈ Finset.range M, y ^ (j + 1) = y * ∑ j ∈ Finset.range M, y ^ j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => pow_succ' y j
  rw [e]
  generalize hG : ∑ j ∈ Finset.range M, y ^ j = G
  have a1 : (1 - y) * G = 1 := by rw [← hG, mul_neg_geom_sum, h0, sub_zero]
  calc (1 + y) * G - 1 - (y + y) = (y + y) * (y * G) + ((1 - y) * G - 1) + (y + y) * ((1 - y) * G - 1) := by
        noncomm_ring
    _ = _ := by rw [a1]; simp

theorem compact_mod_of_filtration [TopologicalSpace S] [IsTopologicalRing S] (S₀ : Subring S) (h : S) (K : Set S)
    (N : ℕ → AddSubgroup S) (p : ℕ → S →+ S) (m : ℕ) (hcont : Continuous st)
    (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (hh0 : h ∈ S₀) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    (hK : IsCompact K) (hcov : ∀ x, ∃ y ∈ S₀, x - y ∈ K)
    (hp : ∀ i, Continuous (p i)) (hpN : ∀ i x, p i x ∈ N i) (hpf : ∀ i, ∀ x ∈ N i, p i x = x)
    (hp0 : ∀ i, ∀ x ∈ S₀, p i x ∈ S₀) (hle : ∀ i, N (i + 1) ≤ N i)
    (hmul : ∀ i, ∀ x ∈ N i, ∀ y ∈ N i, x * y ∈ N (i + 1)) (hst : ∀ i, ∀ x ∈ N i, st x ∈ N i)
    (hz : ∀ x ∈ N m, x = 0) :
    ∃ K' : Set S, IsCompact K' ∧ (∀ g ∈ K', (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N 0) ∧
      ∀ g, (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N 0 →
        ∃ γ ∈ S₀, ((st γ * γ = 1 ∧ γ * st γ = 1) ∧ γ - 1 ∈ N 0) ∧ ∃ k ∈ K', g = γ * k := by
  have h1 : st 1 = 1 := GlobalTheory.TwoStepUnipotent.st_one hm hi
  have hsh : st h = h := GlobalTheory.TwoStepUnipotent.st_half hm hi hh hc
  have hhx : ∀ x, h * x + h * x = x := fun x => by rw [← add_mul, hh, one_mul]
  have hhN : ∀ i, ∀ x ∈ N i, h * x ∈ N i := fun i x hx => by
    have : h * x = p i (h * x) := by
      conv_lhs => rw [← hpf i x hx, ← hhx x, map_add, mul_add, hhx]
    rw [this]; exact hpN _ _
  have hle0 : ∀ i, N i ≤ N 0 := fun i => by
    induction i with
    | zero => exact le_rfl
    | succ i ih => exact (hle i).trans ih
  have hnil : ∀ y ∈ N 0, y ^ 2 ^ m = 0 := fun y hy => by
    have : ∀ k, y ^ 2 ^ k ∈ N k := fun k => by
      induction k with
      | zero => simpa using hy
      | succ k ih => rw [pow_succ, pow_mul, sq]; exact hmul _ _ ih _ ih
    exact hz _ (this m)
  have umul : ∀ g g' : S, (st g * g = 1 ∧ g * st g = 1) → (st g' * g' = 1 ∧ g' * st g' = 1) →
      (st (g * g') * (g * g') = 1 ∧ g * g' * st (g * g') = 1) := fun g g' u u' => by
    rw [hm]
    exact ⟨by rw [mul_assoc, ← mul_assoc (st g), u.1, one_mul, u'.1],
      by rw [mul_assoc, ← mul_assoc g', u'.2, one_mul, u.2]⟩
  have ust : ∀ g : S, (st g * g = 1 ∧ g * st g = 1) → (st (st g) * st g = 1 ∧ st g * st (st g) = 1) :=
    fun g u => by rw [hi]; exact u.symm
  have nmul : ∀ i (g g' : S), g - 1 ∈ N i → g' - 1 ∈ N i → g * g' - 1 ∈ N i := fun i g g' u u' => by
    have : g * g' - 1 = (g - 1) * (g' - 1) + (g - 1) + (g' - 1) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (hle i (hmul i _ u _ u')) u) u'
  have nlead : ∀ i (g g' x x' : S), g - 1 ∈ N i → g' - 1 ∈ N i → g - 1 - x ∈ N (i + 1) → g' - 1 - x' ∈ N (i + 1) →
      g * g' - 1 - (x + x') ∈ N (i + 1) := fun i g g' x x' u u' v v' => by
    have : g * g' - 1 - (x + x') = (g - 1) * (g' - 1) + (g - 1 - x) + (g' - 1 - x') := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (hmul i _ u _ u') v) v'
  have key : ∀ i ≤ m, ∃ K' : Set S, IsCompact K' ∧ (∀ g ∈ K', (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N 0) ∧
      ∀ g, (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N i →
        ∃ γ ∈ S₀, ((st γ * γ = 1 ∧ γ * st γ = 1) ∧ γ - 1 ∈ N 0) ∧ ∃ k ∈ K', g = γ * k := by
    intro i him
    induction him using Nat.decreasingInduction with
    | self =>
      have one : (st 1 * 1 = 1 ∧ 1 * st 1 = 1) ∧ (1 : S) - 1 ∈ N 0 := by simp [h1]
      refine ⟨{1}, isCompact_singleton, fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact one,
        fun g hg => ⟨1, one_mem _, one, 1, rfl, ?_⟩⟩
      rw [one_mul, ← sub_eq_zero]
      exact hz _ hg.2
    | of_succ i _ ih =>
      obtain ⟨K', hK', hU, hcov'⟩ := ih
      obtain ⟨q, hq⟩ : ∃ q : S → S, ∀ z, q z = h * (h * (p i z - st (p i z))) := ⟨_, fun _ => rfl⟩
      have qc : Continuous q := by
        rw [show q = fun z => h * (h * (p i z - st (p i z))) from funext hq]
        have := hp i
        fun_prop
      have qN : ∀ z, q z ∈ N i := fun z => by
        rw [hq]; exact hhN _ _ (hhN _ _ (sub_mem (hpN i z) (hst _ _ (hpN i z))))
      have qs : ∀ z, st (q z) = - q z := fun z => by
        rw [hq, hm, hm, hsh, map_sub, hi, ← hc, ← hc, ← mul_neg, ← mul_neg, neg_sub]
      have q0 : ∀ z ∈ S₀, q z ∈ S₀ := fun z hz => by
        rw [hq]; exact mul_mem hh0 (mul_mem hh0 (sub_mem (hp0 i z hz) (h0 _ (hp0 i z hz))))
      have qsub : ∀ z z', q (z - z') = q z - q z' := fun z z' => by
        simp only [hq, map_sub]; noncomm_ring
      obtain ⟨c, hcd⟩ : ∃ c : S → S, ∀ z, c z = cay (2 ^ m) (q z) := ⟨_, fun _ => rfl⟩
      have cc : Continuous c := by
        rw [show c = fun z => cay (2 ^ m) (q z) from funext hcd]
        unfold cay
        fun_prop
      have cu : ∀ z, st (c z) * c z = 1 ∧ c z * st (c z) = 1 := fun z => by
        rw [hcd]; exact cay_unitary hm hi (hnil _ (hle0 i (qN z))) (qs z)
      have cl : ∀ z, c z - 1 - (q z + q z) ∈ N (i + 1) := fun z => by
        rw [hcd, cay_sub (hnil _ (hle0 i (qN z)))]
        refine hmul _ _ (add_mem (qN z) (qN z)) _ (sum_mem fun j hj => ?_)
        clear hj
        induction j with
        | zero => simpa using qN z
        | succ j ih => rw [pow_succ]; exact hle i (hmul _ _ ih _ (qN z))
      have cN : ∀ z, c z - 1 ∈ N i := fun z => by
        simpa using add_mem (hle i (cl z)) (add_mem (qN z) (qN z))
      have c0 : ∀ z ∈ S₀, c z ∈ S₀ := fun z hz => by
        rw [hcd]
        exact mul_mem (add_mem (one_mem _) (q0 z hz)) (sum_mem fun j _ => pow_mem (q0 z hz) j)
      have sN : ∀ z, st (c z) - 1 ∈ N i := fun z => by
        simpa [h1] using hst _ _ (cN z)
      have sl : ∀ z, st (c z) - 1 - -(q z + q z) ∈ N (i + 1) := fun z => by
        have := hst _ _ (cl z)
        rwa [map_sub, map_sub, map_add, h1, qs, ← neg_add] at this
      refine ⟨(fun x : S × S => x.1 * c x.2) '' (K' ×ˢ K), (hK'.prod hK).image (by fun_prop), ?_, ?_⟩
      · rintro _ ⟨⟨k, z⟩, ⟨hk, -⟩, rfl⟩
        exact ⟨umul _ _ (hU k hk).1 (cu z), nmul _ _ _ (hU k hk).2 (hle0 i (cN z))⟩
      · rintro g ⟨u, hg⟩
        obtain ⟨y, hy, hyK⟩ := hcov (g - 1)
        have gl : g - 1 - (q (g - 1) + q (g - 1)) ∈ N (i + 1) := by
          have e : g - 1 - (q (g - 1) + q (g - 1)) = -(h * (st (g - 1) * (g - 1))) := by
            rw [hq, hhx, hpf i _ hg, map_sub, h1]
            have : (st g - 1) * (g - 1) = -((g - 1) + (st g - 1)) := by
              rw [sub_mul, mul_sub, u.1]; noncomm_ring
            rw [this]
            generalize g - 1 = n
            generalize st g - 1 = n'
            calc n - h * (n - n') = (h * n + h * n) - h * (n - n') := by rw [hhx]
              _ = _ := by noncomm_ring
          rw [e]
          exact neg_mem (hhN _ _ (hmul _ _ (hst _ _ hg) _ hg))
        have t := nlead i _ _ _ _ (nmul i _ _ (sN y) hg) (sN (g - 1 - y)) (nlead i _ _ _ _ (sN y) hg (sl y) gl) (sl (g - 1 - y))
        have e : -(q y + q y) + (q (g - 1) + q (g - 1)) + -(q (g - 1 - y) + q (g - 1 - y)) = 0 := by
          rw [qsub (g - 1) y]; abel
        rw [e, sub_zero] at t
        obtain ⟨γ, hγ, uγ, k, hk, hgk⟩ := hcov' _ ⟨umul _ _ (umul _ _ (ust _ (cu y)) u) (ust _ (cu (g - 1 - y))), t⟩
        refine ⟨c y * γ, mul_mem (c0 y hy) hγ, ⟨umul _ _ (cu y) uγ.1, nmul _ _ _ (hle0 i (cN y)) uγ.2⟩,
          _, ⟨(k, g - 1 - y), ⟨hk, hyK⟩, rfl⟩, ?_⟩
        calc g = (c y * st (c y)) * g * (st (c (g - 1 - y)) * c (g - 1 - y)) := by rw [(cu _).1, (cu _).2, one_mul, mul_one]
          _ = c y * (st (c y) * g * st (c (g - 1 - y))) * c (g - 1 - y) := by simp only [mul_assoc]
          _ = _ := by rw [hgk]; simp only [mul_assoc]
  exact key 0 (Nat.zero_le m)

variable {ι : Type} [Fintype ι] (ε : ι → S) (w : ι → ℤ)

def raise (i : ℕ) : AddSubgroup S where
  carrier := {x | ∀ a b, w a ≤ w b + i → ε a * x * ε b = 0}
  zero_mem' := by simp
  add_mem' hx hy a b hab := by rw [mul_add, add_mul, hx a b hab, hy a b hab, add_zero]
  neg_mem' hx a b hab := by rw [mul_neg, neg_mul, hx a b hab, neg_zero]

variable {ε w}

theorem raise_mul (he : CompleteOrthogonalIdempotents ε) (i : ℕ) {x y : S} (hx : x ∈ raise ε w i) (hy : y ∈ raise ε w i) :
    x * y ∈ raise ε w (i + 1) := fun a b hab => by
  have : ε a * (x * y) * ε b = ∑ c, (ε a * x * ε c) * (ε c * y * ε b) := by
    calc ε a * (x * y) * ε b = ε a * x * (∑ c, ε c) * y * ε b := by rw [he.complete]; simp only [mul_one, mul_assoc]
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        conv_lhs => rw [← (he.idem c).eq]
        simp only [mul_assoc]
  rw [this]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : w a ≤ w c + i
  · rw [hx a c h, zero_mul]
  · rw [hy c b (by push_cast at hab; omega), mul_zero]

omit [Fintype ι] in
theorem raise_le (i : ℕ) : raise ε w (i + 1) ≤ raise ε w i := fun _ hx a b hab => hx a b (by push_cast; omega)

omit [Fintype ι] in
theorem raise_st (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : ∀ a, ∃ a', st (ε a) = ε a' ∧ w a' = - w a) (i : ℕ) {x : S} (hx : x ∈ raise ε w i) : st x ∈ raise ε w i :=
  fun a b hab => by
    obtain ⟨a', ha, wa⟩ := hs a
    obtain ⟨b', hb, wb⟩ := hs b
    have := congrArg st (hx b' a' (by omega))
    rwa [hm, hm, ← ha, ← hb, hi, hi, map_zero, ← mul_assoc] at this

theorem compact_mod_of_weights [TopologicalSpace S] [IsTopologicalRing S] (S₀ : Subring S) (h : S) (K : Set S)
    (hcont : Continuous st) (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (hh0 : h ∈ S₀) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    (hK : IsCompact K) (hcov : ∀ x, ∃ y ∈ S₀, x - y ∈ K) (he : CompleteOrthogonalIdempotents ε)
    (he0 : ∀ a, ε a ∈ S₀) (hs : ∀ a, ∃ a', st (ε a) = ε a' ∧ w a' = - w a) :
    ∃ K' : Set S, IsCompact K' ∧ (∀ g ∈ K', (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ raise ε w 0) ∧
      ∀ g, (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ raise ε w 0 →
        ∃ γ ∈ S₀, ((st γ * γ = 1 ∧ γ * st γ = 1) ∧ γ - 1 ∈ raise ε w 0) ∧ ∃ k ∈ K', g = γ * k := by
  classical
  obtain ⟨m, hmb⟩ : ∃ m : ℕ, ∀ a b, w a ≤ w b + m := by
    obtain ⟨M, hM⟩ := (Set.finite_range fun ab : ι × ι => (w ab.1 - w ab.2).toNat).bddAbove
    refine ⟨M, fun a b => ?_⟩
    have : (w a - w b).toNat ≤ M := hM ⟨(a, b), rfl⟩
    omega
  have hall : ∀ x, ∑ ab : ι × ι, ε ab.1 * x * ε ab.2 = x := fun x => by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, he.complete, mul_one, one_mul]
  let p : ℕ → S →+ S := fun i =>
    { toFun := fun x => ∑ ab ∈ Finset.univ.filter (fun ab : ι × ι => ¬ w ab.1 ≤ w ab.2 + i), ε ab.1 * x * ε ab.2
      map_zero' := by simp
      map_add' := fun x y => by simp only [mul_add, add_mul, Finset.sum_add_distrib] }
  refine compact_mod_of_filtration S₀ h K (raise ε w) p m hcont hm hi h0 hh0 hh hc hK hcov (fun i => ?_) (fun i x => ?_)
    (fun i x hx => ?_) (fun i x hx => ?_) raise_le (fun i x hx y hy => raise_mul he i hx hy)
    (fun i x hx => raise_st hm hi hs i hx) (fun x hx => ?_)
  · exact continuous_finsetSum _ fun ab _ => by fun_prop
  · refine sum_mem fun ab hab a b h' => ?_
    have hab' := (Finset.mem_filter.1 hab).2
    by_cases ea : a = ab.1
    · have eb : ab.2 ≠ b := fun eb => hab' (by rw [eb, ← ea]; exact h')
      rw [mul_assoc, mul_assoc _ (ε ab.2), he.ortho eb, mul_zero, mul_zero]
    · rw [← mul_assoc, ← mul_assoc, he.ortho ea, zero_mul, zero_mul, zero_mul]
  · refine Eq.trans ?_ (hall x)
    exact Finset.sum_filter_of_ne fun ab _ hne h' => hne (hx _ _ h')
  · exact sum_mem fun ab _ => mul_mem (mul_mem (he0 _) hx) (he0 _)
  · rw [← hall x]
    exact Finset.sum_eq_zero fun ab _ => hx _ _ (hmb _ _)

variable {κ : Type} [Fintype κ]

def fam (st : S →+ S) (u : κ → S) : Option (κ ⊕ κ) → S :=
  fun x => x.elim (1 - ∑ j, Sum.elim u (fun j => st (u j)) j) (Sum.elim u fun j => st (u j))

def wt (d : κ → ℕ) (M : ℕ) : Option (κ ⊕ κ) → ℤ :=
  fun x => x.elim 0 (Sum.elim (fun j => (M : ℤ) - d j) fun j => (d j : ℤ) - M)

theorem fam_complete (hm : ∀ x y, st (x * y) = st y * st x) {u : κ → S} (hu : OrthogonalIdempotents u)
    (h13 : ∀ i j, u i * st (u j) = 0) (h31 : ∀ i j, st (u i) * u j = 0) : CompleteOrthogonalIdempotents (fam st u) := by
  refine CompleteOrthogonalIdempotents.option ⟨?_, ?_⟩
  · rintro (j | j)
    · exact hu.idem j
    · exact (hm _ _).symm.trans (congrArg st (hu.idem j).eq)
  · rintro (i | i) (j | j) hij
    · exact hu.ortho fun e => hij (congrArg _ e)
    · exact h13 i j
    · exact h31 i j
    · refine (hm _ _).symm.trans ?_
      rw [hu.ortho (fun e => hij (congrArg _ e.symm)), map_zero]

theorem fam_st (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) (u : κ → S) (d : κ → ℕ) (M : ℕ) :
    ∀ a, ∃ a', st (fam st u a) = fam st u a' ∧ wt d M a' = - wt d M a := by
  rintro (_ | j | j)
  · refine ⟨none, ?_, by simp [wt]⟩
    simp [fam, GlobalTheory.TwoStepUnipotent.st_one hm hi, hi, add_comm]
  · exact ⟨some (.inr j), rfl, by simp [wt]⟩
  · exact ⟨some (.inl j), hi _, by simp [wt]⟩

theorem mem_raise_fam (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) {u : κ → S}
    (he : CompleteOrthogonalIdempotents (fam st u)) {d : κ → ℕ} {M : ℕ} (hd : ∀ j, d j < M) (x : S) :
    x ∈ raise (fam st u) (wt d M) 0 ↔ (1 - ∑ j, u j) * x * (1 - st (∑ j, u j)) = 0 ∧
      (∀ i j, d i ≤ d j → u j * x * u i = 0) ∧ ∀ i j, d i ≤ d j → u j * st x * u i = 0 := by
  classical
  have e1 : 1 - ∑ j, u j = fam st u none + ∑ j, fam st u (some (.inr j)) := by simp [fam]; abel
  have e3 : 1 - st (∑ j, u j) = fam st u none + ∑ j, fam st u (some (.inl j)) := by simp [fam]; abel
  have flip : ∀ i j, u j * st x * u i = 0 ↔ st (u i) * x * st (u j) = 0 := fun i j => by
    constructor
    · intro h
      have := congrArg st h
      rwa [hm, hm, hi, map_zero, ← mul_assoc] at this
    · intro h
      have := congrArg st h
      rwa [hm, hm, hi, hi, map_zero, ← mul_assoc] at this
  constructor
  · intro h
    refine ⟨?_, fun i j hij => h (some (.inl j)) (some (.inl i)) (by simp [wt]; omega),
      fun i j hij => (flip i j).2 (h (some (.inr i)) (some (.inr j)) (by simp [wt]; omega))⟩
    rw [e1, e3]
    simp only [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
    rw [h none none (by simp), Finset.sum_eq_zero fun j _ => h _ none (by have := hd j; simp [wt]; omega),
      Finset.sum_eq_zero fun j _ => ?_]
    · simp
    · rw [h none _ (by have := hd j; simp [wt]; omega),
        Finset.sum_eq_zero fun i _ => h _ _ (by have := hd j; have := hd i; simp [wt]; omega), add_zero]
  · rintro ⟨k1, k2, k3⟩
    have l1 : ∀ a, (∀ j, a ≠ some (.inl j)) → fam st u a * (1 - ∑ j, u j) = fam st u a := fun a ha => by
      rw [mul_sub, mul_one, Finset.mul_sum, sub_eq_self]
      exact Finset.sum_eq_zero fun j _ => he.ortho (ha j)
    have l3 : ∀ b, (∀ j, some (.inr j) ≠ b) → (1 - st (∑ j, u j)) * fam st u b = fam st u b := fun b hb => by
      rw [sub_mul, one_mul, map_sum, Finset.sum_mul, sub_eq_self]
      exact Finset.sum_eq_zero fun j _ => he.ortho (hb j)
    have l : ∀ a b, (∀ j, a ≠ some (.inl j)) → (∀ j, some (.inr j) ≠ b) → fam st u a * x * fam st u b = 0 :=
      fun a b ha hb => by
        rw [← l1 a ha, ← l3 b hb]
        calc _ = fam st u a * ((1 - ∑ j, u j) * x * (1 - st (∑ j, u j))) * fam st u b := by simp only [mul_assoc]
          _ = 0 := by rw [k1, mul_zero, zero_mul]
    rintro (_ | i | i) (_ | j | j) hab
    · exact l _ _ (by simp) (by simp)
    · exact l _ _ (by simp) (by simp)
    · have := hd j; simp [wt] at hab; omega
    · have := hd i; simp [wt] at hab; omega
    · exact k2 j i (by simp [wt] at hab; omega)
    · have := hd i; have := hd j; simp [wt] at hab; omega
    · exact l _ _ (by simp) (by simp)
    · exact l _ _ (by simp) (by simp)
    · exact (flip i j).1 (k3 i j (by simp [wt] at hab; omega))

end Abstract

section Concrete

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

theorem sandwich_eq_zero {A : Type} [CommRing A] {n r : ℕ} {C : Matrix (Fin n) (Fin r) A} {L : Matrix (Fin r) (Fin n) A}
    (hL : L * C = 1) (m : Matrix (Fin n) (Fin n) A) (i j : Fin r) :
    C * single j j (1 : A) * L * m * (C * single i i (1 : A) * L) = 0 ↔ (L * m * C) j i = 0 := by
  have e : C * single j j (1 : A) * L * m * (C * single i i (1 : A) * L) = C * single j i ((L * m * C) j i) * L := by
    have := Matrix.single_mul_mul_single j j i i (1 : A) (L * m * C) 1
    rw [one_mul, mul_one] at this
    rw [← this]; simp only [Matrix.mul_assoc]
  rw [e]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have := congrArg (fun X => (L * X * C) j i) h
  simp only [← Matrix.mul_assoc, hL, Matrix.one_mul] at this
  rw [Matrix.mul_assoc _ L C, hL] at this
  simpa using this

theorem triangular_inv {A : Type} [CommRing A] {r : ℕ} (d : Fin r → ℕ) (X Y : Matrix (Fin r) (Fin r) A)
    (h : Y = -X - Y * X) (hX : ∀ i j, d i ≤ d j → X j i = 0) : ∀ i j, d i ≤ d j → Y j i = 0 := by
  intro i
  induction hi : d i using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    intro j hij
    rw [h, Matrix.sub_apply, Matrix.neg_apply, hX i j (hi ▸ hij), Matrix.mul_apply, Finset.sum_eq_zero fun k _ => ?_]
    · simp
    · by_cases hk : d i ≤ d k
      · rw [hX i k hk, mul_zero]
      · rw [ih (d k) (by omega) k rfl j (by omega), zero_mul]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

theorem perp_iff_idem {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E)
    (hL : L * C = 1) (m : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E)) :
    (∀ x : Fin V.rank → E, (cT (hc.sig : E →+* E) C * V.gram) *ᵥ x = 0 →
        ∃ a, m *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = C.map (inclR (F := F) (AF F)) *ᵥ a) ↔
      (1 - (C * L).map (inclR (F := F) (AF F))) * m * (1 - adj hc V ((C * L).map (inclR (F := F) (AF F)))) = 0 := by
  rw [adj_map]
  set φ := inclR (F := F) (E := E) (AF F)
  have hL' : L.map φ * C.map φ = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : V.gram⁻¹ * cT (hc.sig : E →+* E) (C * L) * V.gram =
      V.gram⁻¹ * cT (hc.sig : E →+* E) L * (cT (hc.sig : E →+* E) C * V.gram) := by
    rw [cT_mul]; simp only [Matrix.mul_assoc]
  have hT : cT (hc.sig : E →+* E) C * V.gram * (V.gram⁻¹ * cT (hc.sig : E →+* E) L) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (gram_det_isUnit V), ← cT_mul, hL, cT_one]
  rw [e]
  generalize cT (hc.sig : E →+* E) C * V.gram = T at hT ⊢
  generalize V.gram⁻¹ * cT (hc.sig : E →+* E) L = P at hT ⊢
  have e1 : 1 - (P * T).map φ = (1 - P * T).map φ := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro h
    ext i k
    obtain ⟨a, ha⟩ := h (fun j => (1 - P * T : Matrix (Fin V.rank) (Fin V.rank) E) j k) (by
      have : T * (1 - P * T) = 0 := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.mul_one, Matrix.one_mul, sub_self]
      funext j; exact congrFun (congrFun this j) k)
    have h2 : (1 - (C * L).map φ) * C.map φ = 0 := by
      rw [Matrix.sub_mul, Matrix.map_mul, Matrix.mul_assoc, hL', Matrix.mul_one, Matrix.one_mul, sub_self]
    have h3 := congrArg ((1 - (C * L).map φ) *ᵥ ·) ha
    simp only [Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec] at h3
    rw [e1]
    exact congrFun h3 i
  · intro h x hx
    refine ⟨(L.map φ * m) *ᵥ fun i => φ (x i), ?_⟩
    have h1 : (T.map φ) *ᵥ (fun i => φ (x i)) = 0 := by
      funext i
      have := RingHom.map_mulVec φ T x i
      rw [hx] at this
      simpa [Function.comp_def] using this.symm
    have h2 := congrArg (· *ᵥ fun i => φ (x i)) h
    simp only [Matrix.zero_mulVec] at h2
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.map_mul (L := P),
      ← Matrix.mulVec_mulVec _ (P.map φ), h1, Matrix.mulVec_zero, sub_zero, Matrix.sub_mul, Matrix.one_mul,
      Matrix.sub_mulVec, sub_eq_zero, Matrix.map_mul, Matrix.mul_assoc] at h2
    rw [h2, Matrix.mulVec_mulVec]

def radSet {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (d : Fin r → ℕ) : Set (GA hc V) :=
  {g | (∀ i, ∃ a : Fin r → AF F ⊗[F] E, (∀ j, d i ≤ d j → a j = 0) ∧
      ((HA.mat _ hc.sig V.gram g).1 - 1) *ᵥ (fun k => inclR (F := F) (AF F) (C k i)) = C.map (inclR (F := F) (AF F)) *ᵥ a) ∧
    ∀ x : Fin V.rank → E, (cT (hc.sig : E →+* E) C * V.gram) *ᵥ x = 0 →
      ∃ a, ((HA.mat _ hc.sig V.gram g).1 - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = C.map (inclR (F := F) (AF F)) *ᵥ a}

noncomputable def idem {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (j : Fin r) :
    Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E) := (C * single j j (1 : E) * L).map (inclR (F := F) (AF F))

theorem idem_eq {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (j : Fin r) :
    idem (F := F) V C L j = C.map (inclR (F := F) (AF F)) * single j j (1 : AF F ⊗[F] E) * L.map (inclR (F := F) (AF F)) := by
  rw [idem, Matrix.map_mul, Matrix.map_mul, Matrix.map_single, map_one]

theorem sum_idem {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) :
    ∑ j, idem (F := F) V C L j = (C * L).map (inclR (F := F) (AF F)) := by
  simp only [idem_eq]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one, Matrix.map_mul]

theorem idem_complete {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (hL : L * C = 1)
    (h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0) (hLL : L * V.gram⁻¹ * cT (hc.sig : E →+* E) L = 0) :
    CompleteOrthogonalIdempotents (fam (adj hc V) (idem V C L)) := by
  have e : ∀ j : Fin r, V.gram⁻¹ * cT (hc.sig : E →+* E) (C * single j j (1 : E) * L) * V.gram =
      V.gram⁻¹ * cT (hc.sig : E →+* E) L * cT (hc.sig : E →+* E) (single j j (1 : E)) *
        (cT (hc.sig : E →+* E) C * V.gram) := fun j => by
    rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
  have e2 : ∀ i j : Fin r, C * single i i (1 : E) * L * (C * single j j (1 : E) * L) = C * (single i i (1 : E) * single j j (1 : E)) * L :=
    fun i j => by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc L C, hL, Matrix.one_mul]
  refine fam_complete (adj_mul hc V) ⟨fun j => ?_, fun i j hij => ?_⟩ (fun i j => ?_) (fun i j => ?_)
  · show _ * _ = _
    rw [idem, ← Matrix.map_mul, e2, Matrix.single_mul_single_same, one_mul]
  · show _ * _ = _
    rw [idem, idem, ← Matrix.map_mul, e2, Matrix.single_mul_single_of_ne (h := hij)]
    simp
  · rw [idem, idem, adj_map, e, ← Matrix.map_mul]
    simp only [Matrix.mul_assoc] at hLL ⊢
    rw [← Matrix.mul_assoc V.gram⁻¹, ← Matrix.mul_assoc L, hLL]
    simp
  · rw [idem, idem, adj_map, e, ← Matrix.map_mul]
    simp only [Matrix.mul_assoc] at h0 ⊢
    rw [← Matrix.mul_assoc V.gram C, ← Matrix.mul_assoc (cT _ C), h0]
    simp

theorem adj_mat (g : GA hc V) : adj hc V (HA.mat _ hc.sig V.gram g).1 = (HA.mat _ hc.sig V.gram g⁻¹).1 := by
  have h := (adj_mul_self_iff hc V g.1).2 g.2
  exact (Units.inv_eq_of_mul_eq_one_left h).symm

theorem mem_radSet_iff {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (hL : L * C = 1)
    (h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0) (hLL : L * V.gram⁻¹ * cT (hc.sig : E →+* E) L = 0)
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M) (g : GA hc V) :
    g ∈ radSet hc V C d ↔ (HA.mat _ hc.sig V.gram g).1 - 1 ∈ raise (fam (adj hc V) (idem V C L)) (wt d M) 0 := by
  rw [mem_raise_fam (adj_mul hc V) (adj_adj hc V) (idem_complete hc V C L hL h0 hLL) hd, sum_idem,
    ← perp_iff_idem hc V C L hL, map_sub, adj_mat, GlobalTheory.TwoStepUnipotent.st_one (adj_mul hc V) (adj_adj hc V)]
  have hinv : (HA.mat _ hc.sig V.gram g⁻¹).1 * (HA.mat _ hc.sig V.gram g).1 = 1 := Units.inv_mul g.1
  unfold radSet
  rw [Set.mem_ofPred_eq]
  generalize (HA.mat _ hc.sig V.gram g⁻¹).1 = y at hinv ⊢
  generalize (HA.mat _ hc.sig V.gram g).1 = x at hinv ⊢
  set φ := inclR (F := F) (E := E) (AF F)
  have hL' : L.map φ * C.map φ = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have sw : ∀ (m : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E)) (i j : Fin r),
      idem V C L j * m * idem V C L i = 0 ↔ (L.map φ * m * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = 0 :=
    fun m i j => by rw [idem_eq, idem_eq]; exact sandwich_eq_zero hL' m i j
  simp only [sw]
  have co : ∀ (i : Fin r) (a : Fin r → AF F ⊗[F] E), (x - 1) *ᵥ (fun k => φ (C k i)) = C.map φ *ᵥ a → ∀ j, (L.map φ * (x - 1) * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = a j :=
    fun i a ha j => by
      have := congrArg (L.map φ *ᵥ ·) ha
      simp only [Matrix.mulVec_mulVec, hL', Matrix.one_mulVec] at this
      exact congrFun this j
  constructor
  · rintro ⟨h1, h2⟩
    have k : ∀ i j : Fin r, d i ≤ d j → (L.map φ * (x - 1) * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = 0 := fun i j hij => by
      obtain ⟨a, ha, ha'⟩ := h1 i
      rw [co i a ha', ha j hij]
    refine ⟨h2, k, triangular_inv d _ _ ?_ k⟩
    have e : (x - 1) * C.map φ = C.map φ * (L.map φ * (x - 1) * C.map φ) := by
      ext k i
      obtain ⟨a, -, ha'⟩ := h1 i
      rw [Matrix.mul_apply (M := C.map φ)]
      simp only [co i a ha']
      exact congrFun ha' k
    have e' : y - 1 = -(x - 1) - (y - 1) * (x - 1) := by
      rw [sub_mul, mul_sub, hinv]; noncomm_ring
    rw [Matrix.mul_assoc (L.map φ * (y - 1)), ← e]
    conv_lhs => rw [e']
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  · rintro ⟨h2, h1, -⟩
    refine ⟨fun i => ?_, h2⟩
    obtain ⟨a, ha⟩ := h2 (fun k => C k i) (funext fun j => congrFun (congrFun h0 j) i)
    exact ⟨a, fun j hij => by rw [← co i a ha, h1 i j hij], ha⟩

theorem closure_radSet_cocompact {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (hC : LinearIndependent E Cᵀ)
    (h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0) (d : Fin r → ℕ) :
    ∃ K : Set (Subgroup.closure (radSet hc V C d)), IsCompact K ∧
      ∀ n, ∃ γ ∈ (ratPts hc V).subgroupOf (Subgroup.closure (radSet hc V C d)), ∃ k ∈ K, n = γ * k := by
  obtain ⟨L, hL, hLL⟩ := exists_dual hc V C hC h0
  obtain ⟨M, hd⟩ : ∃ M, ∀ j, d j < M := by
    obtain ⟨M, hM⟩ := (Set.finite_range d).bddAbove
    exact ⟨M + 1, fun j => Nat.lt_succ_of_le (hM ⟨j, rfl⟩)⟩
  obtain ⟨K, hK, hKs⟩ := tens_cocompact (F := F) (E := E)
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have he := idem_complete hc V C L hL h0 hLL
  have hs := fam_st (adj_mul hc V) (adj_adj hc V) (idem (F := F) V C L) d M
  have h1 := GlobalTheory.TwoStepUnipotent.st_one (adj_mul hc V) (adj_adj hc V)
  have hcont : Continuous (adj hc V) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) hc.sig)).matrix_transpose).matrix_mul continuous_const
  have hst0 : ∀ x ∈ (φ.mapMatrix (m := Fin V.rank)).range, adj hc V x ∈ (φ.mapMatrix (m := Fin V.rank)).range := by
    rintro _ ⟨X, rfl⟩; exact ⟨_, (adj_map hc V X).symm⟩
  have hmem : ∀ g, g ∈ Subgroup.closure (radSet hc V C d) ↔
      (HA.mat _ hc.sig V.gram g).1 - 1 ∈ raise (fam (adj hc V) (idem V C L)) (wt d M) 0 := fun g => by
    refine ⟨fun hg => ?_, fun hg => Subgroup.subset_closure ((mem_radSet_iff hc V C L hL h0 hLL hd g).2 hg)⟩
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact (mem_radSet_iff hc V C L hL h0 hLL hd x).1 hx
    | one => exact (sub_self (1 : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E))).symm ▸ zero_mem _
    | mul x y _ _ hx hy =>
      have e : (HA.mat _ hc.sig V.gram (x * y)).1 = (HA.mat _ hc.sig V.gram x).1 * (HA.mat _ hc.sig V.gram y).1 := rfl
      rw [e]
      generalize (HA.mat _ hc.sig V.gram x).1 = a at hx ⊢
      generalize (HA.mat _ hc.sig V.gram y).1 = b at hy ⊢
      have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
      rw [this]
      exact add_mem (add_mem (raise_le 0 (raise_mul he 0 hx hy)) hx) hy
    | inv x _ hx =>
      have := raise_st (adj_mul hc V) (adj_adj hc V) hs 0 hx
      rwa [map_sub, adj_mat, h1] at this
  obtain ⟨K', hK', k1, k2⟩ := compact_mod_of_weights (st := adj hc V) (w := wt d M)
    (φ.mapMatrix (m := Fin V.rank)).range
    (Matrix.scalar _ (φ (1 / 2))) (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K) hcont
    (adj_mul hc V) (adj_adj hc V) hst0
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (by rw [← map_add, ← map_add, add_halves, map_one, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩) he
    (by
      have hu : ∀ j, idem (F := F) V C L j ∈ (φ.mapMatrix (m := Fin V.rank)).range := fun j => ⟨_, rfl⟩
      have hv : ∀ j : Fin r ⊕ Fin r, Sum.elim (idem (F := F) V C L) (fun j => adj hc V (idem V C L j)) j ∈
          (φ.mapMatrix (m := Fin V.rank)).range := by
        rintro (j | j)
        exacts [hu j, hst0 _ (hu j)]
      rintro (_ | j)
      exacts [sub_mem (one_mem _) (sum_mem fun j _ => hv j), hv j]) hs
  let lift : ∀ x : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E), (adj hc V x * x = 1 ∧ x * adj hc V x = 1) ∧
      x - 1 ∈ raise (fam (adj hc V) (idem V C L)) (wt d M) 0 → Subgroup.closure (radSet hc V C d) := fun x hx =>
    ⟨⟨⟨x, adj hc V x, hx.1.2, hx.1.1⟩, (adj_mul_self_iff hc V _).1 hx.1.1⟩, (hmem _).2 hx.2⟩
  let f : Subgroup.closure (radSet hc V C d) → _ := fun n => Units.embedProduct _ (HA.mat _ hc.sig V.gram n.1)
  have hf : Topology.IsInducing f :=
    Units.isInducing_embedProduct.comp (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  refine ⟨f ⁻¹' ((fun x => (x, MulOpposite.op (adj hc V x))) '' K'),
    hf.isCompact_preimage' (hK'.image (continuous_id.prodMk (MulOpposite.continuous_op.comp hcont))) ?_, fun n => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨lift x (k1 x hx), rfl⟩
  · have u := (adj_mul_self_iff hc V _).2 n.1.2
    obtain ⟨γ, ⟨a, ha⟩, p1, k, hk, p2⟩ := k2 (HA.mat _ hc.sig V.gram n.1).1 ⟨⟨u, mul_eq_one_comm.1 u⟩, (hmem _).1 n.2⟩
    obtain ⟨b, hb⟩ := hst0 γ ⟨a, ha⟩
    refine ⟨lift γ p1, ?_, lift k (k1 k hk), ⟨k, hk, rfl⟩, Subtype.ext (Subtype.ext (Units.ext p2))⟩
    have inj : Function.Injective (φ.mapMatrix (m := Fin V.rank)) := Matrix.map_injective inclA_injective
    have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, p1.1.2])
    refine ⟨⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, inj ?_⟩, Subtype.ext (Units.ext ha)⟩
    have hγ' : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) hc.sig) γ * V.gram.map φ * γ = V.gram.map φ := (lift γ p1).1.2
    rw [← ha] at hγ'
    rw [map_mul, map_mul]
    exact (congrArg (· * V.gram.map φ * a.map φ) (GlobalTheory.AutFunCounterexample.cT_map_gen hc.sig a).symm).trans hγ'

end Concrete

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem radicals_cocompact : ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e → (∃ K : Set (NFlag B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NFlagQ B e, ∃ k ∈ K, n = γ * k) ∧ (∃ K : Set (NI B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NIQ B e, ∃ k ∈ K, n = γ * k) := by
  intro D B ρ e he
  have key : ∀ (d : Fin ρ → ℕ) (H : Subgroup (GA D B)), H = Subgroup.closure (radSet D.sp.cm B e d) →
      ∃ K : Set H, IsCompact K ∧ ∀ n, ∃ γ ∈ (GQ B).subgroupOf H, ∃ k ∈ K, n = γ * k := by
    rintro d _ rfl
    rw [GlobalTheory.AutFunCompare.GQ_eq]
    exact closure_radSet_cocompact D.sp.cm B e he.1 he.2 d
  refine ⟨key Fin.val _ rfl, key (fun _ => 0) _ ?_⟩
  have hs : (NI B e : Set (GA D B)) = radSet D.sp.cm B e fun _ => 0 := by
    ext g
    rw [GlobalTheory.AutFunCompare.NI_eq, SetLike.mem_coe, GlobalTheory.AutFunCompare.mem_unipRad_colSpan]
    refine and_congr ⟨fun h i => ⟨0, fun _ _ => rfl, ?_⟩, fun h => ?_⟩ Iff.rfl
    · rw [Matrix.mulVec_zero]
      exact funext fun k => congrFun (congrFun h k) i
    · ext k i
      obtain ⟨a, ha, h'⟩ := h i
      rw [show a = 0 from funext fun j => ha j le_rfl, Matrix.mulVec_zero] at h'
      exact congrFun h' k
  rw [← hs, Subgroup.closure_eq]

end GlobalTheory.Mem.UnipCocompact
