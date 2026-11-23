import Mathlib

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Adic

structure IsSys (l : ℕ) [Fact l.Prime] (A : ℕ → Type*) [∀ k, AddCommGroup (A k)] [∀ k, Module ℤ_[l] (A k)]
    (ρ : ∀ m n : ℕ, A m →+ A n) : Prop where
  smul : ∀ k (r : ℤ_[l]) (x : A k), r • x = (PadicInt.toZModPow k r).val • x
  id : ∀ m (x : A m), ρ m m x = x
  trans : ∀ m n p (x : A m), p ≤ n → n ≤ m → ρ n p (ρ m n x) = ρ m p x
  bock : ∀ a b (z : A (a + b)), ρ (a + b) b z = 0 → l ^ a • z = 0 ∧ ∃ w : A a, ρ (a + b) a z = l ^ b • w
  fin : ∀ k, Finite (A k)

def konigF {B : ℕ → Type*} (π : ∀ m n, B m → B n) (hid : ∀ m w, π m m w = w)
    (htr : ∀ m n p w, p ≤ n → n ≤ m → π n p (π m n w) = π m p w)
    (P : ∀ m, B m → Prop) (hP : ∀ m n w, n ≤ m → P m w → P n (π m n w)) : ℕᵒᵖ ⥤ Type _ where
  obj m := {w : B m.unop // P m.unop w}
  map {m n} f := TypeCat.ofHom fun w => ⟨π m.unop n.unop w.1, hP _ _ _ (leOfHom f.unop) w.2⟩
  map_id m := by ext w; exact hid _ _
  map_comp {m n p} f g := by ext w; exact (htr _ _ _ _ (leOfHom g.unop) (leOfHom f.unop)).symm

theorem konig {B : ℕ → Type*} [∀ m, Finite (B m)] (π : ∀ m n, B m → B n) (hid : ∀ m w, π m m w = w)
    (htr : ∀ m n p w, p ≤ n → n ≤ m → π n p (π m n w) = π m p w)
    (P : ∀ m, B m → Prop) (hP : ∀ m n w, n ≤ m → P m w → P n (π m n w)) (hne : ∀ m, ∃ w, P m w) :
    ∃ y : ∀ m, B m, (∀ m, P m (y m)) ∧ ∀ m n, n ≤ m → π m n (y m) = y n := by
  have : ∀ j, Finite ((konigF π hid htr P hP).obj j) := fun j => Subtype.finite
  have : ∀ j, Nonempty ((konigF π hid htr P hP).obj j) := fun j =>
    let ⟨w, hw⟩ := hne j.unop
    ⟨⟨w, hw⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system (konigF π hid htr P hP)
  refine ⟨fun m => (s (Opposite.op m)).1, fun m => (s _).2, fun m n h => ?_⟩
  exact congrArg Subtype.val (hs (homOfLE h).op)

variable {l : ℕ} [Fact l.Prime] {A : ℕ → Type*} [∀ k, AddCommGroup (A k)] [∀ k, Module ℤ_[l] (A k)]
  {ρ : ∀ m n : ℕ, A m →+ A n} {S : Submodule ℤ_[l] (∀ k, A k)}

namespace IsSys

section Basic
variable (hA : IsSys l A ρ)
include hA

theorem pow_nsmul_eq_zero {k : ℕ} (x : A k) : l ^ k • x = 0 := by
  have h := hA.smul k ((l : ℤ_[l]) ^ k) x
  have h0 : PadicInt.toZModPow k ((l : ℤ_[l]) ^ k) = 0 := by
    rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  rw [h0, ZMod.val_zero, zero_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at h
  exact h

theorem nsmul_mod {n : ℕ} (a : ℕ) (y : A n) : a • y = (a % l ^ n) • y := by
  conv_lhs => rw [← Nat.mod_add_div a (l ^ n)]
  rw [add_nsmul, mul_comm, mul_nsmul, hA.pow_nsmul_eq_zero]
  simp

theorem map_smul {m n : ℕ} (h : n ≤ m) (r : ℤ_[l]) (x : A m) : ρ m n (r • x) = r • ρ m n x := by
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  rw [hA.smul m, hA.smul n, map_nsmul, hA.nsmul_mod (PadicInt.toZModPow m r).val]
  congr 1
  rw [← PadicInt.cast_toZModPow n m h r, ZMod.cast_eq_val, ZMod.val_natCast]

theorem exists_sec (P : ∀ m, A m → Prop) (hP : ∀ m n w, n ≤ m → P m w → P n (ρ m n w)) (hne : ∀ m, ∃ w, P m w) :
    ∃ y : ∀ m, A m, (∀ m, P m (y m)) ∧ ∀ m, ρ (m + 1) m (y (m + 1)) = y m := by
  have := hA.fin
  obtain ⟨y, hy, hy'⟩ := konig (fun m n => ρ m n) hA.id hA.trans P hP hne
  exact ⟨y, hy, fun m => hy' _ _ (Nat.le_succ m)⟩

end Basic

variable (hA : IsSys l A ρ) (hS : ∀ x, x ∈ S ↔ ∀ k, ρ (k + 1) k (x (k + 1)) = x k)
include hA hS

theorem compat {x : ∀ k, A k} (hx : x ∈ S) {m n : ℕ} (h : n ≤ m) : ρ m n (x m) = x n := by
  induction m, h using Nat.le_induction with
  | base => exact hA.id _ _
  | succ m hnm ih => rw [← hA.trans (m + 1) m n _ hnm (Nat.le_succ m), (hS x).1 hx m, ih]

theorem ker {x : ∀ k, A k} (hx : x ∈ S) (k : ℕ) (h0 : x k = 0) : ∃ y ∈ S, x = ((l : ℤ_[l]) ^ k) • y := by
  obtain ⟨y, hy, hy'⟩ := hA.exists_sec (fun m w => l ^ k • w = x m)
    (fun m n w h hw => by
      rw [← map_nsmul, hw, hA.compat hS hx h])
    (fun m => by
      obtain ⟨-, w, hw⟩ := hA.bock m k (x (m + k)) (by rw [hA.compat hS hx (Nat.le_add_left k m), h0])
      exact ⟨w, by rw [← hw, hA.compat hS hx (Nat.le_add_right m k)]⟩)
  refine ⟨y, (hS y).2 hy', funext fun m => ?_⟩
  rw [Pi.smul_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hy m]

theorem mem_span_of {I : Type*} [Fintype I] (g : I → ∀ k, A k) (hg : ∀ i, g i ∈ S)
    (h1 : ∀ x ∈ S, ∃ n ∈ Submodule.span ℤ_[l] (Set.range g), x 1 = n 1) {x : ∀ k, A k} (hx : x ∈ S) :
    x ∈ Submodule.span ℤ_[l] (Set.range g) := by
  set N := Submodule.span ℤ_[l] (Set.range g) with hN
  have hNS : N ≤ S := Submodule.span_le.2 (Set.range_subset_iff.2 hg)
  have step : ∀ x ∈ S, ∃ n ∈ N, ∃ y ∈ S, x = n + (l : ℤ_[l]) • y := by
    intro x hx
    obtain ⟨n, hn, hn1⟩ := h1 x hx
    obtain ⟨y, hy, hxy⟩ := hA.ker hS (S.sub_mem hx (hNS hn)) 1 (by rw [Pi.sub_apply, hn1, sub_self])
    refine ⟨n, hn, y, hy, ?_⟩
    rw [pow_one] at hxy
    rw [← hxy]
    abel
  have iter : ∀ m, ∀ x ∈ S, ∃ n ∈ N, ∃ y ∈ S, x = n + ((l : ℤ_[l]) ^ m) • y := by
    intro m
    induction m with
    | zero => exact fun x hx => ⟨0, N.zero_mem, x, hx, by simp⟩
    | succ m ih =>
      intro x hx
      obtain ⟨n, hn, y, hy, rfl⟩ := ih x hx
      obtain ⟨n', hn', y', hy', rfl⟩ := step y hy
      refine ⟨n + ((l : ℤ_[l]) ^ m) • n', N.add_mem hn (N.smul_mem _ hn'), y', hy', ?_⟩
      rw [smul_add, smul_smul, ← pow_succ, add_assoc]
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨c, hc, hc'⟩ := konig (B := fun m => I → ZMod (l ^ m))
    (fun m n c i => ((c i).val : ZMod (l ^ n)))
    (fun m c => funext fun i => ZMod.natCast_zmod_val _)
    (fun m n p c hpn hnm => funext fun i => by
      rw [ZMod.val_natCast]
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).2 (Nat.mod_mod_of_dvd _ (pow_dvd_pow l hpn)))
    (fun m c => ∑ i, (c i).val • g i m = x m)
    (fun m n c hnm hc => by
      rw [← hA.compat hS hx hnm, ← hc, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_nsmul, hA.compat hS (hg i) hnm, ZMod.val_natCast, ← hA.nsmul_mod])
    (fun m => by
      obtain ⟨n, hn, y, hy, hxy⟩ := iter m x hx
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hn
      refine ⟨fun i => PadicInt.toZModPow m (a i), ?_⟩
      rw [hxy, Pi.add_apply, Pi.smul_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hA.pow_nsmul_eq_zero, add_zero,
        ← ha, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, hA.smul])
  have hdiv : ∀ i m, (l : ℤ) ^ m ∣ ((c (m + 1) i).val : ℤ) - ((c m i).val : ℤ) := by
    intro i m
    have e := congrFun (hc' (m + 1) m (Nat.le_succ m)) i
    have e2 : (c m i).val = (c (m + 1) i).val % l ^ m := by rw [← e, ZMod.val_natCast]
    have h := Nat.mod_add_div (c (m + 1) i).val (l ^ m)
    refine ⟨((c (m + 1) i).val / l ^ m : ℕ), ?_⟩
    rw [e2]
    have h' := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h' ⊢
    linarith
  let a : I → ℤ_[l] := fun i =>
    PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun m => ((c m i).val : ℤ)) l (hdiv i))
  have ha : ∀ i m, PadicInt.toZModPow m (a i) = c m i := by
    intro i m
    rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hdiv i
  refine (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).2 ⟨a, funext fun m => ?_⟩
  rw [Finset.sum_apply, ← hc m]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, hA.smul, ha]

theorem finite : Module.Finite ℤ_[l] S := by
  classical
  have := hA.fin 1
  let _ : Fintype (A 1) := Fintype.ofFinite _
  let g : A 1 → ∀ k, A k := fun a => if h : ∃ x ∈ S, x 1 = a then h.choose else 0
  have hg : ∀ a, g a ∈ S := fun a => by
    simp only [g]
    split_ifs with h
    · exact h.choose_spec.1
    · exact S.zero_mem
  have hS' : S = Submodule.span ℤ_[l] (Set.range g) := by
    refine le_antisymm (fun x hx => hA.mem_span_of hS g hg (fun x hx => ⟨g (x 1), Submodule.subset_span ⟨_, rfl⟩, ?_⟩) hx)
      (Submodule.span_le.2 (Set.range_subset_iff.2 hg))
    have h : ∃ y ∈ S, y 1 = x 1 := ⟨x, hx, rfl⟩
    simp only [g, dif_pos h]
    exact h.choose_spec.2.symm
  rw [Module.Finite.iff_fg, hS']
  exact Submodule.fg_span (Set.finite_range g)

theorem ml (k : ℕ) : ∃ a, ∀ z : A (k + a), ∃ y ∈ S, y k = ρ (k + a) k z := by
  have := hA.fin k
  have anti : ∀ m n, k ≤ n → n ≤ m → Set.range (ρ m k) ⊆ Set.range (ρ n k) := by
    rintro m n hk hn _ ⟨z, rfl⟩
    exact ⟨ρ m n z, hA.trans _ _ _ _ hk hn⟩
  obtain ⟨a, ha⟩ : ∃ a, ∀ b, (Set.range (ρ (k + a) k)).ncard ≤ (Set.range (ρ (k + b) k)).ncard := by
    classical
    have hex : ∃ n, ∃ b, (Set.range (ρ (k + b) k)).ncard = n := ⟨_, 0, rfl⟩
    obtain ⟨b, hb⟩ := Nat.find_spec hex
    exact ⟨b, fun b' => hb ▸ Nat.find_min' hex ⟨b', rfl⟩⟩
  have stab : ∀ m, k + a ≤ m → Set.range (ρ (k + a) k) ⊆ Set.range (ρ m k) := by
    intro m hm
    have h1 := anti m (k + a) (by omega) hm
    have h2 : (Set.range (ρ (k + a) k)).ncard ≤ (Set.range (ρ m k)).ncard := by
      have := ha (m - k)
      rwa [show k + (m - k) = m by omega] at this
    rw [Set.eq_of_subset_of_ncard_le h1 h2]
  refine ⟨a, fun z => ?_⟩
  obtain ⟨y, hy, hy'⟩ := hA.exists_sec (fun m w => k ≤ m → ρ m k w = ρ (k + a) k z)
    (fun m n w h hw hk => by
      rw [hA.trans _ _ _ _ hk h, hw (hk.trans h)])
    (fun m => by
      rcases le_total m (k + a) with h | h
      · exact ⟨ρ (k + a) m z, fun hk => hA.trans _ _ _ _ hk h⟩
      · obtain ⟨w, hw⟩ := stab m h ⟨z, rfl⟩
        exact ⟨w, fun _ => hw⟩)
  refine ⟨y, (hS y).2 hy', ?_⟩
  have := hy k le_rfl
  rwa [hA.id] at this

theorem cyclic (h1 : ∃ g : A 1, ∀ x : A 1, ∃ n : ℤ, x = n • g) : ∃ g ∈ S, ∀ x ∈ S, ∃ c : ℤ_[l], x = c • g := by
  obtain ⟨g0, hg0⟩ := h1
  have : IsAddCyclic (A 1) := ⟨⟨g0, fun x => let ⟨n, hn⟩ := hg0 x; ⟨n, hn.symm⟩⟩⟩
  let φ : S →+ A 1 := { toFun := fun x => x.1 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  obtain ⟨⟨_, x0, rfl⟩, hgen⟩ := IsAddCyclic.exists_generator (α := φ.range)
  refine ⟨x0.1, x0.2, fun x hx => ?_⟩
  have key := hA.mem_span_of hS (I := Unit) (fun _ => x0.1) (fun _ => x0.2) (fun y hy => ?_) hx
  · rw [Set.range_const, Submodule.mem_span_singleton] at key
    obtain ⟨c, hc⟩ := key
    exact ⟨c, hc.symm⟩
  · obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (hgen ⟨φ ⟨y, hy⟩, ⟨y, hy⟩, rfl⟩)
    refine ⟨(n : ℤ_[l]) • x0.1, Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩), ?_⟩
    have e := congrArg Subtype.val hn
    rw [Pi.smul_apply, Int.cast_smul_eq_zsmul]
    exact e.symm

end IsSys

end CrystallineSemistableComparison.Adic
