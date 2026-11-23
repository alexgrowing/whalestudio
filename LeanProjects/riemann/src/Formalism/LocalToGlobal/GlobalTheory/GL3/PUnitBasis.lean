import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFourSq

noncomputable section
open scoped BigOperators
open Module

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS

variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

structure PLat (c : K →+* K) (h : V → V → K) (O : Subring K) (L : AddSubgroup V) (p : ℕ) : Prop where
  herm : Herm4 c h
  prime : p.Prime
  cO : ∀ t ∈ O, c t ∈ O
  smul : ∀ o ∈ O, ∀ x ∈ L, o • x ∈ L
  int : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ O
  unim : ∀ x, (∀ y ∈ L, h x y ∈ O) → x ∈ L
  full : ∀ x : V, ∃ n : ℕ, 0 < n ∧ (n : K) • x ∈ L
  nat : ∀ x ∈ L, ∃ n : ℕ, h x x = (n : K)
  crit : ∃ ω ∈ O, ∀ t ∈ O, (∃ k : ℤ, t + c t = (p : K) * k) → (∃ k : ℤ, ω * t + c (ω * t) = (p : K) * k) →
    ∃ t' ∈ O, t = (p : K) * t'

def Good (h : V → V → K) (L : AddSubgroup V) (p : ℕ) {ι : Type} (v : ι → V) (n : ι → ℕ) : Prop :=
  (∀ i, v i ∈ L) ∧ (∀ i, h (v i) (v i) = (n i : K)) ∧ (∀ i, ¬ p ∣ n i) ∧ ∀ i j, i ≠ j → h (v i) (v j) = 0

variable {c : K →+* K} {h : V → V → K} {O : Subring K} {L : AddSubgroup V} {p : ℕ}

theorem Herm4.zero_left (H : Herm4 c h) (y : V) : h 0 y = 0 := (H.hl y).map_zero

theorem Herm4.add_right (H : Herm4 c h) (x y z : V) : h x (y + z) = h x y + h x z := by
  rw [H.symm (y + z) x, H.add_left, map_add, ← H.symm, ← H.symm]

theorem Herm4.norm_add (H : Herm4 c h) (y z : V) :
    h (y + z) (y + z) = h y y + h y z + c (h y z) + h z z := by
  rw [H.add_left, H.add_right, H.add_right, H.symm y z]; ring

theorem PLat.proj (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} {n : ι → ℕ}
    (G : Good h L p v n) (x : V) (hx : x ∈ L) :
    ∃ x' ∈ L, (∀ j, h x' (v j) = 0) ∧ ∃ N : ℕ, Nat.Coprime N p ∧ N ≠ 0 ∧
      ((N : K) • x - x' ∈ Submodule.span K (Set.range v)) ∧
      ∀ y, (∀ i, h y (v i) = 0) → h x' y = (N : K) * h x y := by
  obtain ⟨gL, gn, gp, go⟩ := G
  have H := P.herm
  set S : V := ∑ i, (((∏ j ∈ Finset.univ.erase i, n j : ℕ) : K) * h x (v i)) • v i with hS
  have hSL : S ∈ L := AddSubgroup.sum_mem _ fun i _ =>
    P.smul _ (O.mul_mem (natCast_mem O _) (P.int _ hx _ (gL i))) _ (gL i)
  refine ⟨((∏ j, n j : ℕ) : K) • x - S, L.sub_mem (P.smul _ (natCast_mem O _) _ hx) hSL, ?_, ∏ j, n j, ?_, ?_, ?_, ?_⟩
  · intro j
    have e1 : h (((∏ j, n j : ℕ) : K) • x - S) (v j) = H.hl (v j) (((∏ j, n j : ℕ) : K) • x - S) := rfl
    rw [e1, map_sub, map_smul, hS, map_sum, Finset.sum_eq_single j]
    · rw [map_smul]
      show ((∏ j, n j : ℕ) : K) • h x (v j)
        - (((∏ i ∈ Finset.univ.erase j, n i : ℕ) : K) * h x (v j)) • h (v j) (v j) = 0
      rw [gn j, ← Finset.mul_prod_erase Finset.univ n (Finset.mem_univ j)]
      simp only [smul_eq_mul]
      push_cast; ring
    · intro i _ hij
      rw [map_smul]
      show _ • h (v i) (v j) = 0
      rw [go i j hij, smul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · exact Nat.Coprime.prod_left fun i _ => ((Nat.Prime.coprime_iff_not_dvd P.prime).2 (gp i)).symm
  · exact Finset.prod_ne_zero_iff.2 fun i _ hi => gp i (hi ▸ dvd_zero p)
  · rw [sub_sub_cancel]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro y hy
    have e1 : h (((∏ j, n j : ℕ) : K) • x - S) y = H.hl y (((∏ j, n j : ℕ) : K) • x - S) := rfl
    rw [e1, map_sub, map_smul, hS, map_sum, Finset.sum_eq_zero, sub_zero]
    · rfl
    · intro i _
      rw [map_smul]
      show _ • h (v i) y = 0
      rw [H.ortho_symm (hy i), smul_zero]

section Desc

variable (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} {n : ι → ℕ} (G : Good h L p v n)
  (hdiv : ∀ y ∈ L, (∀ i, h y (v i) = 0) → ∃ k : ℕ, h y y = (p : K) * k)
include P G hdiv

theorem PLat.pair_div (y z : V) (hy : y ∈ L) (hy' : ∀ i, h y (v i) = 0) (hz : z ∈ L) (hz' : ∀ i, h z (v i) = 0) :
    ∃ t' ∈ O, h y z = (p : K) * t' := by
  have H := P.herm
  have tr : ∀ y z : V, y ∈ L → (∀ i, h y (v i) = 0) → z ∈ L → (∀ i, h z (v i) = 0) →
      ∃ k : ℤ, h y z + c (h y z) = (p : K) * k := by
    intro y z hy hy' hz hz'
    obtain ⟨k1, e1⟩ := hdiv (y + z) (L.add_mem hy hz) (fun i => by rw [H.add_left, hy' i, hz' i, add_zero])
    obtain ⟨k2, e2⟩ := hdiv y hy hy'
    obtain ⟨k3, e3⟩ := hdiv z hz hz'
    have E0 := H.norm_add y z
    refine ⟨(k1 : ℤ) - k2 - k3, ?_⟩
    push_cast
    linear_combination e1 - E0 - e2 - e3
  obtain ⟨ω, hω, crit⟩ := P.crit
  refine crit _ (P.int _ hy _ hz) (tr y z hy hy' hz hz') ?_
  have := tr (ω • y) z (P.smul _ hω _ hy) (fun i => by rw [H.smul_left, hy' i, mul_zero]) hz hz'
  rwa [H.smul_left] at this

theorem PLat.div (y : V) (hy : y ∈ L) (hy' : ∀ i, h y (v i) = 0) :
    (p : K)⁻¹ • y ∈ L ∧ ∀ i, h ((p : K)⁻¹ • y) (v i) = 0 := by
  have H := P.herm
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast P.prime.ne_zero
  refine ⟨P.unim _ fun x hx => ?_, fun i => by rw [H.smul_left, hy' i, mul_zero]⟩
  obtain ⟨x', hx'L, hx'o, N, hcop, -, -, hform⟩ := P.proj G x hx
  obtain ⟨t', ht', e⟩ := P.pair_div G hdiv x' y hx'L hx'o hy hy'
  rw [hform y hy'] at e
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have habK : (a : K) * (N : K) + (b : K) * (p : K) = 1 := by exact_mod_cast hab
  have e2 : h x y = (p : K) * ((a : K) * t' + (b : K) * h x y) := by
    linear_combination (a : K) * e - (h x y) * habK
  have hmem : (a : K) * t' + (b : K) * h x y ∈ O :=
    O.add_mem (O.mul_mem (intCast_mem O a) ht') (O.mul_mem (intCast_mem O b) (P.int _ hx _ hy))
  rw [H.smul_left, H.symm x y, e2, map_mul, map_natCast, ← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
  exact P.cO _ hmem

theorem PLat.zero_of_div : ∀ (m : ℕ) (y : V), y ∈ L → (∀ i, h y (v i) = 0) → h y y = (m : K) → y = 0 := by
  have H := P.herm
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast P.prime.ne_zero
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro y hy hy' hm
    by_contra hne
    obtain ⟨h1, h2⟩ := P.div G hdiv y hy hy'
    obtain ⟨m', hm'⟩ := P.nat _ h1
    have e : h ((p : K)⁻¹ • y) ((p : K)⁻¹ • y) = (p : K)⁻¹ * ((p : K)⁻¹ * (m : K)) := by
      rw [H.smul_left, H.symm ((p : K)⁻¹ • y) y, H.smul_left, hm, map_mul, map_inv₀, map_natCast, map_natCast]
    have e2 : (m' : K) * (p : K) * (p : K) = (m : K) := by
      rw [← hm', e]; field_simp
    have e3 : m' * p * p = m := by exact_mod_cast e2
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero] at hm
      exact (H.pos y hne).1 hm
    have hp2 := P.prime.two_le
    have hlt : m' < m := by
      have hm'0 : 0 < m' := by
        rcases Nat.eq_zero_or_pos m' with h0 | h0
        · rw [h0] at e3; simp at e3; exact absurd e3.symm hm0
        · exact h0
      calc m' < m' * 2 * 2 := by omega
        _ ≤ m' * p * p := Nat.mul_le_mul (Nat.mul_le_mul_left _ hp2) hp2
        _ = m := e3
    have := ih m' hlt _ h1 h2 hm'
    rcases smul_eq_zero.1 this with h0 | h0
    · exact inv_ne_zero hp0 h0
    · exact hne h0

end Desc

theorem PLat.fam (P : PLat c h O L p) (m : ℕ) (hm : m ≤ finrank K V) :
    ∃ (v : Fin m → V) (n : Fin m → ℕ), Good h L p v n := by
  have H := P.herm
  induction m with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨v, n, G⟩ := ih (Nat.le_of_succ_le hm)
    have hne : Submodule.span K (Set.range v) ≠ ⊤ := by
      intro e
      have h1 := finrank_range_le_card (R := K) v
      rw [Set.finrank, e, finrank_top, Fintype.card_fin] at h1
      omega
    obtain ⟨x, hx⟩ : ∃ x, x ∉ Submodule.span K (Set.range v) := by
      by_contra hcon
      push Not at hcon
      exact hne (Submodule.eq_top_iff'.2 hcon)
    obtain ⟨k, hk, hkx⟩ := P.full x
    obtain ⟨x', hx'L, hx'o, N, -, hN, hspan, -⟩ := P.proj G _ hkx
    have hx'0 : x' ≠ 0 := by
      intro e
      rw [e, sub_zero, smul_smul] at hspan
      have hc : (N : K) * (k : K) ≠ 0 := mul_ne_zero (by exact_mod_cast hN) (by exact_mod_cast hk.ne')
      have := Submodule.smul_mem _ ((N : K) * (k : K))⁻¹ hspan
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      exact hx this
    by_cases hex : ∃ y ∈ L, (∀ i, h y (v i) = 0) ∧ ∃ ny : ℕ, h y y = (ny : K) ∧ ¬ p ∣ ny
    · obtain ⟨y, hyL, hyo, ny, hny, hpy⟩ := hex
      obtain ⟨gL, gn, gp, go⟩ := G
      refine ⟨Fin.cons y v, Fin.cons ny n, ?_, ?_, ?_, ?_⟩
      · intro i; refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hyL
        · simpa using gL i
      · intro i; refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hny
        · simpa using gn i
      · intro i; refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hpy
        · simpa using gp i
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
        · intro e; exact absurd rfl e
        · intro _; simpa using hyo j
        · intro _; simpa using H.ortho_symm (hyo i)
        · intro e
          have : i ≠ j := fun e' => e (congrArg Fin.succ e')
          simpa using go i j this
    · exfalso
      have hdiv : ∀ y ∈ L, (∀ i, h y (v i) = 0) → ∃ k : ℕ, h y y = (p : K) * k := by
        intro y hy hy'
        obtain ⟨ny, hny⟩ := P.nat y hy
        by_cases hd : p ∣ ny
        · obtain ⟨k, rfl⟩ := hd
          exact ⟨k, by rw [hny]; push_cast; ring⟩
        · exact absurd ⟨y, hy, hy', ny, hny, hd⟩ hex
      obtain ⟨nx, hnx⟩ := P.nat x' hx'L
      exact hx'0 (P.zero_of_div G hdiv nx x' hx'L hx'o hnx)

theorem PLat.basis (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = finrank K V) :
    ∃ (b : Basis ι K V) (n : ι → ℕ), Good h L p b n := by
  have H := P.herm
  obtain ⟨v, n, gL, gn, gp, go⟩ := P.fam (finrank K V) le_rfl
  let e : ι ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq hι
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i e0
    have h1 := gn i
    rw [e0, H.zero_left] at h1
    have : n i = 0 := by exact_mod_cast h1.symm
    exact gp i (this ▸ dvd_zero p)
  have hv' : ∀ i j : ι, i ≠ j → h (v (e i)) (v (e j)) = 0 := fun i j hij => go _ _ (fun e' => hij (e.injective e'))
  have hli : LinearIndependent K (fun i => v (e i)) := H.linInd _ (fun i => hv0 _) hv'
  have hsp := hli.span_eq_top_of_card_eq_finrank' hι
  refine ⟨Basis.mk hli (le_of_eq hsp.symm), fun i => n (e i), ?_, ?_, fun i => gp _, ?_⟩
  · intro i; rw [Basis.mk_apply]; exact gL _
  · intro i; rw [Basis.mk_apply]; exact gn _
  · intro i j hij; rw [Basis.mk_apply, Basis.mk_apply]; exact hv' i j hij

theorem qM_mem (O : Subring K) {p q r s : K} (hp : p ∈ O) (hq : q ∈ O) (hr : r ∈ O) (hs : s ∈ O) (β a : Fin 4) :
    qM p q r s β a ∈ O := by
  fin_cases β <;> fin_cases a <;> simp [qM, hp, hq, hr, hs]

theorem PLat.iso (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = finrank K V) :
    ∃ g : (Fin 4 → V) ≃ₗ[K] (Fin 4 × ι → K), (∀ x y, ∑ w, g x w * c (g y w) = ∑ a, h (x a) (y a)) ∧
      ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x : Fin 4 → V, (∀ a, x a ∈ L) → ∀ w, (s : K) * g x w ∈ O) ∧
        ∀ u : Fin 4 × ι → K, (∀ w, u w ∈ O) → ∀ a, (s : K) • g.symm u a ∈ L := by
  have H := P.herm
  obtain ⟨b, n, gL, gn, gp, go⟩ := P.basis hι
  choose a1 a2 a3 a4 h4 using fun i => Nat.sum_four_squares (n i)
  obtain ⟨g, hg, hform⟩ := H.iso_of b go (fun i => (a1 i : K)) (fun i => (a2 i : K)) (fun i => (a3 i : K))
    (fun i => (a4 i : K)) (fun i => map_natCast c _) (fun i => map_natCast c _) (fun i => map_natCast c _)
    (fun i => map_natCast c _) (fun i => by rw [gn i, ← h4 i]; push_cast; ring)
  have hn0 : ∀ i, (n i : K) ≠ 0 := by
    intro i e0
    have : n i = 0 := by exact_mod_cast e0
    exact gp i (this ▸ dvd_zero p)
  have hcop : Nat.Coprime (∏ j, n j) p :=
    Nat.Coprime.prod_left fun i _ => ((Nat.Prime.coprime_iff_not_dvd P.prime).2 (gp i)).symm
  have h1 : ∀ x : Fin 4 → V, (∀ a, x a ∈ L) → ∀ w, ((∏ j, n j : ℕ) : K) * g x w ∈ O := by
    intro x hx w
    rw [hform, Finset.mul_sum]
    refine O.sum_mem fun a _ => ?_
    have e : ((∏ j, n j : ℕ) : K) * b.repr (x a) w.2
        = ((∏ j ∈ Finset.univ.erase w.2, n j : ℕ) : K) * h (x a) (b w.2) := by
      rw [H.coord b go, gn, ← Finset.mul_prod_erase Finset.univ n (Finset.mem_univ w.2)]
      push_cast; ring
    have e' : ((∏ j, n j : ℕ) : K) * (qM (a1 w.2 : K) (a2 w.2 : K) (a3 w.2 : K) (a4 w.2 : K) w.1 a * b.repr (x a) w.2)
        = qM (a1 w.2 : K) (a2 w.2 : K) (a3 w.2 : K) (a4 w.2 : K) w.1 a *
          (((∏ j ∈ Finset.univ.erase w.2, n j : ℕ) : K) * h (x a) (b w.2)) := by
      rw [← e]; ring
    rw [e']
    exact O.mul_mem (qM_mem O (natCast_mem O _) (natCast_mem O _) (natCast_mem O _) (natCast_mem O _) _ _)
      (O.mul_mem (natCast_mem O _) (P.int _ (hx a) _ (gL _)))
  refine ⟨g, hg, ∏ j, n j, hcop, h1, ?_⟩
  intro u hu a
  refine P.unim _ fun y hy => ?_
  have e := hg (g.symm u) (Pi.single a y)
  rw [LinearEquiv.apply_symm_apply, Finset.sum_eq_single a] at e
  · rw [Pi.single_eq_same] at e
    rw [H.smul_left, ← e, Finset.mul_sum]
    refine O.sum_mem fun w _ => ?_
    have e2 : ((∏ j, n j : ℕ) : K) * (u w * c (g (Pi.single a y) w))
        = u w * c (((∏ j, n j : ℕ) : K) * g (Pi.single a y) w) := by
      rw [map_mul, map_natCast]; ring
    rw [e2]
    refine O.mul_mem (hu w) (P.cO _ (h1 _ ?_ w))
    intro a'
    by_cases ha : a' = a
    · subst ha; rwa [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne ha]; exact L.zero_mem
  · intro a' _ ha'
    rw [Pi.single_eq_of_ne ha', H.symm 0 _, H.zero_left, map_zero]
  · intro ha; exact absurd (Finset.mem_univ a) ha

namespace Test

theorem herm : Herm4 (RingHom.id ℚ) (fun x y : ℚ => x * y) where
  add_left x x' y := add_mul x x' y
  smul_left k x y := by simp [mul_assoc]
  symm x y := mul_comm y x
  pos x hx := ⟨mul_self_ne_zero.2 hx, x, 0, 0, 0, rfl, rfl, rfl, rfl, by ring⟩

theorem plat : PLat (RingHom.id ℚ) (fun x y : ℚ => x * y) (Int.castRingHom ℚ).range (Int.castAddHom ℚ).range 3 where
  herm := herm
  prime := Nat.prime_three
  cO t ht := ht
  smul := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨a * b, by simp⟩
  int := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨a * b, by simp⟩
  unim x h := by
    obtain ⟨a, ha⟩ := h 1 ⟨1, by simp⟩
    exact ⟨a, by simpa using ha⟩
  full x := ⟨x.den, x.den_pos, ⟨x.num, by simp [Rat.den_mul_eq_num]⟩⟩
  nat := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a.natAbs * a.natAbs, ?_⟩
    push_cast
    rw [Nat.cast_natAbs]
    push_cast
    simp
  crit := by
    refine ⟨1, one_mem _, ?_⟩
    rintro _ ⟨a, rfl⟩ ⟨k, hk⟩ -
    refine ⟨((a - k : ℤ) : ℚ), ⟨a - k, rfl⟩, ?_⟩
    simp only [eq_intCast, RingHom.id_apply, Nat.cast_ofNat] at hk ⊢
    push_cast
    linarith

end Test

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS

end
