import Development.EtaleCohomology.KummerTheory.AdicLimPf

noncomputable section
open CategoryTheory Opposite GlobalTheory.EtC LateralTheory.KummerTheory

namespace LateralTheory.EWeil.AdicKerPf

theorem nz (l : ℕ) [Fact l.Prime] (k : ℕ) : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem comp (hA : A11) {l : ℕ} [Fact l.Prime] {E : Spc} {n i : ℤ} (y : Hl l E n i) (M m : ℕ) (h : m ≤ M) :
    red (l ^ M) (l ^ m) E n i (y.1 M) = y.1 m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => haveI := nz l m; exact (hA (l ^ m) (l ^ m) dvd_rfl E).2.2.1 n i (y.1 m)
  | succ d ih =>
    haveI := nz l (m + (d + 1))
    rw [← (hA (l ^ (m + (d + 1))) (l ^ (m + d)) (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ m)
      (pow_dvd_pow l (by omega)) n i (y.1 _)]
    rw [show red (l ^ (m + (d + 1))) (l ^ (m + d)) E n i (y.1 (m + (d + 1))) = y.1 (m + d) from y.2 (m + d)]
    exact ih

theorem smul_pow {l : ℕ} [Fact l.Prime] {E : Spc} {n i : ℤ} (m b : ℕ) (v : HtL l m E n i) :
    ((l : ℤ_[l]) ^ b) • v = (show Ht (l ^ m) E n i from (l ^ b : ℕ) • v) := by
  change PadicInt.toZModPow m ((l : ℤ_[l]) ^ b) • (show Ht (l ^ m) E n i from v) = _
  rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl

theorem AdicKer_of : LateralTheory.KummerTheory.AdicKer := by
  intro hA l _ E i hB hFin n b x hx
  change x.1 b = 0 at hx
  obtain ⟨u, d, hBk⟩ := hB b
  let S : ℕ → Type 1 := fun a => {w : Ht (l ^ a) E n i // u a n w = x.1 (b + a)}
  let f : ∀ a, S (a + 1) → S a := fun a w => ⟨red (l ^ (a + 1)) (l ^ a) E n i w.1, by
    rw [← (hBk a n).2.2.2.2.2 w.1, w.2]; exact x.2 (b + a)⟩
  let F : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence (X := S) fun a => TypeCat.ofHom (f a)
  haveI : ∀ j, Finite (F.obj j) := fun j => by
    haveI := hFin j.unop n
    exact (inferInstance : Finite (S j.unop))
  haveI : ∀ j, Nonempty (F.obj j) := fun j => by
    have h0 : red (l ^ (b + j.unop)) (l ^ b) E n i (x.1 (b + j.unop)) = 0 := by
      rw [comp hA x (b + j.unop) b (by omega)]; exact hx
    obtain ⟨w, hw⟩ := ((hBk j.unop n).1 (x.1 (b + j.unop))).1 h0
    exact ⟨(⟨w, hw⟩ : S j.unop)⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  let y : Hl l E n i := ⟨fun a => (show S a from s (op a)).1, fun a => by
    have := hs (homOfLE (Nat.le_succ a)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at this
    exact congrArg Subtype.val this⟩
  refine ⟨y, Subtype.ext (funext fun m => ?_)⟩
  change x.1 m = ((l : ℤ_[l]) ^ b) • y.1 m
  rw [smul_pow]
  rcases le_or_gt m b with h | h
  · have hxm : x.1 m = 0 := by
      rw [← comp hA x b m h]
      exact (congrArg (red (l ^ b) (l ^ m) E n i) hx).trans (map_zero _)
    rw [hxm]
    obtain ⟨c, hc⟩ := pow_dvd_pow l h
    change 0 = (l ^ b : ℕ) • (show Ht (l ^ m) E n i from y.1 m)
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ m)), hc, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_smul]
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h.le
    have h1 : u a n (y.1 a) = x.1 (b + a) := (show S a from s (op a)).2
    rw [← h1, ← comp hA y (b + a) a (by omega)]
    exact (hBk a n).2.2.2.1 (y.1 (b + a))

end LateralTheory.EWeil.AdicKerPf
