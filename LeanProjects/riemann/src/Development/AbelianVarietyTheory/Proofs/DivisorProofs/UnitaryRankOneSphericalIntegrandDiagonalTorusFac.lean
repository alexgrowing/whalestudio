import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.WeylCell.U21TorusFactor

open Formalism.UG

theorem swap_rev_comm {n : ℕ} (a i : Fin n) :
    Equiv.swap a a.rev i.rev = (Equiv.swap a a.rev i).rev := by
  rcases eq_or_ne i a with rfl | h1
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rcases eq_or_ne i a.rev with rfl | h2
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne]
  · exact fun h => h2 (by rw [← h, Fin.rev_rev])
  · exact fun h => h1 (Fin.rev_injective h)

theorem conj_diag_apply {R : Type} [CommRing R] {n : ℕ} (s : Equiv.Perm (Fin n))
    (Y Yi T : Matrix (Fin n) (Fin n) R) (hinv : Yi * Y = 1)
    (hY : ∀ i j, i ≠ s j → Y i j = 0) (hYi : ∀ i j, j ≠ s i → Yi i j = 0)
    (hT : ∀ i j, i ≠ j → T i j = 0) (i j : Fin n) :
    (Yi * T * Y) i j = if i = j then T (s i) (s i) else 0 := by
  have e1 : (Yi * T * Y) i j = Yi i (s j) * T (s j) (s j) * Y (s j) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
      · intro p _ hp; rw [hT p (s j) hp, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro r _ hr; rw [hY r j hr, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e1]
  split_ifs with hij
  · subst hij
    have e2 : (Yi * Y) i i = Yi i (s i) * Y (s i) i := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
      · intro p _ hp; rw [hY p i hp, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hinv, Matrix.one_apply_eq] at e2
    calc Yi i (s i) * T (s i) (s i) * Y (s i) i = T (s i) (s i) * (Yi i (s i) * Y (s i) i) := by ring
      _ = T (s i) (s i) := by rw [← e2, mul_one]
  · rw [hYi i (s j) (fun h => hij (s.injective h).symm), zero_mul, zero_mul]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_inv (z : L) : ordL z⁻¹ = -ordL z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [ordL]
  have h1 := GlobalTheory.BorelUMod.v_eq_exp (inv_ne_zero hz)
  rw [map_inv₀, GlobalTheory.BorelUMod.v_eq_exp hz, ← WithZero.exp_neg, WithZero.exp_inj] at h1
  linarith

theorem ordL_map {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (z : L) : ordL (σ z) = ordL z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz' : σ z ≠ 0 := (map_ne_zero σ).2 hz
  have h1 := hσ z
  rw [GlobalTheory.BorelUMod.v_eq_exp hz, GlobalTheory.BorelUMod.v_eq_exp hz', WithZero.exp_inj] at h1
  linarith

end GlobalTheory.WeylCell.U21TorusFactor

namespace GlobalTheory.WeylCell.U21TorusFactor

open Formalism.UG

theorem torus_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂˣ) (φ : GU σ n → ℂ), IsSphericalU q (fun i => (α i : ℂ)) φ →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → ∀ w x : GU σ n,
      φ (y⁻¹ * t * w * x) * (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
        chiDeltaU q (fun i => (actU k α i : ℂ)) t * φ (y⁻¹ * w * x) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw α φ hφ t ht w x
  have hσv : ∀ z, Valued.v (σ z) = Valued.v z := hU.2.1
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by
    rw [simpleU, if_neg hk]
  set a : Fin n := lo k with ha
  have hkv : k.val = n / 2 - 1 := by have := k.2; omega
  have hodd : n % 2 = 1 := by
    rcases Nat.even_or_odd n with h | h
    · exact absurd h hn
    · exact Nat.odd_iff.1 h
  have hav : a.val = k.val := rfl
  have hrv : (a.rev).val = n - 1 - k.val := by rw [Fin.val_rev, hav]; omega

  set Y : Matrix (Fin n) (Fin n) L := (((y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hYd
  set Yi : Matrix (Fin n) (Fin n) L := ((((y : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hYid
  set T : Matrix (Fin n) (Fin n) L := (((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTd
  have hinv : Yi * Y = 1 := by
    rw [hYid, hYd, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYw : ∀ i j, i ≠ Equiv.swap a a.rev j → Y i j = 0 := by
    intro i j h; rw [← hs] at h; exact hw i j h
  have hYi : ∀ i j, j ≠ Equiv.swap a a.rev i → Yi i j = 0 := by
    intro i j h
    have hm := (GlobalTheory.LGrp.mem_GU_iff σ n _).1 (y : GU σ n).2 i j
    rw [hYid, hm]
    have : j.rev ≠ Equiv.swap a a.rev i.rev := by
      rw [swap_rev_comm]; exact fun h' => h (Fin.rev_injective h')
    exact (congrArg σ (hYw _ _ this)).trans (map_zero σ)
  set b : GU σ n := y⁻¹ * t * y with hbd
  have hb : ∀ i j, (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      if i = j then T (Equiv.swap a a.rev i) (Equiv.swap a a.rev i) else 0 := by
    intro i j
    have : (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Yi * T * Y := by
      simp [hbd, hYid, hYd, hTd, Units.val_mul]
    rw [this]
    exact conj_diag_apply _ Y Yi T hinv hYw hYi ht i j
  have hB : IsBorelU b := by
    intro i j hij
    rw [hb, if_neg (ne_of_gt hij)]
  have hsph := hφ b (y⁻¹ * w * x) 1 hB (one_mem _)
  have hprod : y⁻¹ * t * w * x = b * (y⁻¹ * w * x) * 1 := by
    rw [hbd]; group

  have hTa : T a a ≠ 0 ∧ ordL (T a.rev a.rev) = -ordL (T a a) := by
    set Ti : Matrix (Fin n) (Fin n) L := ((((t : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTid
    have h1 : T * Ti = 1 := by
      rw [hTid, hTd, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : (T * Ti) a a = T a a * Ti a a := by
      rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · intro p _ hp; rw [ht a p (Ne.symm hp), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, Matrix.one_apply_eq] at h2
    have hne : T a a ≠ 0 := by intro h0; rw [h0, zero_mul] at h2; exact one_ne_zero h2
    have hTi : Ti a a = (T a a)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right h2.symm
    have hm := (GlobalTheory.LGrp.mem_GU_iff σ n _).1 (t : GU σ n).2 a a
    rw [← hTid, hTi] at hm
    refine ⟨hne, ?_⟩
    rw [← ordL_map hσv (T a.rev a.rev)]
    exact (congrArg ordL hm.symm).trans (ordL_inv _)

  have e : ∀ (β : Fin (n / 2) → ℂ) (g : GU σ n), chiDeltaU q β g =
      ∏ i : Fin (n / 2), β i ^ ordL ((((g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
        (q : ℂ) ^ (-(ordL ((((g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
          ((n : ℤ) - 1 - 2 * (i.val : ℤ))) := by
    intro β g
    unfold chiDeltaU
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dif_pos (by have := i.2; omega)]
    rfl
  have hact : ∀ i, (actU k α i : ℂ) = if i = k then (α k : ℂ)⁻¹ else α i := by
    intro i
    unfold actU
    rw [dif_neg hk]
    by_cases hi : i = k
    · subst hi; simp [Function.update_self, Units.val_inv_eq_inv_val]
    · simp [Function.update_of_ne hi, hi]
  have key : chiDeltaU q (fun i => (α i : ℂ)) b * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
    rw [e, e, Fintype.prod_eq_mul_prod_compl k, Fintype.prod_eq_mul_prod_compl k]
    have hrest : ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (α i : ℂ) ^ ordL ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ))) =
        ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (actU k α i : ℂ) ^ ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ))) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hik : i ≠ k := by simpa using hi
      have hfix : Equiv.swap a a.rev (lo i) = lo i := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; apply hik; ext; have := congrArg Fin.val h; simpa [ha] using this
        · intro h; have := congrArg Fin.val h; rw [hrv] at this
          have h3 : (lo i : Fin n).val = i.val := rfl
          have := i.2; omega
      rw [hb, if_pos rfl, hfix, hact, if_neg hik]
    rw [hrest, hb, if_pos rfl, ← ha, Equiv.swap_apply_left, hTa.2, hact, if_pos rfl]
    have hE : ((n : ℤ) - 1 - 2 * (k.val : ℤ)) = 2 := by omega
    rw [hE]
    set o := ordL (T a a)
    set R := ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (actU k α i : ℂ) ^ ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ)))
    have hqq : (q : ℂ) ^ (-(-o) * 2) * (q : ℂ) ^ (-4 * o) = (q : ℂ) ^ (-o * 2) := by
      rw [← zpow_add₀ hq]; ring_nf
    have hα : (α k : ℂ) ^ (-o) = ((α k : ℂ)⁻¹) ^ o := by rw [zpow_neg, inv_zpow]
    calc (α k : ℂ) ^ (-o) * (q : ℂ) ^ (-(-o) * 2) * R * (q : ℂ) ^ (-4 * o)
        = (α k : ℂ) ^ (-o) * ((q : ℂ) ^ (-(-o) * 2) * (q : ℂ) ^ (-4 * o)) * R := by ring
      _ = ((α k : ℂ)⁻¹) ^ o * (q : ℂ) ^ (-o * 2) * R := by rw [hqq, hα]
  rw [hprod, hsph]
  calc chiDeltaU q (fun i => (α i : ℂ)) b * φ (y⁻¹ * w * x) * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k)))
      = (chiDeltaU q (fun i => (α i : ℂ)) b * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k)))) * φ (y⁻¹ * w * x) := by ring
    _ = _ := by rw [key]

end GlobalTheory.WeylCell.U21TorusFactor
