import Mathlib
import Formalism.PieriBlockIdeals.LemmaWAssembled
import Formalism.PieriBlockIdeals.PieriColumnMinors.MinorValuationBoundHolds
import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightExchangeChainHolds

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

theorem le_sum_of_dvd_det_submatrix {R : Type*} [CommRing R] [IsDomain R] (π : R) (hπ : Prime π) {t n : ℕ}
    (Φ : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) (pos : Fin t → Fin n)
    (hinj : Function.Injective pos) (hpos : ∀ s j, b j = b (pos s) → j = pos s)
    (hΦ : Φ.BlockTriangular b) (al : Fin t → ℕ)
    (hdiag : ∀ s, ∃ u : Rˣ, Φ (pos s) (pos s) = (u : R) * π ^ al s) (c : ℕ)
    (hdvd : π ^ c ∣ (Φ.submatrix pos pos).det) : c ≤ ∑ s, al s := by
  have hbp : Function.Injective (b ∘ pos) := fun s s' hs => hinj (hpos s' (pos s) hs)
  have hdet := lw_det_inj (Φ.submatrix pos pos) (b ∘ pos) hΦ.submatrix hbp
  simp only [Matrix.submatrix_apply] at hdet
  choose u hu using hdiag
  rw [hdet, Finset.prod_congr rfl (fun s _ => hu s), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Units.coe_prod, Units.dvd_mul_left] at hdvd
  exact (pow_dvd_pow_iff hπ.ne_zero hπ.not_unit).1 hdvd

theorem map_cast_le_of_map_neg_mul_le (l : ℕ) (hl : l.Prime) (F : Type) [Field F] [CharP F l] (a : F) (ha : a ≠ 0)
    {α β : Type} (A : Multiset α) (B : Multiset β) (f : α → ℤ) (g : β → ℤ)
    (h : Multiset.map (fun x => -a * ((f x : ℤ) : F)) A ≤
      Multiset.map (fun y => -a * ((g y : ℤ) : F)) B) :
    Multiset.map (fun x => ((f x : ℤ) : ZMod l)) A ≤ Multiset.map (fun y => ((g y : ℤ) : ZMod l)) B := by
  haveI := Fact.mk hl
  let φ : ZMod l →+* F := ZMod.castHom (dvd_refl l) F
  have hφ : Function.Injective φ := φ.injective
  have hψ : Function.Injective (fun z : ZMod l => -a * φ z) := fun z w hzw =>
    hφ (mul_left_cancel₀ (neg_ne_zero.2 ha) hzw)
  rw [← Multiset.map_le_map_iff hψ, Multiset.map_map, Multiset.map_map]
  simpa [Function.comp_def, φ, map_intCast] using h

private lemma sub_one_mul_abs_kap_le {ι : Type} [Fintype ι] (σ : Equiv.Perm ι) (l h : ℕ) (hl : 2 ≤ l)
    (w kap : ι → ℤ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ (h : ℤ))
    (hd : ∀ i, 0 ≤ (l : ℤ) * kap (σ i) + w i - kap i ∧ (l : ℤ) * kap (σ i) + w i - kap i ≤ (h : ℤ))
    (i : ι) : ((l : ℤ) - 1) * |kap i| ≤ (h : ℤ) := by
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => |kap i|)
  have hσ : σ (σ.symm i₀) = i₀ := σ.apply_symm_apply i₀
  have h1 := hd (σ.symm i₀)
  rw [hσ] at h1
  have h2 := hw (σ.symm i₀)
  have hm : |kap (σ.symm i₀)| ≤ |kap i₀| := hi₀ (σ.symm i₀)
  have hl2 : (2 : ℤ) ≤ l := by exact_mod_cast hl
  have hl' : (0 : ℤ) ≤ (l : ℤ) - 1 := by linarith
  have key : (l : ℤ) * |kap i₀| ≤ |kap (σ.symm i₀)| + h := by
    rcases abs_cases (kap i₀) with ⟨e0, _⟩ | ⟨e0, _⟩ <;>
      rcases abs_cases (kap (σ.symm i₀)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;> rw [e0, e1] <;> nlinarith
  have h3 : ((l : ℤ) - 1) * |kap i₀| ≤ h := by nlinarith
  calc ((l : ℤ) - 1) * |kap i| ≤ ((l : ℤ) - 1) * |kap i₀| := mul_le_mul_of_nonneg_left (hi₀ i) hl'
    _ ≤ h := h3

theorem twisted_block_bounds : LemmaWAssembled := by
  intro ι _ σ l h t n F _ _ W U' bot kap c hl hW hb hd
  obtain ⟨ha, hinj, hpos, hΘ, hchar, hdiag, hΦ, hΦd, hc⟩ := hW
  have hbp : Function.Injective (W.b ∘ W.pos) := fun s s' hs => hinj (hpos s' (W.pos s) hs)
  refine ⟨?_, ?_, ?_⟩
  · intro i s
    exact sub_one_mul_abs_kap_le σ l h hl.two_le (fun i => bot i + ((s : ℕ) : ℤ)) (fun i => kap i s)
      (fun i => hb i s) (fun i => hd i s) i
  · intro i
    have hdvd : ∏ s, (Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s))) ∣
        (W.Θ i).charpoly := by
      show _ ∣ (Matrix.charmatrix (W.Θ i)).det
      rw [(hΘ i).charmatrix.det]
      have e : ∏ s, (Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s))) =
          ∏ k ∈ Finset.univ.image (W.b ∘ W.pos),
            ((Matrix.charmatrix (W.Θ i)).toSquareBlock W.b k).det := by
        rw [Finset.prod_image (fun s _ s' _ hs => hbp hs)]
        refine Finset.prod_congr rfl fun s _ => ?_
        simp only [Function.comp_apply]
        rw [lw_det_block _ W.b (W.pos s) (hpos s), Matrix.charmatrix_apply_eq]
      rw [e]
      apply Finset.prod_dvd_prod_of_subset
      intro k hk
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply] at hk ⊢
      obtain ⟨s, rfl⟩ := hk
      exact ⟨W.pos s, rfl⟩
    have hne : (W.Θ i).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
    have hr := Polynomial.roots.le_of_dvd hne hdvd
    rw [hchar i] at hr
    have r1 : (∏ s, (Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s)))).roots =
        Multiset.map (fun s => W.Θ i (W.pos s) (W.pos s)) Finset.univ.val := by
      rw [Finset.prod_eq_multiset_prod]
      rw [show Multiset.map (fun s => Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s)))
          Finset.univ.val = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
            (Multiset.map (fun s => W.Θ i (W.pos s) (W.pos s)) Finset.univ.val) by
        rw [Multiset.map_map]; rfl]
      exact Polynomial.roots_multiset_prod_X_sub_C _
    have r2 : (∏ u, (Polynomial.X - Polynomial.C (-W.a * ((U' i u : ℤ) : F)))).roots =
        Multiset.map (fun u => -W.a * ((U' i u : ℤ) : F)) Finset.univ.val := by
      rw [Finset.prod_eq_multiset_prod]
      rw [show Multiset.map (fun u => Polynomial.X - Polynomial.C (-W.a * ((U' i u : ℤ) : F)))
          Finset.univ.val = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
            (Multiset.map (fun u => -W.a * ((U' i u : ℤ) : F)) Finset.univ.val) by
        rw [Multiset.map_map]; rfl]
      exact Polynomial.roots_multiset_prod_X_sub_C _
    rw [r1, r2] at hr
    have e2 : Multiset.map (fun s => W.Θ i (W.pos s) (W.pos s)) Finset.univ.val =
        Multiset.map (fun s : Fin t => -W.a * (((bot i + ((s : ℕ) : ℤ) - kap i s : ℤ)) : F))
          Finset.univ.val := Multiset.map_congr rfl (fun s _ => hdiag i s)
    rw [e2] at hr
    exact map_cast_le_of_map_neg_mul_le l hl F W.a ha Finset.univ.val Finset.univ.val
      (fun s : Fin t => bot i + ((s : ℕ) : ℤ) - kap i s) (U' i) hr
  · intro i
    have hm := le_sum_of_dvd_det_submatrix (PowerSeries.X : PowerSeries F) PowerSeries.X_prime (W.Φ i) W.b W.pos hinj
      hpos (hΦ i) (fun s => ((l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s).toNat)
      (hΦd i) (c i) (hc i)
    have hm' : ((c i : ℕ) : ℤ) ≤ ∑ s : Fin t,
        ((((l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s).toNat : ℕ) : ℤ) := by
      exact_mod_cast hm
    calc (c i : ℤ) ≤ _ := hm'
      _ = ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Int.toNat_of_nonneg (hd i s).1]
        ring

theorem weightExchangeFull_holds : WEFull := by
  intro ι _ σ k j t q l h F _ _ W U U' bot cst kap c τ hl hlt hW hb hd hU hU' hUb hprod hU0 hU'h
    hsum hblock hcτ
  obtain ⟨h1, h2, h3⟩ := twisted_block_bounds ι σ l h t (k + j + t + q) F W U' bot kap c hl hW hb hd
  have hκ : ∀ i s, |kap i s| ≤ ((h / (l - 1) : ℕ) : ℤ) := by
    intro i s
    have hl2 := hl.two_le
    have hpos : (0 : ℤ) < ((l - 1 : ℕ) : ℤ) := by omega
    have e : ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 := by omega
    rw [Int.natCast_div, Int.le_ediv_iff_mul_le hpos, e, mul_comm]
    exact h1 i s
  exact weightExchangeChain_holds k j t q l h (h / (l - 1)) F (U τ) (U' τ) (U (σ τ)) (U' (σ τ)) (bot τ)
    (bot (σ τ)) (cst τ) (cst (σ τ)) (kap τ) (kap (σ τ)) hl hlt (hU τ) (hU' τ) (hU (σ τ))
    (hU' (σ τ)) hU0 (fun a => (hU'h a).2) hsum hblock (hUb (σ τ)) (hprod τ) (hprod (σ τ))
    (hκ τ) (hκ (σ τ)) (h2 τ) (h2 (σ τ)) (by rw [← hcτ]; exact h3 τ)

end Formalism.CohomologicalDescent
