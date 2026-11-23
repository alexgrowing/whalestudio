import Formalism.WachLatticeTwists.StatementSplit
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelsOfBlockChiCOfBlockChiOne

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology

theorem split_sum_rows_columns_le (v : ℕ∞) (what₂ cols : Finset ℕ) (conj : ℕ → ℕ) (lenRow F G : ℕ → ℕ∞)
    (s R1 R2 R3 R4 R5 R6 : ℕ∞)
    (hk : v ≤ ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, F w + s + R1 + R2 + R3 + R4 + R5 + R6)
    (hrows : what₂ = cols.image conj) (hF : ∀ w ∈ cols, F w + lenRow (conj w) ≤ G w) :
    v ≤ ∑ w ∈ cols, G w + s + R1 + R2 + R3 + R4 + R5 + R6 := by
  refine hk.trans ?_
  have h1 : ∑ w ∈ what₂, lenRow w ≤ ∑ w ∈ cols, lenRow (conj w) := by
    rw [hrows]
    exact Finset.sum_image_le_of_nonneg (fun _ _ => bot_le)
  have h2 : ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, F w ≤ ∑ w ∈ cols, G w := by
    calc ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, F w
        ≤ ∑ w ∈ cols, lenRow (conj w) + ∑ w ∈ cols, F w := add_le_add h1 le_rfl
      _ = ∑ w ∈ cols, (F w + lenRow (conj w)) := by rw [Finset.sum_add_distrib, add_comm]
      _ ≤ ∑ w ∈ cols, G w := Finset.sum_le_sum hF
  gcongr

theorem split_summand_le (a x c h y1 y2 L : ℕ∞) (j n : ℕ) (hj : j ≤ n) (hL : L ≤ y1 + y2) :
    a + (j : ℕ∞) * x + c + h + L ≤ a + (n : ℕ∞) * x + c + h + y1 + y2 := by
  rw [add_assoc (a + (n : ℕ∞) * x + c + h)]
  have : (j : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hj
  gcongr

theorem theorem_five_split_of_bounds (hR : Formalism.RepresentationBoundsCohomology.StatRowColength.{0, 0}) (hH : Formalism.RepresentationBoundsCohomology.SubmoduleLengthBound.{0, 0})
    (hJC : Formalism.RepresentationBoundsCohomology.StatJumpsColumn.{0}) (hJR : Formalism.RepresentationBoundsCohomology.StatJumpsRow.{0}) : Formalism.RepresentationBoundsCohomology.LengthBoundViaSplitting := by
  intro O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' _ hdet Tc _ _ _ _ G _ r χ E e₁ δ ι _ _ colIdx hinj
    D j e' Kc k0 hE he₁ hloc g₀ n hspan π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ hcard hsize
    sE tE δO ℓ cB what₂ qs lenRow deg vζ s vhE H0 Sha hEsum hk0 NNc cols eO vδ N h0
    hb0E hb0δ hb0τ hb0iso hb0lift hb0loc hc2 hc1 conj nlam m c0 Mrow _ _ _ Irow
    cloudC lowsC cloudR lowsR h0C h0R hrows hlen hlift hH0 hJC' hJR'
  have key := Formalism.NG.n5 O X X' T T' Z p q b hT hZ d R' hdet Tc G r χ E e₁ δ ι colIdx hinj
    D j e' Kc k0 hE he₁ hloc g₀ n hspan π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard hsize
    sE tE δO ℓ cB what₂ qs lenRow deg vζ s vhE H0 Sha hEsum hk0
    hb0E hb0δ hb0τ hb0iso hb0lift hb0loc hc2 hc1
  have hper : ∀ w ∈ cols, j w ≤ nlam w * m ∧ lenRow (conj w) ≤
      ((nlam w * m : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) + N * ((c0 w : ℕ∞) * eO) := by
    intro w hw

    have hj : j w ≤ nlam w * m := by
      obtain ⟨h1, h2, h3, h4⟩ := hJC' w hw
      have := hJC (Fin (nlam w)) (cloudC w) (lowsC w) m (j w) (h0C w) h1 h2 h3 h4
      simpa [Fintype.card_fin] using this

    have hrk : Module.finrank O (Mrow (conj w)) ≤ nlam w * m := by
      obtain ⟨h1, h2, h3, h4⟩ := hJR' w hw
      have := hJR (Fin (nlam w)) (cloudR w) (lowsR w) m (Module.finrank O (Mrow (conj w))) (h0R w)
        h1 h2 h3 h4
      simpa [Fintype.card_fin] using this
    have hcol := hR O (Mrow (conj w)) (Irow (conj w)) ℓ (e' w) (hlift w hw)
    obtain ⟨H, hHk, hHt⟩ := hH0 w hw
    have htor := hH O {a // bl a = 0} H ℓ (c0 w) hHk
    have hL : lenRow (conj w) ≤
        ((nlam w * m : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) + N * ((c0 w : ℕ∞) * eO) := by
      rw [hlen w hw]
      refine hcol.trans ?_
      have hrk' : (Module.finrank O (Mrow (conj w)) : ℕ∞) ≤ ((nlam w * m : ℕ) : ℕ∞) := by
        exact_mod_cast hrk
      gcongr
      exact hHt.trans htor
    exact ⟨hj, hL⟩
  refine ⟨fun w hw => (hper w hw).1, fun w hw => (hper w hw).2, ?_⟩
  refine split_sum_rows_columns_le _ what₂ cols conj lenRow
    (fun w => eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w)
    (fun w => eO * (e' w : ℕ∞) + ((nlam w * m : ℕ) : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ +
          h0 w + ((nlam w * m : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) + N * ((c0 w : ℕ∞) * eO))
    _ _ _ _ _ _ _ key hrows ?_
  intro w hw
  exact split_summand_le _ _ _ _ _ _ _ (j w) (nlam w * m) (hper w hw).1 (hper w hw).2

end Formalism.RepresentationBoundsCohomology
