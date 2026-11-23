import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen

namespace GlobalTheory.SenLines.Coords

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def zc (c : F⟦X⟧) (n : ℤ) : F := if 0 ≤ n then coeff n.toNat c else 0

theorem zc_nat (c : F⟦X⟧) (n : ℕ) : zc c n = coeff n c := by
  simp [zc]

theorem zc_neg (c : F⟦X⟧) {n : ℤ} (h : n < 0) : zc c n = 0 := by
  unfold zc
  rw [if_neg (not_le.mpr h)]

theorem zc_add (c c' : F⟦X⟧) (n : ℤ) : zc (c + c') n = zc c n + zc c' n := by
  unfold zc
  split_ifs <;> simp [map_add]

theorem zc_mul (f c : F⟦X⟧) (n : ℤ) (N : ℕ) (h : n < N) :
    zc (f * c) n = ∑ j ∈ Finset.range N, coeff j f * zc c (n - j) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [zc_neg _ hn]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [zc_neg _ (by omega), mul_zero]
  · lift n to ℕ using hn
    have hN : n < N := by exact_mod_cast h
    rw [zc_nat, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j c),
      ← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ N by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (n + 1) N) ?_, add_zero]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show ((n : ℤ) - (j : ℤ)) = ((n - j : ℕ) : ℤ) by omega, zc_nat]
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [zc_neg _ (by omega), mul_zero]

def lines {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c : Fin r → F⟦X⟧) : ℤ → M :=
  ∑ k, serLine (u k) (d k) (c k)

theorem lines_apply {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c : Fin r → F⟦X⟧) (m : ℤ) :
    lines u d c m = ∑ k, zc (c k) (m + u k) • d k := by
  unfold lines
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [serLine, zc]
  split_ifs <;> simp

theorem lines_add {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c c' : Fin r → F⟦X⟧) :
    lines u d (c + c') = lines u d c + lines u d c' := by
  funext m
  simp only [lines_apply, Pi.add_apply, zc_add, add_smul, Finset.sum_add_distrib]

theorem lines_zero {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) :
    lines u d (0 : Fin r → F⟦X⟧) = 0 := by
  funext m
  rw [lines_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : zc (0 : F⟦X⟧) (m + u k) = 0 := by
    unfold zc
    split_ifs <;> simp
  rw [Pi.zero_apply, this, zero_smul]

theorem lines_sum {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) {ι : Type} (s : Finset ι)
    (c : ι → Fin r → F⟦X⟧) : lines u d (∑ j ∈ s, c j) = ∑ j ∈ s, lines u d (c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, lines_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lines_add, ih]

theorem coeff_eq_of_apply {r : ℕ} (u : Fin r → ℤ) {d : Fin r → M} (hd : LinearIndependent F d)
    (c c' : Fin r → F⟦X⟧) (a : F) (m : ℤ) (h : lines u d c m = a • lines u d c' m) (k : Fin r) :
    zc (c k) (m + u k) = a * zc (c' k) (m + u k) := by
  rw [lines_apply, lines_apply, Finset.smul_sum] at h
  have h2 : ∑ k, (zc (c k) (m + u k) - a * zc (c' k) (m + u k)) • d k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [h, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hd _ h2 k)

theorem lines_injective {r : ℕ} (u : Fin r → ℤ) {d : Fin r → M} (hd : LinearIndependent F d) :
    Function.Injective (lines (F := F) u d) := by
  intro c c' h
  funext k
  ext n
  have := coeff_eq_of_apply u hd c c' 1 ((n : ℤ) - u k) (by rw [h, one_smul]) k
  rwa [sub_add_cancel, one_mul, zc_nat, zc_nat] at this

theorem serAct_lines {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (f : F⟦X⟧) (c : Fin r → F⟦X⟧) :
    serAct f (lines u d c) = lines u d (f • c) := by
  funext m
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k, m + u k < N := by
    refine ⟨(Finset.univ.sup fun k => (m + u k).toNat) + 1, fun k => ?_⟩
    have h1 : (m + u k).toNat ≤ Finset.univ.sup fun k => (m + u k).toNat :=
      Finset.le_sup (f := fun k => (m + u k).toNat) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (m + u k)
    push_cast
    omega
  have hsupp : (Function.support fun j : ℕ => coeff j f • lines u d c (m - j)) ⊆ ↑(Finset.range N) := by
    intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hjN
    apply hj
    rw [lines_apply, Finset.sum_eq_zero, smul_zero]
    intro k _
    rw [zc_neg _ (by have := hN k; omega), zero_smul]
  unfold serAct
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  simp_rw [lines_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [zc_mul f (c k) (m + u k) N (hN k), Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show m - (j : ℤ) + u k = m + u k - j by ring]

theorem exists_coords : ∀ {F M A N : Type} [Field F] [AddCommGroup M] [Module F M] [CommRing A] [AddCommGroup N] [Module A N] (lev : A → F⟦X⟧) (L : N →+ (ℤ → M)) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M), LinearIndependent F d → (∀ a x, L (a • x) = serAct (lev a) (L x)) → SpanIsLines L u d F → ∃ e : N →+ (Fin r → F⟦X⟧), (∀ a x, e (a • x) = lev a • e x) ∧ Submodule.span F⟦X⟧ (Set.range e) = ⊤ ∧ ∀ (χ : F) (x y : N), χ ≠ 0 → (∀ k : ℤ, L y k = χ ^ k • L x k) → ∀ k, e y k = C (χ ^ (-u k)) * rescale χ (e x k) := by
  intro F M A N _ _ _ _ _ _ lev L r u d hd hL hS
  have hex : ∀ x, ∃ c : Fin r → F⟦X⟧, L x = lines u d c := by
    intro x
    obtain ⟨c, hc⟩ := (hS (L x)).mp ⟨1, fun _ => x, fun _ => 1, by simp only [Fin.sum_univ_one, serAct_one]⟩
    exact ⟨c, hc⟩
  choose e he using hex
  have hinj := lines_injective (F := F) u hd
  have eadd : ∀ x y, e (x + y) = e x + e y := fun x y =>
    hinj (by rw [← he, lines_add, ← he, ← he, map_add])
  refine ⟨AddMonoidHom.mk' e eadd, ?_, ?_, ?_⟩
  · intro a x
    show e (a • x) = lev a • e x
    apply hinj
    rw [← he, hL, he x, serAct_lines]
  · rw [eq_top_iff]
    intro c _
    obtain ⟨s, x, f, hy⟩ := (hS (lines u d c)).mpr ⟨c, rfl⟩
    have hc : c = ∑ j, f j • e (x j) := by
      apply hinj
      rw [hy, lines_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [he, serAct_lines]
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x j, rfl⟩)
  · intro χ x y hχ hxy k
    show e y k = C (χ ^ (-u k)) * rescale χ (e x k)
    ext n
    have h1 : lines u d (e y) ((n : ℤ) - u k) = χ ^ ((n : ℤ) - u k) • lines u d (e x) ((n : ℤ) - u k) := by
      rw [← he, ← he]
      exact hxy _
    have h2 := coeff_eq_of_apply u hd (e y) (e x) _ _ h1 k
    rw [sub_add_cancel, zc_nat, zc_nat] at h2
    rw [h2, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, zpow_sub₀ hχ, zpow_neg, zpow_natCast]
    ring

end GlobalTheory.SenLines.Coords
