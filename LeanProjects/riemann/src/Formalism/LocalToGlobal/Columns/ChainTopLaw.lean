import Formalism.LocalToGlobal.Columns.LastRowColLevSym
import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
import Formalism.LocalToGlobal.Columns.StdBasisFlagSubmoduleOfBlockTriangular
import Formalism.LocalToGlobal.Columns.ColumnsProofs.SymLevEnt
import Formalism.LocalToGlobal.Columns.RecLevelSymF
import Formalism.LocalToGlobal.Columns.TiedGlMat

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

private theorem intAt_mul_columns {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨r * r', s * s', fun hm => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem hm with h1 | h1
    · exact hs h1
    · exact hs' h1
  · simp only [map_mul]
    linear_combination (algebraMap (𝓞 E) E s' * b) * h + (algebraMap (𝓞 E) E r) * h'

private theorem intAt_add_columns {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨r * s' + s * r', s * s', fun hm => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem hm with h1 | h1
    · exact hs h1
    · exact hs' h1
  · simp only [map_add, map_mul]
    linear_combination (algebraMap (𝓞 E) E s') * h + (algebraMap (𝓞 E) E s) * h'

private theorem intAt_zero_columns : IntAt P (0 : E) :=
  ⟨0, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩

private theorem intAt_one_columns : IntAt P (1 : E) :=
  ⟨1, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩

private theorem intAt_neg_columns {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h⟩ := ha
  exact ⟨-r, s, hs, by rw [mul_neg, h, map_neg]⟩

theorem ctl_red_symm {N : ℕ} {κ : Sp E N ≃ₗ[E] Sp E N} (hκ : κ ∈ GLint E N P) {H : GL (Fin N) (𝓞 E ⧸ P.asIdeal)}
    (hred : ∀ x ∈ stdAt E N P, redV P (κ x) = (H⁻¹).1.mulVec (redV P x)) :
    ∀ x ∈ stdAt E N P, redV P (κ.symm x) = H.1.mulVec (redV P x) := by
  intro x hx
  have hκ' : ∀ y, κ y ∈ stdAt E N P ↔ y ∈ stdAt E N P := hκ
  have hy : κ.symm x ∈ stdAt E N P := (hκ' _).mp (by rw [LinearEquiv.apply_symm_apply]; exact hx)
  have h := hred _ hy
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem ctl_ent {N : ℕ} {g : Sp E N →ₗ[E] Sp E N} (hg : ∀ x ∈ stdAt E N P, g x ∈ stdAt E N P) {H : Matrix (Fin N) (Fin N) (𝓞 E ⧸ P.asIdeal)}
    (hred : ∀ x ∈ stdAt E N P, redV P (g x) = H.mulVec (redV P x)) (l j : Fin N) :
    IntAt P (g (Pi.single j 1) l) ∧ redP P (g (Pi.single j 1) l) = H l j := by
  have he : (Pi.single j 1 : Sp E N) ∈ stdAt E N P := by
    rw [ciMem_stdAt]
    intro i
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same]
      exact intAt_one_columns
    · rw [Pi.single_eq_of_ne hij]
      exact intAt_zero_columns
  have hge := hg _ he
  rw [ciMem_stdAt] at hge
  refine ⟨hge l, ?_⟩
  have hrv : redV P (Pi.single j 1 : Sp E N) = (Pi.single j 1 : Fin N → 𝓞 E ⧸ P.asIdeal) := by
    funext i
    simp only [redV]
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same, Pi.single_eq_same]
      simpa using reduction_coe P 1
    · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij]
      simpa using reduction_coe P 0
  have h := congrFun (hred _ he) l
  rw [hrv] at h
  show redV P (g (Pi.single j 1)) l = H l j
  rw [h]
  simp

end Red

section Congr

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ctl_col {N M : ℕ} (g : Sp E N →ₗ[E] Sp E M) (v : Sp E N) {p : ℕ} (hp : p < M) :
    Loc.atN (g v) p = ∑ l ∈ Finset.range N, Loc.atN v l * Loc.atN (g (Loc.eN E N l)) p := by
  have hv : v = ∑ l : Fin N, v l • Loc.eN E N l.1 := by
    funext m
    simp [Loc.eN, Finset.sum_apply, ← Fin.ext_iff]
  rw [Finset.sum_range]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul]
  unfold Loc.atN
  simp [hp, Finset.sum_apply]

theorem entB_zero_eq_atN {k₀ n' n : ℕ} (z : HomE E (n' + 0) (n + 0)) {p p' : ℕ} (hp : p < n) (hp' : p' < n') :
    LocE.entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1) z p p' = Loc.atN (z (Loc.eN E (n' + 0) p')) p := by
  have hf : ∀ m s : ℕ, LocE.fIdx k₀ 0 m s = s := by
    intro m s
    unfold LocE.fIdx
    split_ifs <;> omega
  have h1 : LocE.scE n' (fun i => i + 1) p' = 0 := by
    unfold LocE.scE
    rw [if_pos hp']
  have h2 : LocE.scE n (fun i => i + 1) p = 0 := by
    unfold LocE.scE
    rw [if_pos hp]
  unfold LocE.entB
  rw [hf, hf, h1, h2, sub_self, zpow_zero, mul_one]

theorem ctl_funLeft_eN {n' s : ℕ} : LinearMap.funLeft E E (Fin.castAdd 0) (Loc.eN E (n' + 0) s) = Loc.eN E n' s := by
  funext l
  rfl

theorem ctl_atN_prXp {N p : ℕ} (v : Sp E N) (hp : p < N - 1) : Loc.atN (prXpG E N v) p = Loc.atN v p := by
  have h1 : p < N - 1 + 0 := by omega
  have h2 : p < N := by omega
  unfold Loc.atN
  rw [dif_pos h1, dif_pos h2]
  rfl

open Classical in

theorem ctl_congr (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ rS r t j n' N : ℕ} (hk : k₀ ≤ r) (hN1 : 1 ≤ N) (hn' : r + (j - 1) * t = n')
    (han : n' ≤ N - 1) (g : Sp E N →ₗ[E] Sp E N) (A : Sp E (N - 1) →ₗ[E] Sp E (N - 1)) (y : HomE E n' N) (κ : Sp E n' →ₗ[E] Sp E n')
    (hgA : ∀ p l, p < N - 1 → l < N - 1 → ∃ d, IntAt P d ∧
      Loc.atN (g (Loc.eN E N l)) p = Loc.atN (A (Loc.eN E (N - 1) l)) p + (q : E) * d)
    (hgl : ∀ p, p < N - 1 → ∃ d, IntAt P d ∧ Loc.atN (g (Loc.eN E N (N - 1))) p = (q : E) * d)
    (hY : ∀ l s, l < N → s < n' → IntAt P (Loc.atN (y (κ (Loc.eN E n' s))) l)) :
    LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j 0 n' 0 (N - 1) (prXpG E N ∘ₗ (g ∘ₗ y ∘ₗ κ) ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) =
      LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j 0 n' 0 (N - 1) (A ∘ₗ (prXpG E N ∘ₗ y ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) ∘ₗ κ) := by
  have hq0 := ciQ_ne_zero hu
  refine xtPhiGS_congr hq hq0 ψ₀ χ _ _ hk (by omega) fun p p' hp hp' => ?_
  have hp1 : p < N - 1 := by omega
  have hp1' : p' < n' := by omega
  rw [entB_zero_eq_atN _ hp1 hp1', entB_zero_eq_atN _ hp1 hp1']
  set v := y (κ (Loc.eN E n' p')) with hv
  have e1 : Loc.atN ((prXpG E N ∘ₗ (g ∘ₗ y ∘ₗ κ) ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) (Loc.eN E (n' + 0) p')) p =
      Loc.atN (g v) p := by
    simp only [LinearMap.comp_apply, ctl_funLeft_eN]
    rw [ctl_atN_prXp _ hp1]
  have e2 : Loc.atN ((A ∘ₗ (prXpG E N ∘ₗ y ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) ∘ₗ κ) (Loc.eN E (n' + 0) p')) p =
      Loc.atN (A (prXpG E N v)) p := rfl
  rw [e1, e2, ctl_col g v (show p < N by omega), ctl_col A (prXpG E N v) hp1]
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hr : Finset.range (N' + 1 - 1) = Finset.range N' := by simp
  rw [hr, Finset.sum_range_succ]
  have hvI : ∀ l, l < N' + 1 → IntAt P (Loc.atN v l) := fun l hl => hY l p' hl hp1'
  choose! D hD using fun l (hl : l < N' + 1 - 1) => hgA p l hp1 hl
  obtain ⟨d', hd'I, hd'⟩ := hgl p hp1
  refine ⟨∑ l ∈ Finset.range N', Loc.atN v l * D l + Loc.atN v N' * d', ?_, ?_⟩
  · refine (ciIntAt_sum _ _ fun l hl => (hvI l (by have := Finset.mem_range.1 hl; omega)).mul
      (hD l (by have := Finset.mem_range.1 hl; omega)).1).add ((hvI N' (by omega)).mul hd'I)
  · have h1 : ∀ l ∈ Finset.range N', Loc.atN v l * Loc.atN (g (Loc.eN E (N' + 1) l)) p =
        Loc.atN v l * Loc.atN (A (Loc.eN E (N' + 1 - 1) l)) p + (q : E) * (Loc.atN v l * D l) := by
      intro l hl
      rw [(hD l (by have := Finset.mem_range.1 hl; omega)).2]
      ring
    have h2 : ∀ l ∈ Finset.range N', Loc.atN (prXpG E (N' + 1) v) l * Loc.atN (A (Loc.eN E (N' + 1 - 1) l)) p =
        Loc.atN v l * Loc.atN (A (Loc.eN E (N' + 1 - 1) l)) p := by
      intro l hl
      rw [ctl_atN_prXp v (by have := Finset.mem_range.1 hl; omega)]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.mul_sum,
      show N' + 1 - 1 = N' from rfl] at *
    rw [hd']
    ring

end Congr

section Pat

variable {κ : Type} [CommRing κ]

theorem ctl_bt_of_allow {n k₀ rS r t : ℕ} (hkr : k₀ + rS ≤ r) (M : Matrix (Fin n) (Fin n) κ)
    (hpat : ∀ P P' : Fin n, P ≠ P' → M P P' ≠ 0 → slAllowY k₀ rS r t P.1 P'.1) :
    M.BlockTriangular fun l => betaExponentOfRanks k₀ rS r t l.1 := by
  intro i j hij
  by_contra hne
  have hij' : i ≠ j := by
    rintro rfl
    exact lt_irrefl _ hij
  have hA := hpat i j hij' hne
  have hs : i.1 < r → symIdx k₀ rS i.1 < r := fun h => symIdx_lt hkr h
  have hj0 := Nat.zero_le ((j.1 - r) / t)
  have hi0 := Nat.zero_le ((i.1 - r) / t)
  dsimp only at hij
  unfold slAllowY at hA
  unfold betaExponentOfRanks at hij
  split_ifs at hA hij <;> omega

end Pat

section FinalTheorems

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem columns_ctl_fact {n : ℕ} (x : Sp E (n + 0)) : x ∈ LocE.lamY P q n 0 (fun i => i + 1) ↔ x ∈ stdAt E n P := by
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap, ciMem_stdAt, ciMem_stdAt]
  refine forall_congr' fun l => ?_
  have hl : l.1 < n := l.2
  simp [LocE.scE, hl]

theorem ctl_stab0 {n : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) :
    κ ∈ stabL E (n + 0) (LocE.lamY P q n 0 (fun i => i + 1)) := by
  have h : ∀ x, κ x ∈ stdAt E n P ↔ x ∈ stdAt E n P := hκ
  show ∀ x : Sp E (n + 0), κ x ∈ LocE.lamY P q n 0 (fun i => i + 1) ↔ x ∈ LocE.lamY P q n 0 (fun i => i + 1)
  intro x
  rw [columns_ctl_fact, columns_ctl_fact]
  exact h x

theorem ctl_ob2M {n : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) {H : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hred : ∀ x ∈ stdAt E n P, redV P (κ x) = H.mulVec (redV P x)) (l l' : Fin n) : ob2M P q (c := 0) κ l l' = H l l' := by
  have h1 := (ctl_ent (g := κ.toLinearMap)
    (fun x hx => ((show ∀ y, κ y ∈ stdAt E n P ↔ y ∈ stdAt E n P from hκ) x).mpr hx) hred l l').2
  unfold ob2M
  have hl : l.1 < n := l.2
  have hl' : l'.1 < n := l'.2
  simp only [LocE.scE, hl, hl', ↓reduceIte, sub_self, zpow_zero, mul_one]
  exact h1

theorem ctl_mem_JGsym (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {k₀ rS r t j n : ℕ}
    (hr : k₀ + rS < r) (hkn : k₀ ≤ n) (hrn : r ≤ n) (ht : 0 < t) (hn : n ≤ r + j * t)
    {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) {H : GL (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hH : H ∈ HJsym (𝓞 E ⧸ P.asIdeal) n k₀ r t j rS hrn) (hred : ∀ x ∈ stdAt E n P, redV P (κ x) = H.1.mulVec (redV P x)) :
    κ ∈ LocE.JGsym P q k₀ rS r t n 0 := by
  obtain ⟨hdiag, hpat⟩ := (sl_mem_HJsym_iff hrn (by omega) ht hn H).1 hH
  have hM := ctl_ob2M (q := q) hκ hred
  have hfp : ∀ l : ℕ, l < n → LocE.fPos k₀ 0 n l = l := fun l hl => by unfold LocE.fPos; split_ifs <;> omega
  refine mem_parahoric_of_blockTriangular hq hu hkn hr (by omega) (ctl_stab0 hκ) ?_ ?_ ?_
  · intro l l' hlt
    rw [hM]
    dsimp only at hlt
    rw [hfp l.1 l.2, hfp l'.1 l'.2] at hlt
    exact ctl_bt_of_allow (by omega) H.1 hpat hlt
  · intro l hl
    rw [hfp l.1 l.2] at hl
    rw [hM]
    exact hdiag l hl
  · intro l l' hl hl'
    rw [hfp l.1 l.2] at hl
    rw [hfp l'.1 l'.2] at hl'
    rw [hM]
    by_contra hne
    have h := hpat l l' (fun e => by rw [e] at hl; omega) hne
    unfold slAllowY at h
    rw [if_pos (by omega)] at h
    exact h.2.2 ⟨hl, hl'⟩

end FinalTheorems

section Tgt

variable {κ : Type} [CommRing κ]

def ctlTL {N' : ℕ} (M : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ) : Matrix (Fin N') (Fin N') κ :=
  fun p s => M (Fin.castSucc p) (Fin.castSucc s)

theorem ctlTL_mul {N' : ℕ} (M M' : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ) (hM : ∀ p : Fin N', M (Fin.castSucc p) (Fin.last N') = 0) :
    ctlTL (M * M') = ctlTL M * ctlTL M' := by
  ext p s
  simp only [ctlTL, Matrix.mul_apply, Fin.sum_univ_castSucc, hM, zero_mul, add_zero]

theorem ctlTL_one {N' : ℕ} : ctlTL (1 : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ) = 1 := by
  ext p s
  simp [ctlTL, Matrix.one_apply]

theorem ctl_fixCol_zero {N' c : ℕ} {M : GL (Fin (N' + 1)) κ} (hM : M ∈ fixCol (N' + 1) κ c) (hc : N' = c) (p : Fin N') :
    (M : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ) (Fin.castSucc p) (Fin.last N') = 0 := by
  have h : ∀ i j : Fin (N' + 1), j.val = c → (M : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ) i j = (1 : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ) i j := hM
  rw [h (Fin.castSucc p) (Fin.last N') (by rw [Fin.val_last]; exact hc)]
  exact Matrix.one_apply_ne (Fin.castSucc_lt_last p).ne

def ctlTLGL {N' : ℕ} (M : GL (Fin (N' + 1)) κ) (hM : ∀ p : Fin N', (M : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ) (Fin.castSucc p) (Fin.last N') = 0)
    (hM' : ∀ p : Fin N', ((M⁻¹ : GL (Fin (N' + 1)) κ) : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ) (Fin.castSucc p) (Fin.last N') = 0) :
    GL (Fin N') κ :=
  ⟨ctlTL M.1, ctlTL (M⁻¹).1, by rw [← ctlTL_mul _ _ hM, ← Units.val_mul, mul_inv_cancel, Units.val_one, ctlTL_one],
    by rw [← ctlTL_mul _ _ hM', ← Units.val_mul, inv_mul_cancel, Units.val_one, ctlTL_one]⟩

theorem ctl_TL_mem {N' k r t m rS : ℕ} (h : r ≤ N' + 1) (h' : r ≤ N') {M : GL (Fin (N' + 1)) κ}
    (hMJ : M ∈ HJsym κ (N' + 1) k r t m rS h)
    (hM : ∀ p : Fin N', (M : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ) (Fin.castSucc p) (Fin.last N') = 0)
    (hM' : ∀ p : Fin N', ((M⁻¹ : GL (Fin (N' + 1)) κ) : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ) (Fin.castSucc p) (Fin.last N') = 0) :
    ctlTLGL M hM hM' ∈ HJsym κ N' k r t m rS h' := by
  unfold HJsym HPar HPsymF blockUT blk0 at hMJ ⊢
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hMJ
  have hb : ((y : GL (Fin (N' + 1)) κ) : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ).BlockTriangular fun i => blkIdx (r :: List.replicate m t) i.1 :=
    y.2
  refine Subgroup.mem_map.mpr ⟨⟨ctlTLGL (y : GL (Fin (N' + 1)) κ) hM hM', ?_⟩, ?_, rfl⟩
  · show (ctlTL ((y : GL (Fin (N' + 1)) κ) : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ)).BlockTriangular fun i => blkIdx (r :: List.replicate m t) i.1
    intro p s hlt
    exact hb (i := Fin.castSucc p) (j := Fin.castSucc s) hlt
  · rw [Subgroup.mem_comap] at hy ⊢
    convert hy using 1
    apply Units.ext
    ext i j
    rfl

end Tgt

section TgtE

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ctl_mulVec_std {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (hM : ∀ i j, IntAt P (M i j)) {v : Sp E n} (hv : v ∈ stdAt E n P) :
    M.mulVec v ∈ stdAt E n P := by
  rw [ciMem_stdAt] at hv ⊢
  intro i
  show IntAt P (∑ j, M i j * v j)
  exact Finset.sum_induction _ (IntAt P) (fun a b ha hb => intAt_add_columns ha hb) intAt_zero_columns
    (fun j _ => intAt_mul_columns (hM i j) (hv j))

theorem ctl_redV_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (hM : ∀ i j, IntAt P (M i j)) {v : Sp E n} (hv : v ∈ stdAt E n P) :
    redV P (M.mulVec v) = (M.map (redP P)).mulVec (redV P v) := by
  rw [ciMem_stdAt] at hv
  funext i
  show redP P (∑ j, M i j * v j) = ∑ j, redP P (M i j) * redP P (v j)
  rw [redP_sum _ _ (fun j _ => intAt_mul_columns (hM i j) (hv j))]
  exact Finset.sum_congr rfl (fun j _ => reduction_mul (hM i j) (hv j))

theorem ctl_map_mul {n : ℕ} (M M' : Matrix (Fin n) (Fin n) E) (hM : ∀ i j, IntAt P (M i j)) (hM' : ∀ i j, IntAt P (M' i j)) :
    (M * M').map (redP P) = M.map (redP P) * M'.map (redP P) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [redP_sum _ _ (fun l _ => intAt_mul_columns (hM i l) (hM' l j))]
  exact Finset.sum_congr rfl (fun l _ => reduction_mul (hM i l) (hM' l j))

theorem ctl_lift {n : ℕ} (B : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) :
    ∃ γ : Sp E n ≃ₗ[E] Sp E n, γ ∈ GLint E n P ∧ (∀ x ∈ stdAt E n P, redV P (γ x) = B.1.mulVec (redV P x)) ∧
      ∀ x ∈ stdAt E n P, redV P (γ.symm x) = (B⁻¹).1.mulVec (redV P x) := by
  have hne : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  choose A0 hA0 using fun i j => Ideal.Quotient.mk_surjective
    ((B : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j)
  let A0' : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of A0
  have hB0 : (Ideal.Quotient.mk P.asIdeal).mapMatrix A0' = (B : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) := by
    ext i j
    exact hA0 i j
  have hdet0 : A0'.det ∉ P.asIdeal := by
    intro h
    have h1 : Ideal.Quotient.mk P.asIdeal A0'.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [RingHom.map_det, hB0] at h1
    have hu := (Matrix.isUnit_iff_isUnit_det _).mp B.isUnit
    rw [h1] at hu
    exact not_isUnit_zero hu
  let A : Matrix (Fin n) (Fin n) E := A0'.map (algebraMap (𝓞 E) E)
  have hdA : A.det = algebraMap (𝓞 E) E A0'.det := (RingHom.map_det _ A0').symm
  have hAdet : A.det ≠ 0 := by
    rw [hdA]
    intro h
    apply hdet0
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mp h]
    exact P.asIdeal.zero_mem
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hAdet
  have hAi : ∀ i j, IntAt P (A i j) := fun i j => ⟨A0' i j, 1, hne, by simp [A]⟩
  have hAinv : ∀ i j, IntAt P (A⁻¹ i j) := by
    intro i j
    refine ⟨Matrix.adjugate A0' i j, A0'.det, hdet0, ?_⟩
    have hadj : Matrix.adjugate A = (Matrix.adjugate A0').map (algebraMap (𝓞 E) E) :=
      (RingHom.map_adjugate _ A0').symm
    rw [← hdA, Matrix.inv_def, Matrix.smul_apply, hadj, Matrix.map_apply, smul_eq_mul, Ring.inverse_eq_inv,
      ← mul_assoc, mul_inv_cancel₀ hAdet, one_mul]
  let γ : Sp E n ≃ₗ[E] Sp E n := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' A⁻¹)
    (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hu, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ hu, Matrix.toLin'_one])
  have hγ : ∀ x, γ x = A.mulVec x := fun x => Matrix.toLin'_apply A x
  have hγs : ∀ x, γ.symm x = A⁻¹.mulVec x := fun x => Matrix.toLin'_apply A⁻¹ x
  have hAB : A.map (redP P) = (B : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) := by
    ext i j
    simp only [A, A0', Matrix.map_apply, Matrix.of_apply]
    rw [reduction_coe]
    exact hA0 i j
  have hAinvB : A⁻¹.map (redP P) = ((B⁻¹ : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) := by
    have h1 := ctl_map_mul A A⁻¹ hAi hAinv
    rw [Matrix.mul_nonsing_inv _ hu, hAB] at h1
    have h2 : (1 : Matrix (Fin n) (Fin n) E).map (redP P) = 1 := by
      ext i j
      rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · simpa using reduction_coe P 1
      · simpa using reduction_coe P 0
    rw [h2] at h1
    calc A⁻¹.map (redP P) = ((B⁻¹ * B : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) * A⁻¹.map (redP P) := by
          rw [inv_mul_cancel, Units.val_one, Matrix.one_mul]
      _ = _ := by rw [Units.val_mul, Matrix.mul_assoc, ← h1, Matrix.mul_one]
  refine ⟨γ, ?_, ?_, ?_⟩
  · show ∀ x, γ x ∈ stdAt E n P ↔ x ∈ stdAt E n P
    intro x
    constructor
    · intro hx
      have h := ctl_mulVec_std A⁻¹ hAinv hx
      rwa [← hγs, LinearEquiv.symm_apply_apply] at h
    · intro hx
      rw [hγ]
      exact ctl_mulVec_std A hAi hx
  · intro x hx
    rw [hγ, ctl_redV_mulVec A hAi hx, hAB]
  · intro x hx
    rw [hγs, ctl_redV_mulVec A⁻¹ hAinv hx, hAinvB]

private theorem exists_intAt_eq_q_mul_of_redP_eq_zero (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {x : E}
    (hx : IntAt P x) (h0 : redP P x = 0) : ∃ d, IntAt P d ∧ x = (q : E) * d := by
  obtain ⟨r, s, hs, h⟩ := hx
  have hr : r ∈ P.asIdeal := by
    have h1 := reduction_spec P hs h
    rw [h0, mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  have hdvd : P.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 E)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hq)
  obtain ⟨J, hJ⟩ := hdvd
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hle
    apply hu
    have h2 : Ideal.span {((q : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right hle
    exact h2 (Ideal.mem_span_singleton_self _)
  obtain ⟨s', hs'J, hs'P⟩ := SetLike.not_le_iff_exists.mp hJP
  have hmem : r * s' ∈ Ideal.span {((q : ℕ) : 𝓞 E)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hr hs'J
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hsE : algebraMap (𝓞 E) E s ≠ 0 := fun h3 =>
    hs (by rw [(map_eq_zero_iff _ hinj).mp h3]; exact P.asIdeal.zero_mem)
  have hs'E : algebraMap (𝓞 E) E s' ≠ 0 := fun h3 =>
    hs'P (by rw [(map_eq_zero_iff _ hinj).mp h3]; exact P.asIdeal.zero_mem)
  have hcE : algebraMap (𝓞 E) E c * (q : E) = algebraMap (𝓞 E) E r * algebraMap (𝓞 E) E s' := by
    have h4 := congrArg (algebraMap (𝓞 E) E) hc
    simp only [map_mul, map_natCast] at h4
    exact h4
  refine ⟨algebraMap (𝓞 E) E c / (algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E s'), ⟨c, s * s', ?_, ?_⟩, ?_⟩
  · intro hm
    rcases P.isPrime.mem_or_mem hm with h5 | h5
    · exact hs h5
    · exact hs'P h5
  · rw [map_mul, mul_div_assoc', mul_comm (_ * _) _, mul_div_assoc, div_self (mul_ne_zero hsE hs'E), mul_one]
  · rw [eq_comm, mul_div_assoc', div_eq_iff (mul_ne_zero hsE hs'E)]
    linear_combination hcE - (algebraMap (𝓞 E) E s') * h

private theorem eN_eq_pi_single {N l : ℕ} (hl : l < N) : (Loc.eN E N l : Sp E N) = Pi.single (⟨l, hl⟩ : Fin N) 1 := by
  funext m
  simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem ctl_tgt (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {N' k₀ r t m rS : ℕ}
    (hN' : N' = r + m * t) (hrN : r ≤ N' + 1) (hr' : r ≤ N') (hr : k₀ + rS < r) (hkN : k₀ ≤ N') (ht : 0 < t)
    {κ' : Sp E (N' + 1) ≃ₗ[E] Sp E (N' + 1)} (hκ' : κ' ∈ GLint E (N' + 1) P) {H' : GL (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal)}
    (hH' : H' ∈ HJsym (𝓞 E ⧸ P.asIdeal) (N' + 1) k₀ r t m rS hrN)
    (hA : ∀ p : Fin N', (H' : Matrix (Fin (N' + 1)) (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal)) (Fin.castSucc p) (Fin.last N') = 0)
    (hA' : ∀ p : Fin N', ((H'⁻¹ : GL (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin (N' + 1)) (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal))
      (Fin.castSucc p) (Fin.last N') = 0)
    (hred : ∀ x ∈ stdAt E (N' + 1) P, redV P (κ' x) = (H'⁻¹).1.mulVec (redV P x)) :
    ∃ γ : Sp E N' ≃ₗ[E] Sp E N', γ ∈ GLint E N' P ∧ γ ∈ LocE.JGsym P q k₀ rS r t N' 0 ∧
      (∀ x ∈ stdAt E N' P, redV P (γ x) = ((ctlTLGL H' hA hA')⁻¹).1.mulVec (redV P x)) ∧
      (∀ p l, p < N' → l < N' → ∃ d, IntAt P d ∧
        Loc.atN (κ'.symm.toLinearMap (Loc.eN E (N' + 1) l)) p = Loc.atN (γ.symm.toLinearMap (Loc.eN E N' l)) p + (q : E) * d) ∧
      (∀ p, p < N' → ∃ d, IntAt P d ∧ Loc.atN (κ'.symm.toLinearMap (Loc.eN E (N' + 1) N')) p = (q : E) * d) := by
  have hTL := ctl_TL_mem hrN hr' hH' hA hA'
  have hBJ := inv_mem hTL
  obtain ⟨γ, hγ, hγred, hγsred⟩ := ctl_lift ((ctlTLGL H' hA hA')⁻¹)
  have hJ := ctl_mem_JGsym hq hu hr hkN hr' ht hN'.le hγ hBJ hγred
  have hκ'm : ∀ y, κ' y ∈ stdAt E (N' + 1) P ↔ y ∈ stdAt E (N' + 1) P := hκ'
  have hκs : ∀ x ∈ stdAt E (N' + 1) P, κ'.symm.toLinearMap x ∈ stdAt E (N' + 1) P := fun x hx =>
    (hκ'm _).mp (by rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]; exact hx)
  have hκred := ctl_red_symm hκ' hred
  have hEκ := fun l j => ctl_ent (g := κ'.symm.toLinearMap) hκs hκred l j
  have hγm : ∀ y, γ y ∈ stdAt E N' P ↔ y ∈ stdAt E N' P := hγ
  have hγs : ∀ x ∈ stdAt E N' P, γ.symm.toLinearMap x ∈ stdAt E N' P := fun x hx =>
    (hγm _).mp (by rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]; exact hx)
  rw [inv_inv] at hγsred
  have hEγ := fun l j => ctl_ent (g := γ.symm.toLinearMap) hγs hγsred l j
  refine ⟨γ, hγ, hJ, hγred, ?_, ?_⟩
  · intro p l hp hl
    have hp1 : p < N' + 1 := by omega
    have hl1 : l < N' + 1 := by omega
    rw [eN_eq_pi_single hl1, eN_eq_pi_single hl]
    unfold Loc.atN
    rw [dif_pos hp1, dif_pos hp]
    obtain ⟨ia, ra⟩ := hEκ ⟨p, hp1⟩ ⟨l, hl1⟩
    obtain ⟨ib, rb⟩ := hEγ ⟨p, hp⟩ ⟨l, hl⟩
    have hsub := intAt_add_columns ia (intAt_neg_columns ib)
    rw [← sub_eq_add_neg] at hsub
    have hred0 : redP P (κ'.symm.toLinearMap (Pi.single ⟨l, hl1⟩ 1) ⟨p, hp1⟩ -
        γ.symm.toLinearMap (Pi.single ⟨l, hl⟩ 1) ⟨p, hp⟩) = 0 := by
      have h1 := reduction_add hsub ib
      rw [sub_add_cancel, ra, rb] at h1
      have h2 : (H' : Matrix (Fin (N' + 1)) (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal)) ⟨p, hp1⟩ ⟨l, hl1⟩ =
          ((ctlTLGL H' hA hA' : GL (Fin N') (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin N') (Fin N') (𝓞 E ⧸ P.asIdeal)) ⟨p, hp⟩ ⟨l, hl⟩ := rfl
      rw [h2] at h1
      linear_combination -h1
    obtain ⟨d, hd, hdeq⟩ := exists_intAt_eq_q_mul_of_redP_eq_zero hq hu hsub hred0
    exact ⟨d, hd, by rw [← hdeq]; ring⟩
  · intro p hp
    have hp1 : p < N' + 1 := by omega
    rw [eN_eq_pi_single (by omega : N' < N' + 1)]
    unfold Loc.atN
    rw [dif_pos hp1]
    obtain ⟨ia, ra⟩ := hEκ ⟨p, hp1⟩ ⟨N', by omega⟩
    have h0 : redP P (κ'.symm.toLinearMap (Pi.single ⟨N', by omega⟩ 1) ⟨p, hp1⟩) = 0 := by
      rw [ra]
      exact hA ⟨p, hp⟩
    exact exists_intAt_eq_q_mul_of_redP_eq_zero hq hu ia h0

end TgtE

section abelian₂

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

def ctlE {κ : Type} [Zero κ] {n : ℕ} (H : Matrix (Fin n) (Fin n) κ) (p p' : ℕ) : κ := if h : p < n ∧ p' < n then H ⟨p, h.1⟩ ⟨p', h.2⟩ else 0

theorem ctl_unitV_glm {K k' : Type} [Field K] [Field k'] (e : (𝓞 E ⧸ P.asIdeal) ≃+* k') (σ₀ : K →+* ℂ)
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : σ₀ (LocE.unitV χ a) = glmChi e σ₀ χ (e (redP P a)) := by
  unfold LocE.unitV
  by_cases hu : IsUnit (redP P a)
  · rw [dif_pos hu]
    have hx : e (redP P a) = ((Units.map e.toRingHom.toMonoidHom hu.unit : k'ˣ) : k') := by simp
    have hu2 : Units.map e.symm.toRingHom.toMonoidHom (Units.map e.toRingHom.toMonoidHom hu.unit) = hu.unit := by
      ext
      simp
    rw [hx]
    unfold glmChi
    rw [MulChar.ofUnitHom_coe]
    simp only [MonoidHom.comp_apply, Units.coe_map]
    rw [hu2]
    rfl
  · rw [dif_neg hu, map_zero, MulChar.map_nonunit]
    exact fun h => hu (by simpa using h.map e.symm)

theorem ctl_lamGBS_lamJ {K k' : Type} [Field K] [Field k'] (e : (𝓞 E ⧸ P.asIdeal) ≃+* k') (σ₀ : K →+* ℂ)
    (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r t j n : ℕ} (hkr : k₀ < r) (hrn : r + j * t ≤ n)
    {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) {H : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hred : ∀ x ∈ stdAt E n P, redV P (κ x) = H.mulVec (redV P x)) :
    σ₀ (LocE.lamGBS q ψ₀ χ k₀ r t j n 0 κ.toLinearMap) =
      Formalism.L2.Forms.lamJ (glmPsi e σ₀ ψ₀) (fun s => glmChi e σ₀ (χ s)) r t j k₀ (H.map e) := by
  classical
  have hM : ∀ p p', p < n → p' < n →
      IntAt P (LocE.entB q k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p') ∧
      redP P (LocE.entB q k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p') = ctlE H p p' := by
    intro p p' hp hp'
    rw [entB_zero_eq_atN (z := κ.toLinearMap) hp hp', ocbS_eN_single (show p' < n + 0 from hp'), ocbS_atN_of_lt _ (show p < n + 0 from hp)]
    have h1 := ctl_ent (g := κ.toLinearMap) (fun x hx => (hκ x).2 hx) hred ⟨p, hp⟩ ⟨p', hp'⟩
    exact ⟨h1.1, h1.2.trans (by unfold ctlE; rw [dif_pos ⟨hp, hp'⟩])⟩
  have hS : ∀ x, x + 1 < r → (x ∈ SPsymF r k₀ ↔ x + 1 ≠ k₀) := by
    intro x hx
    unfold SPsymF
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  unfold LocE.lamGBS LocE.lamGvS Formalism.L2.Forms.lamJ
  rw [map_mul]
  congr 1
  · rw [← supSum_map_eq e (SPsymF r k₀) hS H, glmPsi_apply]
    congr 2
    have hI1 : ∀ i ∈ Finset.range (k₀ - 1), IntAt P (LocE.entB q k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap i (i + 1)) :=
      fun i hi => (hM _ _ (by have := Finset.mem_range.1 hi; omega) (by have := Finset.mem_range.1 hi; omega)).1
    have hI2 : ∀ i ∈ Finset.range (r - k₀ - 1),
        IntAt P (LocE.entB q k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap (k₀ + i) (k₀ + i + 1)) :=
      fun i hi => (hM _ _ (by have := Finset.mem_range.1 hi; omega) (by have := Finset.mem_range.1 hi; omega)).1
    rw [reduction_add (ciIntAt_sum _ _ hI1) (ciIntAt_sum _ _ hI2), redP_sum _ _ hI1, redP_sum _ _ hI2,
      Finset.sum_congr rfl fun i hi => (hM _ _ (by have := Finset.mem_range.1 hi; omega) (by have := Finset.mem_range.1 hi; omega)).2,
      Finset.sum_congr rfl fun i (hi : i ∈ Finset.range (r - k₀ - 1)) =>
        (hM _ _ (by have := Finset.mem_range.1 hi; omega) (by have := Finset.mem_range.1 hi; omega)).2]
    have hins := sl_sup_ins (r := r) (k := k₀) (c := 0) (j := r - k₀) (by omega) (ctlE H) (ctlE H) (fun _ _ => rfl)
      (fun i h1 h2 => by omega) (fun i _ => by rw [Nat.sub_zero])
    rw [show r - k₀ - 1 = r - k₀ - 1 from rfl, ← hins, sl_supSum_eq]
    symm
    have hsub : Finset.range r ⊆ Finset.range n := fun x hx =>
      Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) (show r ≤ n by omega))
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      by_cases hc : i + 1 < r ∧ i + 1 ≠ k₀
      · rw [if_pos ⟨hc.1, (hS i hc.1).2 hc.2⟩, if_pos hc, dif_pos (show i + 1 < n by omega)]
        unfold ctlE
        rw [dif_pos ⟨by omega, by omega⟩]
      · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, (hS i h.1).1 h.2⟩)]
    · intro i _ hi
      rw [Finset.mem_range] at hi
      rw [if_neg (fun h => by omega)]
  · rw [map_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have hbd : ∀ s : Fin t, r + i * t + s.1 < n := fun s => by
      have h1 : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t hi'
      rw [Nat.succ_mul] at h1
      have := s.2
      omega
    rw [ctl_unitV_glm e σ₀ (χ i)]
    congr 1
    rw [redP_det (Matrix.of fun s s' : Fin t => LocE.entB q k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap
      (r + i * t + s.1) (r + i * t + s'.1)) (fun s s' => (hM _ _ (hbd s) (hbd s')).1)]
    refine (RingHom.map_det e.toRingHom _).trans ?_
    congr 1
    ext s s'
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, (hM _ _ (hbd s) (hbd s')).2]
    unfold Formalism.L2.Forms.blkMat Formalism.L2.Forms.entN ctlE
    rw [dif_pos ⟨hbd s, hbd s'⟩, dif_pos ⟨hbd s, hbd s'⟩]
    rfl

end abelian₂

section Cmp

theorem ctl_lamJ_TL {k' : Type} [Field k'] (ψ : AddChar k' ℂ) (χ : ℕ → MulChar k' ℂ) {N' a t nb skip : ℕ} (ha : a ≤ N')
    (hb : a + nb * t ≤ N') (M : Matrix (Fin (N' + 1)) (Fin (N' + 1)) k') :
    Formalism.L2.Forms.lamJ ψ χ a t nb skip M = Formalism.L2.Forms.lamJ ψ χ a t nb skip (ctlTL M) := by
  unfold Formalism.L2.Forms.lamJ
  congr 1
  · congr 1
    rw [Fin.sum_univ_castSucc]
    have hlast : ∀ y : Fin (N' + 1),
        ¬ (((Fin.last N' : Fin (N' + 1)) : ℕ) + 1 = (y : ℕ) ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ skip) := by
      intro y h
      have := y.2
      simp only [Fin.val_last] at h
      omega
    simp only [hlast, if_false, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fin.sum_univ_castSucc]
    have hl2 : ¬ (((Fin.castSucc x : Fin (N' + 1)) : ℕ) + 1 = ((Fin.last N' : Fin (N' + 1)) : ℕ) ∧
        ((Fin.last N' : Fin (N' + 1)) : ℕ) < a ∧ ((Fin.last N' : Fin (N' + 1)) : ℕ) ≠ skip) := by
      simp only [Fin.val_last]
      omega
    rw [if_neg hl2, add_zero]
    simp only [Fin.coe_castSucc]
    rfl
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hB : Formalism.L2.Forms.blkMat a t i M = Formalism.L2.Forms.blkMat a t i (ctlTL M) := by
      ext s s'
      have hit : i * t + t ≤ nb * t := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right t hi
      have hs := s.2
      have hs' := s'.2
      have h1 : a + i * t + (s : ℕ) < N' := by omega
      have h2 : a + i * t + (s' : ℕ) < N' := by omega
      simp only [Formalism.L2.Forms.blkMat, Formalism.L2.Forms.entN]
      rw [dif_pos ⟨by omega, by omega⟩, dif_pos ⟨h1, h2⟩]
      rfl
    rw [hB]

variable {κ : Type} [CommRing κ]

theorem ctl_det_TL {N' : ℕ} (M : Matrix (Fin (N' + 1)) (Fin (N' + 1)) κ) (hcol : ∀ p : Fin N', M (Fin.castSucc p) (Fin.last N') = 0)
    (hll : M (Fin.last N') (Fin.last N') = 1) : M.det = (ctlTL M).det := by
  rw [Matrix.det_succ_column M (Fin.last N'), Fin.sum_univ_castSucc]
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, hll, mul_one, Fin.succAbove_last, Fin.val_last]
  rw [Even.neg_one_pow ⟨N', rfl⟩, one_mul]
  rfl

end Cmp

section DetE

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem ctl_det_red {n : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) {H : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hred : ∀ x ∈ stdAt E n P, redV P (κ x) = H.mulVec (redV P x)) :
    IntAt P (LinearEquiv.det κ : E) ∧ redP P (LinearEquiv.det κ : E) = H.det := by
  have hκ' : ∀ y, κ y ∈ stdAt E n P ↔ y ∈ stdAt E n P := hκ
  set A : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' κ.toLinearMap with hA
  have hAi : ∀ i j, IntAt P (A i j) ∧ redP P (A i j) = H i j := by
    intro i j
    rw [hA, LinearMap.toMatrix'_apply]
    exact ctl_ent (g := κ.toLinearMap) (fun x hx => (hκ' x).mpr hx) hred i j
  have hdet : (LinearEquiv.det κ : E) = A.det := by
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  let S : Subring E :=
    { carrier := {a | IntAt P a}
      mul_mem' := fun ha hb => intAt_mul_columns ha hb
      one_mem' := intAt_one_columns
      add_mem' := fun ha hb => intAt_add_columns ha hb
      zero_mem' := intAt_zero_columns
      neg_mem' := fun ha => intAt_neg_columns ha }
  let f : S →+* 𝓞 E ⧸ P.asIdeal :=
    { toFun := fun a => redP P a.1
      map_one' := by
        show redP P 1 = 1
        simpa using reduction_coe P 1
      map_mul' := fun a b => reduction_mul a.2 b.2
      map_zero' := by
        show redP P 0 = 0
        simpa using reduction_coe P 0
      map_add' := fun a b => reduction_add a.2 b.2 }
  let B : Matrix (Fin n) (Fin n) S := fun i j => ⟨A i j, (hAi i j).1⟩
  have hB : B.map S.subtype = A := by
    ext i j
    rfl
  have hdB : A.det = (B.det : E) := by
    rw [← hB]
    exact (RingHom.map_det S.subtype B).symm
  have hfB : f.mapMatrix B = H := by
    ext i j
    exact (hAi i j).2
  refine ⟨?_, ?_⟩
  · rw [hdet, hdB]
    exact B.det.2
  · rw [hdet, hdB, ← hfB]
    exact RingHom.map_det f B

end DetE

end Formalism.L2.Col
