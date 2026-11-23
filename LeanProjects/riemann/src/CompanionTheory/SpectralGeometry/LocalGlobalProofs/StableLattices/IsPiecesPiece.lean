import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

section Concrete

variable {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}

theorem hLin_apply (hh : IsHerm s h) (x y : V) : hLin hh x y = h x y := rfl

theorem h_sub_right (hh : IsHerm s h) (x y z : V) : h x (y - z) = h x y - h x z :=
  map_sub (hLin hh x) y z

theorem h_zero_right (hh : IsHerm s h) (x : V) : h x 0 = 0 := map_zero (hLin hh x)

theorem eq_of_pair (hh : IsHerm s h) {z z' : V} (H : ∀ x, h x z = h x z') : z = z' := by
  have : z - z' = 0 := by
    apply hh.2.2.2
    intro y
    rw [hh.2.2.1 y (z - z'), h_sub_right hh, H, sub_self, map_zero]
  exact sub_eq_zero.1 this

theorem s_ne (hδ : δ ≠ 0) : s δ ≠ 0 := by
  simpa using (map_ne_zero s).2 hδ

theorem projE_apply (hh : IsHerm s h) (i : Fin l) (x : V) :
    projE hh δ e f i x = ((s δ)⁻¹ * h (f i) x) • e i := by
  simp [projE, hLin_apply, mul_smul]

theorem projF_apply (hh : IsHerm s h) (i : Fin l) (x : V) :
    projF hh δ e f i x = (δ⁻¹ * h (e i) x) • f i := by
  simp [projF, hLin_apply, mul_smul]

theorem h_f_e (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    h (f i) (e j) = if j = i then s δ else 0 := by
  rw [hh.2.2.1 (e j) (f i), hF.2.2.1 j i]
  split_ifs <;> simp

theorem projE_e (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projE hh δ e f i (e j) = if j = i then e i else 0 := by
  rw [projE_apply, h_f_e hh hF]
  split_ifs
  · simp [s_ne hδ]
  · simp

theorem projE_f (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projE hh δ e f i (f j) = 0 := by
  rw [projE_apply, hF.2.1]; simp

theorem projE_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Fin l) {w : V} (hw : w ∈ W) :
    projE hh δ e f i w = 0 := by
  rw [projE_apply, (hF.2.2.2.1 w hw i).2]; simp

theorem projF_e (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projF hh δ e f i (e j) = 0 := by
  rw [projF_apply, hF.1]; simp

theorem projF_f (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projF hh δ e f i (f j) = if j = i then f i else 0 := by
  rw [projF_apply, hF.2.2.1 i j]
  by_cases hij : j = i
  · subst hij; simp [hδ]
  · simp [hij, Ne.symm hij]

theorem projF_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Fin l) {w : V} (hw : w ∈ W) :
    projF hh δ e f i w = 0 := by
  rw [projF_apply, (hF.2.2.2.1 w hw i).1]; simp

theorem piece_e (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) (j : Fin l) :
    piece hh δ e f i (e j) = if i = some (Sum.inl j) then e j else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_e hh hδ hF, projF_e hh hF]
  · by_cases hij : j = i
    · subst hij; simp [piece, projE_e hh hδ hF]
    · simp [piece, projE_e hh hδ hF, hij, Ne.symm hij]
  · simp [piece, projF_e hh hF]

theorem piece_f (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) (j : Fin l) :
    piece hh δ e f i (f j) = if i = some (Sum.inr j) then f j else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_f hh hF, projF_f hh hδ hF]
  · simp [piece, projE_f hh hF]
  · by_cases hij : j = i
    · subst hij; simp [piece, projF_f hh hδ hF]
    · simp [piece, projF_f hh hδ hF, hij, Ne.symm hij]

theorem piece_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Idx l) {w : V} (hw : w ∈ W) :
    piece hh δ e f i w = if i = none then w else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_w hh hF _ hw, projF_w hh hF _ hw]
  · simp [piece, projE_w hh hF _ hw]
  · simp [piece, projF_w hh hF _ hw]

theorem end_ext (hF : IsFrame h δ e f W) {A B : Module.End L V} (he : ∀ i, A (e i) = B (e i))
    (hf : ∀ i, A (f i) = B (f i)) (hw : ∀ w ∈ W, A w = B w) : A = B := by
  ext x
  obtain ⟨a, b, w, hwW, rfl⟩ := hF.2.2.2.2.2 x
  simp [map_add, map_sum, he, hf, hw w hwW]

theorem isPieces_piece (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) :
    IsPieces (piece hh δ e f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, piece_e hh hδ hF, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_e hh hδ hF]
    · simp only [Module.End.mul_apply, piece_f hh hδ hF, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_f hh hδ hF]
    · simp only [Module.End.mul_apply, piece_w hh hF _ hw, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_w hh hF _ hw]
  · intro i
    refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, piece_e hh hδ hF]
      split_ifs with h1 <;> simp_all [piece_e hh hδ hF]
    · simp only [Module.End.mul_apply, piece_f hh hδ hF]
      split_ifs with h1 <;> simp_all [piece_f hh hδ hF]
    · simp only [Module.End.mul_apply, piece_w hh hF _ hw]
      split_ifs with h1 <;> simp_all [piece_w hh hF _ hw]
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp [LinearMap.sum_apply, piece_e hh hδ hF]
    · simp [LinearMap.sum_apply, piece_f hh hδ hF]
    · simp [LinearMap.sum_apply, piece_w hh hF _ hw]

theorem lat_smul {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {c : L} (hc : ‖c‖ ≤ 1) {x : V} (hx : x ∈ Λ) :
    c • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hx i)

theorem e_mem {Λ : AddSubgroup V} (hA : IsAdapted h e f W (fun _ => 1) Λ) (hh : IsHerm s h) (j : Fin l) :
    e j ∈ Λ := by
  have := (hA (Pi.single j 1) 0 0 W.zero_mem).2 ⟨fun i => by
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij], fun i => by simp, by simp [h_zero_right hh]⟩
  simpa [Pi.single_apply, ite_smul] using this

theorem f_mem {Λ : AddSubgroup V} (hA : IsAdapted h e f W (fun _ => 1) Λ) (hh : IsHerm s h) (j : Fin l) :
    f j ∈ Λ := by
  have := (hA 0 (Pi.single j 1) 0 W.zero_mem).2 ⟨fun i => by simp, fun i => by
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij], by simp [h_zero_right hh]⟩
  simpa [Pi.single_apply, ite_smul] using this

theorem piece_mem {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (hA : IsAdapted h e f W (fun _ => 1) Λ)
    (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) {x : V} (hx : x ∈ Λ) :
    piece hh δ e f i x ∈ Λ := by
  obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
  obtain ⟨ha, hb, hww⟩ := (hA a b w hw).1 hx
  rcases i with _ | i | i
  · have : piece hh δ e f none (∑ i, a i • e i + ∑ i, b i • f i + w) = w := by
      simp [map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    have := (hA 0 0 w hw).2 ⟨fun i => by simp, fun i => by simp, hww⟩
    simpa using this
  · have : piece hh δ e f (some (Sum.inl i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = a i • e i := by
      simp [map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    exact lat_smul hΛ (by simpa using ha i) (e_mem hA hh i)
  · have : piece hh δ e f (some (Sum.inr i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = b i • f i := by
      simp [map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    exact lat_smul hΛ (by simpa using hb i) (f_mem hA hh i)

theorem tor_piece (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) {u : Fin l → L}
    {t : V ≃ₗ[L] V} (ht : IsTor s e f W u t) (i : Idx l) :
    (t.toLinearMap : Module.End L V) * piece hh δ e f i = tau s u i • piece hh δ e f i ∧
      piece hh δ e f i * (t.toLinearMap : Module.End L V) = tau s u i • piece hh δ e f i := by
  obtain ⟨t1, t2, t3⟩ := ht
  constructor
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_e hh hδ hF, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t1]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_f hh hδ hF, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t2]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_w hh hF _ hw, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t3 w hw]
      · simp
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t1, map_smul,
        piece_e hh hδ hF]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t2, map_smul,
        piece_f hh hδ hF]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t3 w hw,
        piece_w hh hF _ hw]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp

theorem wt_le {l : ℕ} (i : Idx l) : wt i ≤ 2 * l := by
  rcases i with _ | i | i <;> simp only [wt] <;> omega

theorem wt_injective {l : ℕ} : Function.Injective (wt : Idx l → ℕ) := by
  rintro (_ | i | i) (_ | j | j) hij <;> simp only [wt] at hij <;>
    first
    | rfl
    | (exfalso; have := i.2; omega)
    | (exfalso; have := j.2; omega)
    | (exfalso; have := i.2; have := j.2; omega)
    | (congr 2; apply Fin.ext; have := i.2; have := j.2; omega)

theorem wt_rev {l : ℕ} (i : Idx l) : wt (rev i) + wt i = 2 * l := by
  rcases i with _ | i | i
  · simp only [wt, rev]; omega
  · simp only [wt, rev]; have := i.2; omega
  · simp only [wt, rev]; have := i.2; omega

theorem rev_rev {l : ℕ} (i : Idx l) : rev (rev i) = i := by
  rcases i with _ | i | i <;> rfl

theorem tau_mono (hs : IsInv s) {u : Fin l → L} (hu0 : ∀ i, u i ≠ 0) (hm : Monotone fun i => ‖u i‖)
    (h1 : ∀ i, ‖u i‖ ≤ 1) (i j : Idx l) (hij : wt i ≤ wt j) : ‖tau s u i‖ ≤ ‖tau s u j‖ := by
  have hinv : ∀ m, 1 ≤ ‖(s (u m))⁻¹‖ := fun m => by
    rw [norm_inv, hs.2.1]
    exact (one_le_inv₀ (norm_pos_iff.2 (hu0 m))).2 (h1 m)
  rcases i with _ | i | i <;> rcases j with _ | j | j <;> simp only [wt] at hij <;> simp only [tau]
  · simp
  · have := j.2; omega
  · simpa using hinv j
  · simpa using h1 i
  · have hij' : i ≤ j := by rw [Fin.le_def]; exact hij
    exact hm hij'
  · exact (h1 i).trans (hinv j)
  · have := i.2; omega
  · have := i.2; have := j.2; omega
  · rw [norm_inv, norm_inv, hs.2.1, hs.2.1]
    refine inv_anti₀ (norm_pos_iff.2 (hu0 j)) (hm ?_)
    have := i.2; have := j.2
    rw [Fin.le_def]; omega

theorem tau_ne {u : Fin l → L} (hu0 : ∀ i, u i ≠ 0) (i : Idx l) : tau s u i ≠ 0 := by
  rcases i with _ | i | i
  · simp [tau]
  · simpa [tau] using hu0 i
  · simpa [tau] using hu0 i

theorem h_smul_left (hh : IsHerm s h) (c : L) (x y : V) : h (c • x) y = s c * h x y := by
  rw [hh.2.2.1 y (c • x), hh.2.1, map_mul, ← hh.2.2.1 y x]

theorem h_add_left (hh : IsHerm s h) (x x' y : V) : h (x + x') y = h x y + h x' y := by
  rw [hh.2.2.1 y (x + x'), hh.1, map_add, ← hh.2.2.1 y x, ← hh.2.2.1 y x']

theorem h_zero_left (hh : IsHerm s h) (y : V) : h 0 y = 0 := by
  rw [hh.2.2.1 y 0, h_zero_right hh, map_zero]

theorem h_sum_left (hh : IsHerm s h) {ι : Type} (A : Finset ι) (v : ι → V) (y : V) :
    h (∑ m ∈ A, v m) y = ∑ m ∈ A, h (v m) y :=
  map_sum (⟨⟨fun x => h x y, h_zero_left hh y⟩, fun x x' => h_add_left hh x x' y⟩ : V →+ L) v A

theorem h_sub_left (hh : IsHerm s h) (x x' y : V) : h (x - x') y = h x y - h x' y := by
  rw [hh.2.2.1 y (x - x'), h_sub_right hh, map_sub, ← hh.2.2.1 y x, ← hh.2.2.1 y x']

theorem projE_adj (hs : IsInv s) (hh : IsHerm s h) (i : Fin l) (x y : V) :
    h (projE hh δ e f i x) y = h x (projF hh δ e f i y) := by
  rw [projE_apply, projF_apply, h_smul_left hh, hh.2.1, map_mul, map_inv₀, hs.1, ← hh.2.2.1 (f i) x]
  ring

theorem projF_adj (hs : IsInv s) (hh : IsHerm s h) (i : Fin l) (x y : V) :
    h (projF hh δ e f i x) y = h x (projE hh δ e f i y) := by
  rw [projE_apply, projF_apply, h_smul_left hh, hh.2.1, map_mul, map_inv₀, ← hh.2.2.1 (e i) x]
  ring

theorem piece_adj (hs : IsInv s) (hh : IsHerm s h) (i : Idx l) (x y : V) :
    h (piece hh δ e f i x) y = h x (piece hh δ e f (rev i) y) := by
  rcases i with _ | i | i
  · have hx := map_sum (hLin hh x) (fun m => projE hh δ e f m y + projF hh δ e f m y) Finset.univ
    simp only [hLin_apply] at hx
    simp only [piece, rev, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply,
      LinearMap.add_apply, h_sub_left hh, h_sub_right hh, h_sum_left hh, hx, h_add_left hh, hh.1,
      projE_adj hs hh, projF_adj hs hh]
    congr 1
    exact Finset.sum_congr rfl fun m _ => add_comm _ _
  · exact projE_adj hs hh i x y
  · exact projF_adj hs hh i x y

theorem exists_star (hs : IsInv s) (hh : IsHerm s h)
    (hadj : ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y)) :
    ∃ st : Module.End L V → Module.End L V, (∀ g x y, h (g x) y = h x (st g y)) ∧
      (∀ a b, st (a * b) = st b * st a) ∧ st 1 = 1 ∧ st 0 = 0 ∧
      ∀ i : Idx l, st (piece hh δ e f i) = piece hh δ e f (rev i) := by
  choose st hst using hadj
  refine ⟨st, hst, fun a b => ?_, ?_, ?_, fun i => ?_⟩
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst, Module.End.mul_apply, Module.End.mul_apply, ← hst, ← hst]
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst]; rfl
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst]; simp [h_zero_left hh, h_zero_right hh]
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst, piece_adj hs hh]

end Concrete

end GlobalTheory.CompanionTheory.Iwahori

end
