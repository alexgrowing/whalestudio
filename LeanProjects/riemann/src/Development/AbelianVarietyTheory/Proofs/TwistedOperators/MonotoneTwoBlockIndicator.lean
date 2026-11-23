import Mathlib
import Formalism.JacquetSubsetSums.JacquetSubsetSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermMatrixRepParabolicDoubleCoset

noncomputable section

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors GlobalTheory.Parabolic GlobalTheory.FiniteGL

namespace GlobalTheory.GoodNoFixed

theorem mem_radical_iff {k : Type} [Field k] {r a : ℕ} {u : GL (Fin r) k} :
    u ∈ radical k r a ↔ u ∈ unipRadical k (blk2 a) := by
  rw [GlobalTheory.FiniteGL.mem_unipRadical]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical, Set.mem_ofPred_eq]
  constructor
  · intro h i j hij
    rw [Matrix.sub_apply, sub_eq_zero]
    by_contra hne
    obtain ⟨h1, h2⟩ := h i j hne
    simp only [Formalism.L2.DIV.blk2] at hij
    split_ifs at hij <;> omega
  · intro h i j hne
    by_contra hc
    apply hne
    rw [← sub_eq_zero, ← Matrix.sub_apply]
    apply h
    simp only [Formalism.L2.DIV.blk2]
    by_cases hi : (i : ℕ) < a
    · have hj : (j : ℕ) < a := by
        by_contra hj
        exact hc ⟨hi, by omega⟩
      split_ifs <;> omega
    · split_ifs <;> omega

theorem monotone_twoBlockIndicator {r : ℕ} (a : ℕ) : Monotone (blk2 (n := r) a) := by
  intro i j hij
  rw [Fin.le_iff_val_le_val] at hij
  simp only [Formalism.L2.DIV.blk2]
  split_ifs <;> omega

private theorem mem_map_castLEEmb_trans_perm_iff {r a : ℕ} (ha : a ≤ r) (w : Equiv.Perm (Fin r)) (i : Fin r) :
    i ∈ Finset.univ.map ((Fin.castLEEmb ha).trans w.toEmbedding) ↔ (w.symm i : ℕ) < a := by
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
    Fin.castLEEmb_apply, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [show Fin.castLE ha ⟨(w.symm i : ℕ), h⟩ = w.symm i from Fin.ext rfl]
    simp

theorem exists_union_of_blocks {k : Type} [Field k] {r : ℕ} {b : Fin r → ℕ} (hb : Monotone b) {Y : Type} [Zero Y]
    (ρ : blockTri (κ := k) b → Y → Y) (hρ : ∀ q, ρ q 0 = 0)
    (cusp : ∀ S : Finset (Fin r), (∃ i j, b i = b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : Y,
      (∀ u : blockTri (κ := k) b, (∀ i j, ((u : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) i j ≠
        (1 : Matrix (Fin r) (Fin r) k) i j → b i = b j ∧ i ∈ S ∧ j ∉ S) → ρ u y = y) → y = 0)
    {a : ℕ} (ha : a ≤ r) (φ : GL (Fin r) k → Y)
    (hl : ∀ (q : blockTri (κ := k) b) (x : GL (Fin r) k), φ (q * x) = ρ q (φ x))
    (hr : ∀ x, ∀ n ∈ radical k r a, φ (x * n) = φ x) (x : GL (Fin r) k) (hx : φ x ≠ 0) :
    ∃ S : Finset (Fin r), S.card = a ∧ ∀ i j, b i = b j → i ∈ S → j ∈ S := by
  obtain ⟨w, p', p, hxe⟩ := GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri k r (blk2 a) b (monotone_twoBlockIndicator a) hb x
  have hy : φ (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)) ≠ 0 := by
    intro h0
    apply hx
    rw [hxe, mul_assoc, hl p', h0, hρ]
  have hS := mem_map_castLEEmb_trans_perm_iff ha w
  refine ⟨Finset.univ.map ((Fin.castLEEmb ha).trans w.toEmbedding), by simp, fun i j hij hi => ?_⟩
  by_contra hj
  apply hy
  refine cusp _ ⟨i, j, hij, hi, hj⟩ _ fun u hu => ?_
  have hm : (GlobalTheory.Parabolic.permGL k w)⁻¹ * (u : GL (Fin r) k) * GlobalTheory.Parabolic.permGL k w ∈ radical k r a := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical, Set.mem_ofPred_eq]
    intro i' j' hne
    have he := GlobalTheory.Parabolic.conj_permGL_apply (k := k) w⁻¹ (u : GL (Fin r) k) (w i') (w j')
    rw [map_inv, inv_inv] at he
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at he
    rw [he] at hne
    have h1 : (1 : Matrix (Fin r) (Fin r) k) (w i') (w j') = (1 : Matrix (Fin r) (Fin r) k) i' j' := by
      by_cases h : i' = j'
      · subst h; simp
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun e => h (w.injective e))]
    rw [← h1] at hne
    obtain ⟨-, hi', hj'⟩ := hu _ _ hne
    rw [hS] at hi' hj'
    simp only [Equiv.symm_apply_apply] at hi' hj'
    exact ⟨hi', not_lt.1 hj'⟩
  have hm' : (p : GL (Fin r) k)⁻¹ * ((GlobalTheory.Parabolic.permGL k w)⁻¹ * (u : GL (Fin r) k) *
      GlobalTheory.Parabolic.permGL k w) * (p : GL (Fin r) k) ∈ radical k r a := by
    rw [mem_radical_iff] at hm ⊢
    have hn := GlobalTheory.Parabolic.blockTri_le_normalizer (k := k) (blk2 (n := r) a) (Subgroup.inv_mem _ p.2)
    have := (Subgroup.mem_normalizer_iff.1 hn _).1 hm
    simpa only [inv_inv, SetLike.mem_coe] using this
  calc ρ u (φ (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)))
      = φ ((u : GL (Fin r) k) * (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k))) := (hl u _).symm
    _ = φ ((GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)) * ((p : GL (Fin r) k)⁻¹ *
        ((GlobalTheory.Parabolic.permGL k w)⁻¹ * (u : GL (Fin r) k) * GlobalTheory.Parabolic.permGL k w) *
        (p : GL (Fin r) k))) := by congr 1; group
    _ = φ (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)) := hr _ _ hm'

theorem card_eq_sum_blocks {r : ℕ} {ι : Type} [DecidableEq ι] (b : Fin r → ι) (S : Finset (Fin r))
    (hS : ∀ i j, b i = b j → i ∈ S → j ∈ S) :
    S.card = ∑ c ∈ S.image b, (Finset.univ.filter fun i => b i = c).card := by
  rw [Finset.card_eq_sum_card_image b S]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  intro hj
  exact hS i j hj.symm hi

theorem fixedVectorBlocks : FixedVectorBlocks := by
  intro k _ _ r b W _ _ ρ hc V _ _ τ hsub a ha0 har hnf
  obtain ⟨T, hTi, hT⟩ := hsub
  unfold NoFixed at hnf
  push Not at hnf
  obtain ⟨v, hv, hv0⟩ := hnf
  have hTv : T v ≠ 0 := fun h => hv0 (hTi (h.trans (map_zero T).symm))
  obtain ⟨y, hy⟩ : ∃ y, ((T v : _) : GL (Fin r) k → W) y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hTv (Subtype.ext (funext hcon))
  have hl : ∀ (q : blockTri (κ := k) b) (z : GL (Fin r) k),
      ((T v : _) : GL (Fin r) k → W) (q * z) = ρ q (((T v : _) : GL (Fin r) k → W) z) :=
    fun q z => (T v).2 q z
  have hr : ∀ z, ∀ n ∈ radical k r a, ((T v : _) : GL (Fin r) k → W) (z * n) = ((T v : _) : GL (Fin r) k → W) z := by
    intro z n hn
    have h1 := LinearMap.congr_fun (hT n) v
    simp only [LinearMap.comp_apply] at h1
    rw [hv n hn] at h1
    have h2 := congrFun (congrArg Subtype.val h1) z
    exact h2.symm
  obtain ⟨S, hS, hU⟩ := exists_union_of_blocks (k := k) hc.mono (Y := W) (fun q w => ρ q w)
    (fun q => map_zero _) hc.cusp (le_of_lt har) _ hl hr y hy
  refine ⟨S.image b, Finset.image_subset_image (Finset.subset_univ _), ?_⟩
  rw [← hS, card_eq_sum_blocks b S hU]
  simp only [Fintype.card_subtype]

theorem map_mem_radical {k k' : Type} [CommRing k] [CommRing k'] (e : k →+* k') {r a : ℕ} {u : GL (Fin r) k}
    (hu : u ∈ radical k r a) : Matrix.GeneralLinearGroup.map e u ∈ radical k' r a := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical, Set.mem_ofPred_eq] at hu ⊢
  intro i j hij
  apply hu i j
  intro heq
  apply hij
  rw [Matrix.GeneralLinearGroup.map_apply]
  rw [heq]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem sum_character_eq_zero_iff {H V : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ H V) : ∑ h, τ.character h = 0 ↔ ∀ x : V, (∀ h, τ h x = x) → x = 0 := by
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.card_pos (α := H)).ne'
  haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hcard
  have h := τ.card_inv_mul_sum_char_eq_finrank
  constructor
  · intro hs x hx
    rw [hs, mul_zero] at h
    have h0 : Module.finrank ℂ τ.invariants = 0 := by exact_mod_cast h.symm
    have hb : τ.invariants = ⊥ := Submodule.finrank_eq_zero.1 h0
    have hxm : x ∈ τ.invariants := (τ.mem_invariants x).2 hx
    rw [hb] at hxm
    exact (Submodule.mem_bot ℂ).1 hxm
  · intro hx
    have hb : τ.invariants = ⊥ :=
      (Submodule.eq_bot_iff _).2 fun x hxm => hx x ((τ.mem_invariants x).1 hxm)
    rw [hb, finrank_bot, Nat.cast_zero] at h
    exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero hcard)

theorem noFixed_iff_sum {k : Type} [Field k] {r a : ℕ} [Fintype (unipRadical k (blk2 (n := r) a))] {G V : Type} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ G V) (ι : GL (Fin r) k →* G) :
    NoFixed τ (ι '' radical k r a) ↔ ∑ u : unipRadical k (blk2 (n := r) a), τ.character (ι u) = 0 := by
  refine Iff.trans ?_ (sum_character_eq_zero_iff (τ.comp (ι.comp (unipRadical k (blk2 (n := r) a)).subtype))).symm
  unfold NoFixed
  refine forall_congr' fun x => imp_congr_left ⟨fun hx h => hx _ ⟨h, mem_radical_iff.2 h.2, rfl⟩, ?_⟩
  rintro hx _ ⟨u, hu, rfl⟩
  exact hx ⟨u, mem_radical_iff.1 hu⟩

end GlobalTheory.GoodNoFixed
