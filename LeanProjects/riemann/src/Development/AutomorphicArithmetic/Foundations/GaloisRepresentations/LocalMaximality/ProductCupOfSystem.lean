import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedDualRegularFormsFiniteCoverStatement

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 GlobalTheory.W1.Lef UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

private lemma lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) : lft (uni I J) = I := by
  have h : Finset.map ofLex.toEmbedding (Finset.map toLex.toEmbedding (I.disjSum J)) = I.disjSum J := by
    ext x
    simp
  simp only [lft, uni, h, Finset.toLeft_disjSum]

private lemma rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) : rgt (uni I J) = J := by
  have h : Finset.map ofLex.toEmbedding (Finset.map toLex.toEmbedding (I.disjSum J)) = I.disjSum J := by
    ext x
    simp
  simp only [rgt, uni, h, Finset.toRight_disjSum]

private lemma uni_lft_rgt' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (s : Finset (ι ⊕ₗ κ)) : uni (lft s) (rgt s) = s := by
  simp only [lft, rgt, uni, Finset.toLeft_disjSum_toRight]
  ext x
  simp

private lemma card_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) : (uni I J).card = I.card + J.card := by
  simp [uni]

private lemma card_split {ι : Type} [LinearOrder ι] (I : Finset ι) (i : ι) (hi : i ∈ I) :
    (I.filter (· ≤ i)).card + (I.filter (i ≤ ·)).card = I.card + 1 := by
  rw [← Finset.card_union_add_card_inter, Finset.filter_union_right]
  have h1 : I.filter (fun x => x ≤ i ∨ i ≤ x) = I := Finset.filter_true_of_mem (fun x _ => le_total x i)
  have h2 : I.filter (· ≤ i) ∩ I.filter (i ≤ ·) = {i} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, a⟩, _, b⟩
      exact le_antisymm a b
    · rintro rfl
      exact ⟨⟨hi, le_rfl⟩, hi, le_rfl⟩
  rw [h1, h2, Finset.card_singleton]

private lemma mem_acx_C {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (A : Finset ι → Submodule ℂ E)
    (w : ι → Module.End ℂ E) (n : ℤ) (c : Finset ι → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) := by
  simp [acx, Submodule.mem_pi]

private lemma omB_le_fixed {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (q : ℕ) (y : DR ℂ K)
    (hy : y ∈ omB ℂ K B q) : y ∈ ⋀[K]^q Ω[K⁄ℂ] := by
  refine Submodule.span_induction (p := fun y _ => y ∈ ⋀[K]^q Ω[K⁄ℂ]) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, -, v, -, rfl⟩
    exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range K q ⟨_, rfl⟩)
  · exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    exact Submodule.smul_of_tower_mem _ c ha

private lemma pk_filter {d : ℕ} (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) (hi : i ∈ I) :
    pk (I.filter (· ≤ i)) = pk I := by
  have hne : I.Nonempty := ⟨i, hi⟩
  have hmin : I.min' hne ∈ I.filter (· ≤ i) :=
    Finset.mem_filter.2 ⟨Finset.min'_mem _ _, Finset.min'_le _ _ hi⟩
  have hfne : (I.filter (· ≤ i)).Nonempty := ⟨_, hmin⟩
  simp only [pk, dif_pos hne, dif_pos hfne]
  apply le_antisymm
  · exact Finset.min'_le _ _ hmin
  · exact Finset.le_min' _ _ _ (fun y hy => Finset.min'_le _ _ (Finset.mem_filter.1 hy).1)

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private lemma muP_tmul' (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ[ℂ] w'' := by
  simp [muP]

private abbrev phi : F ⊗[ℂ] K →ₐ[ℂ] K ⊗[ℂ] K :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K)

private lemma phi_X {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (i : Fin (d + 1)) :
    phi (((sysP K x a).X i : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) = (((sysZ K x a).X i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) := by
  simp [phi, sysP, sysZ]

private lemma phi_Y {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (i : Fin (d + 1)) :
    phi (((sysP K x a).Y i : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) = (((sysZ K x a).Y i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) := by
  simp [phi, sysP, sysZ]

private lemma phi_u {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (i j : Fin (d + 1)) (L : Finset (Mi d)) :
    phi (((∏ l ∈ L, (sysP K x a).u n11 i j l : (F ⊗[ℂ] K)ˣ)) : F ⊗[ℂ] K) =
      ((∏ l ∈ L, (sysZ K x a).u n11 i j l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) := by
  simp only [Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  simp only [Sys.u, n11, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, phi_X, phi_Y]

private lemma phi_mu {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (l : Mi d) :
    phi ((sysP K x a).mu l) = (sysZ K x a).mu l := by
  simp only [Sys.mu, map_sub, map_mul, phi_X, phi_Y]

private lemma term_mem {d : ℕ} (x : Fin (d + 1) → Fˣ) (hfin : IsFinCover ℂ K (xv x)) (τ : DR ℂ K →ₗ[K] K)
    (hτ : IsTop ℂ K (xv x) τ) (a : ℕ) (had : a ≤ d)
    (h6 : ∀ (s : F ⊗[ℂ] K) m w, muP F K τ (actZ K (phi s) m) w = (sysP K x a).act s (muP F K τ m w))
    (hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q)
    (I I' I'' J : Finset (Fin (d + 1))) (L : Finset (Mi d)) (hI' : I'.Nonempty) (hI'' : I''.Nonempty)
    (hs' : I' ⊆ I) (hs'' : I'' ⊆ I) (hpk : pk I' = pk I) (m : DR ℂ K ⊗[ℂ] DR ℂ K)
    (hm : m ∈ ((sysZ K x a).M I' J).map
      ((sysZ K x a).act ((∏ l ∈ L, (sysZ K x a).u n11 (pk I') (pk J) l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)))
    (y : DR ℂ K) (hy : y ∈ omB ℂ K (rB ℂ K (xv x) I'') a) :
    muP F K τ m y ∈ ((sysP K x a).M I J).map
      ((sysP K x a).act ((∏ l ∈ L, (sysP K x a).u n11 (pk I) (pk J) l : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K)) := by
  obtain ⟨m0, hm0, rfl⟩ := Submodule.mem_map.1 hm
  have hU : ((∏ l ∈ L, (sysZ K x a).u n11 (pk I') (pk J) l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      phi ((∏ l ∈ L, (sysP K x a).u n11 (pk I) (pk J) l : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) := by
    rw [phi_u, hpk]
  have e : muP F K τ ((sysZ K x a).act ((∏ l ∈ L, (sysZ K x a).u n11 (pk I') (pk J) l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) m0) y =
      (sysP K x a).act ((∏ l ∈ L, (sysP K x a).u n11 (pk I) (pk J) l : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K)
        (muP F K τ m0 y) := by
    rw [hU]
    exact h6 _ m0 y
  rw [e]
  refine Submodule.mem_map_of_mem ?_
  have hne : I.Nonempty := hI'.mono hs'
  have hyI : y ∈ omB ℂ K (rB ℂ K (xv x) I) a := hmono a I'' I hI'' hs'' hy
  have key : ∀ w' ∈ omB ℂ K (rB ℂ K (xv x) I') (d - a), ∀ w'' ∈ omB ℂ K (rB ℂ K (xv x) J) a,
      muP F K τ (w' ⊗ₜ w'') y ∈ (sysP K x a).M I J := by
    intro w' hw' w'' hw''
    rw [muP_tmul']
    have hw'I : w' ∈ omB ℂ K (rB ℂ K (xv x) I) (d - a) := hmono (d - a) I' I hI' hs' hw'
    have htr := (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) hfin τ hτ I hne (d - a) a (Nat.sub_add_cancel had) y
      (omB_le_fixed _ a y hyI)).2 hyI w' hw'I
    exact Submodule.apply_mem_map₂ _ htr hw''
  have hle : Submodule.map₂ (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K)) (omB ℂ K (rB ℂ K (xv x) I') (d - a))
      (omB ℂ K (rB ℂ K (xv x) J) a) ≤ ((sysP K x a).M I J).comap ((muP F K τ).flip y) :=
    Submodule.map₂_le.2 (fun w' hw' w'' hw'' => key w' hw' w'' hw'')
  exact hle hm0

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.pCup_of :
    RCup → SysBasic → SysOk → ActsLin → GoodZ → PCup := by
  intro hR hB hOk hA hG
  unfold PCup
  intro F K _ _ _ _ _ _ d x hfin τ hτ a p had c hc hdiag α hα
  obtain ⟨hcC, hcD⟩ := Submodule.mem_inf.1 hc
  obtain ⟨hαC, hαD⟩ := Submodule.mem_inf.1 hα
  have hAL := hA F K d x hfin τ hτ a
  have h6 : ∀ (s : F ⊗[ℂ] K) m w, muP F K τ (actZ K (phi (F := F) (K := K) s) m) w =
      (sysP K x a).act s (muP F K τ m w) := hAL.2.2.2.2.2
  have hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q := fun q => (hG F K d x hfin q).2.2
  have hcv := (mem_acx_C _ _ _ c).1 hcC
  have hcz : ∀ (I J : Finset (Fin (d + 1))) (L : Finset (Mi d)),
      ¬ (I.card + J.card + L.card = d + 2 ∧ I.Nonempty ∧ J.Nonempty) → c (uni (uni I J) L) = 0 := by
    intro I J L h
    have hv := hcv (uni (uni I J) L)
    rw [card_uni', card_uni', mixF, lft_uni', lft_uni', rgt_uni'] at hv
    split_ifs at hv with h1 h2
    · exact absurd ⟨by push_cast at h1; omega, h2⟩ h
    · exact (Submodule.mem_bot _).1 hv
    · exact (Submodule.mem_bot _).1 hv
  have hcm : ∀ (I J : Finset (Fin (d + 1))) (L : Finset (Mi d)), I.card + J.card + L.card = d + 2 →
      I.Nonempty → J.Nonempty → c (uni (uni I J) L) ∈ ((sysZ K x a).M I J).map
        ((sysZ K x a).act ((∏ l ∈ L, (sysZ K x a).u n11 (pk I) (pk J) l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)) := by
    intro I J L h h1 h2
    have hv := hcv (uni (uni I J) L)
    rw [card_uni', card_uni', mixF, lft_uni', lft_uni', rgt_uni', if_pos (by push_cast; omega),
      if_pos ⟨h1, h2⟩, rgt_uni'] at hv
    exact hv
  have hαv : ∀ s, α s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (p : ℤ) + 1 then omB ℂ K (rB ℂ K (xv x) s) a else ⊥) :=
    fun s => (Submodule.mem_pi.1 hαC) s (Set.mem_univ _)
  have hαz : ∀ s, ¬ (s.Nonempty ∧ s.card = p + 1) → α s = 0 := by
    intro s h
    have hv := hαv s
    rw [if_neg (fun h' => h ⟨h'.1, by omega⟩)] at hv
    exact (Submodule.mem_bot _).1 hv
  have hαm : ∀ s, s.Nonempty → s.card = p + 1 → α s ∈ omB ℂ K (rB ℂ K (xv x) s) a := by
    intro s h1 h2
    have hv := hαv s
    rw [if_pos ⟨h1, by omega⟩] at hv
    exact hv
  have hterm : ∀ (I J : Finset (Fin (d + 1))) (L : Finset (Mi d)) (i : Fin (d + 1)), i ∈ I →
      muP F K τ (c (uni (uni (I.filter (· ≤ i)) J) L)) (α (I.filter (i ≤ ·))) ∈
        (if ((uni (uni I J) L).card : ℤ) = ↑d + ↑p + 2 then
          mixF (fun I J => Submodule.map ((sysP K x a).act
            ((∏ l ∈ L, (sysP K x a).u n11 (pk I) (pk J) l : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K)) ((sysP K x a).M I J))
            (uni I J) else ⊥) := by
    intro I J L i hi
    have hfne : (I.filter (· ≤ i)).Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, le_rfl⟩⟩
    have hgne : (I.filter (i ≤ ·)).Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, le_rfl⟩⟩
    by_cases h1 : (I.filter (· ≤ i)).card + J.card + L.card = d + 2 ∧ J.Nonempty
    swap
    · rw [hcz _ _ _ (fun h => h1 ⟨h.1, h.2.2⟩), map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    by_cases h2 : (I.filter (i ≤ ·)).card = p + 1
    swap
    · rw [hαz _ (fun h => h2 h.2), map_zero]
      exact Submodule.zero_mem _
    have hsplit := card_split I i hi
    have hIne : I.Nonempty := ⟨i, hi⟩
    rw [if_pos (by rw [card_uni', card_uni']; push_cast; omega), mixF, lft_uni', rgt_uni', if_pos ⟨hIne, h1.2⟩]
    exact term_mem x hfin τ hτ a had h6 hmono I _ _ J L hfne hgne (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) (pk_filter I i hi) _ (hcm _ _ _ h1.1 hfne h1.2) _ (hαm _ hgne h2)
  refine ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Sys.cx, mem_acx_C]
    intro s
    obtain ⟨I, J, L, rfl⟩ : ∃ I J L, s = uni (uni I J) L :=
      ⟨lft (lft s), rgt (lft s), rgt s, by rw [uni_lft_rgt', uni_lft_rgt']⟩
    have hsum := Submodule.sum_mem _ (fun i hi => hterm I J L i hi)
    simp only [rcup, lft_uni', rgt_uni']
    first
      | exact Submodule.smul_of_tower_mem _ _ hsum
      | exact Submodule.smul_mem _ _ hsum
  · rw [LinearMap.mem_ker]
    have hz : ∀ (l : Mi d) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (y : DR ℂ K),
        muP F K τ ((sysZ K x a).act ((sysZ K x a).mu l) m) y =
          (sysP K x a).act ((sysP K x a).mu l) (muP F K τ m y) := by
      intro l m y
      have := h6 ((sysP K x a).mu l) m y
      rw [phi_mu] at this
      exact this
    exact hR d _ _ (sysZ K x a) _ _ _ (sysP K x a) (Mi d) _ _ (muP F K τ) p c α hz
      (LinearMap.mem_ker.1 hcD)
      (fun J L => hcz _ _ _ (fun h => Finset.not_nonempty_empty h.2.1))
      (LinearMap.mem_ker.1 hαD) (fun I h => hαz I (fun h' => h h'.2))
  · intro b L hL
    simp only [rcup, lft_uni', rgt_uni']
    rw [Finset.sum_eq_zero, smul_zero]
    intro i hi
    rw [hcz _ _ _ (fun h => ?_), map_zero, LinearMap.zero_apply]
    have h1 := h.2.1.card_pos
    have h2 := h.2.2.card_pos
    omega
  · intro b L hL
    simp only [rcup, lft_uni', rgt_uni', edge1]
    generalize lft b = I
    generalize rgt b = J
    by_cases hJ : J.card = 1
    · rw [if_pos hJ]
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hJ
      have hαI : α I ∈ ⋀[K]^a Ω[K⁄ℂ] := by
        by_cases h : I.Nonempty ∧ I.card = p + 1
        · exact omB_le_fixed _ a _ (hαm I h.1 h.2)
        · rw [hαz I h]
          exact Submodule.zero_mem _
      rcases I.eq_empty_or_nonempty with hI | hI
      · subst hI
        rw [Finset.sum_empty, smul_zero, map_zero, hαz ∅ (fun h => Finset.not_nonempty_empty h.1),
          smul_zero, smul_zero]
      · have hmin := Finset.min'_mem I hI
        rw [Finset.sum_eq_single_of_mem _ hmin ?_]
        · have hf1 : I.filter (· ≤ I.min' hI) = {I.min' hI} := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · rintro ⟨hy, hle⟩
              exact le_antisymm hle (Finset.min'_le _ _ hy)
            · rintro rfl
              exact ⟨hmin, le_rfl⟩
          have hf2 : I.filter (I.min' hI ≤ ·) = I := Finset.filter_true_of_mem (fun y hy => Finset.min'_le _ _ hy)
          rw [hf1, hf2]
          have hact := hdiag (I.min' hI) j L hL _ hαI
          rw [LinearMap.map_smul_of_tower, hact, Finset.card_singleton, hL]
          rw [← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K, smul_smul, smul_smul]
          congr 1
          push_cast
          ring
        · intro i hi hne
          rw [hcz _ _ _ (fun h => ?_), map_zero, LinearMap.zero_apply]
          have hsub : ({I.min' hI, i} : Finset (Fin (d + 1))) ⊆ I.filter (· ≤ i) := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_filter.2 ⟨hmin, Finset.min'_le _ _ hi⟩
            · exact Finset.mem_filter.2 ⟨hi, le_rfl⟩
          have hc2 := Finset.card_le_card hsub
          rw [Finset.card_pair (Ne.symm hne)] at hc2
          rw [Finset.card_singleton] at h
          omega
    · rw [if_neg hJ, smul_zero, smul_zero, Finset.sum_eq_zero, smul_zero, map_zero]
      intro i hi
      rw [hcz _ _ _ (fun h => ?_), map_zero, LinearMap.zero_apply]
      have h1 := h.2.1.card_pos
      have h2 := h.2.2.card_pos
      omega
