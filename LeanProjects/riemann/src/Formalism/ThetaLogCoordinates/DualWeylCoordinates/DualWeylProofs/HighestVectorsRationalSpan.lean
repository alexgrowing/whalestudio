import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.TranslatesSpanCanonical
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbBasisApply

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qd_ev_point (M : GLMod n) (nu : Fin n → ℤ) (x : M.ι → ℚ) {R' : Type} [CommRing R'] [Algebra ℚ R']
    (g : GL (Fin n) R') (i : M.ι) :
    evGLR (R := ℚ) g (qb_ev M ℚ nu x i) =
      Matrix.mulVec ((prMu M nu).map (Int.castRingHom R'))
        (Matrix.mulVec (M.A.map (evGL g)) (fun l => algebraMap ℚ R' (x l))) i := by
  rw [qb_ev_apply]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_intCast, qd_evGLR_mapCoord, qd_ev_algebraMap,
    Matrix.map_apply, Int.coe_castRingHom]

lemma qd_ev_inv (M : GLMod n) (la nu : Fin n → ℤ) (x : M.ι → ℚ) (hx : IsHighest M ℚ la x)
    {R' : Type} [CommRing R'] [Algebra ℚ R'] (g u : GL (Fin n) R') (hu1 : ∀ a, u.val a a = 1)
    (hu2 : ∀ a b, b < a → u.val a b = 0) (i : M.ι) :
    evGLR (R := ℚ) (g * u) (qb_ev M ℚ nu x i) = evGLR (R := ℚ) g (qb_ev M ℚ nu x i) := by
  rw [qd_ev_point, qd_ev_point, M.mul, ← Matrix.mulVec_mulVec, hx.2 R' u hu1 hu2]

variable [NeZero n]

lemma qd_canT_std (mu : Fin n → ℤ) : StdT (canT mu) := by
  intro c hc t
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x hx
  simp only [canT, Finset.mem_map, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  have hle : colH mu ((c : ℤ) + 1) ≤ colH mu c := by
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    omega
  exact ⟨⟨a.1, lt_of_lt_of_le a.2 hle⟩, rfl⟩

def qd_f {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (j : CF.J) : GLCoord ℚ n :=
  ∑ I : {I : TIdx (CF.mu j) // StdT I}, a ⟨j, I⟩ • mapCoord ℚ (brk (CF.mu j) I.1)

lemma qd_f_mem {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (j : CF.J) :
    qd_f CF a j ∈ Submodule.span ℚ (Set.range fun I : TIdx (CF.mu j) => mapCoord ℚ (brk (CF.mu j) I)) :=
  Submodule.sum_mem _ fun I _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨I.1, rfl⟩)

lemma qd_ev_expand {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (nu : Fin n → ℤ)
    (hmax : ∀ y, a y ≠ 0 → DomLE nu (CF.mu y.1) → CF.mu y.1 = nu) (i : M.ι) :
    qb_ev M ℚ nu (∑ y, a y • qb_vecF CF ℚ y) i =
      ∑ j : {j : CF.J // CF.mu j = nu}, ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : ℚ) • qd_f CF a j.1 := by
  classical
  rw [← qb_evL_apply, map_sum, Finset.sum_apply, Fintype.sum_sigma,
    ← Finset.sum_subtype (univ.filter fun j => CF.mu j = nu) (by simp)
      (fun j => ((CF.ph j i (canT (CF.mu j)) : ℤ) : ℚ) • qd_f CF a j), Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · subst hj
    rw [qd_f, Finset.smul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, Pi.smul_apply, qb_evL_apply, qb_vecF_def, qb_key_eq, smul_comm, Algebra.smul_def (R := ℚ)
      ((CF.ph j i (canT (CF.mu j)) : ℤ) : ℚ), map_intCast]
  · refine Finset.sum_eq_zero fun I _ => ?_
    rw [map_smul, Pi.smul_apply, qb_evL_apply, qb_vecF_def]
    by_cases ha : a ⟨j, I⟩ = 0
    · rw [ha, zero_smul]
    · rw [qb_key_zero CF ℚ j I.1 nu (fun hd => hj (hmax ⟨j, I⟩ ha hd)), Pi.zero_apply, smul_zero]

theorem highest_vectors_rational_span_of : LemmaA → HighestVectorsRationalSpan := by
  intro hA n _ M CF la hla x hx
  classical
  have hsp := (qb_basisR hA CF ℚ).2
  have hli := (qb_basisR hA CF ℚ).1
  obtain ⟨a, ha⟩ : ∃ a : qb_Idx CF → ℚ, ∑ y, a y • qb_vecF CF ℚ y = x := by
    have : x ∈ Submodule.span ℚ (Set.range (qb_vecF CF ℚ)) := by rw [hsp]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).1 this
  subst ha

  have h1 : ∀ y, a y ≠ 0 → qb_wtT (CF.mu y.1) y.2.1 = la := by
    have hpr : ∀ y, Matrix.mulVec ((prMu M la).map (Int.castRingHom ℚ)) (qb_vecF CF ℚ y) =
        if qb_wtT (CF.mu y.1) y.2.1 = la then qb_vecF CF ℚ y else 0 := by
      intro y
      funext i
      have := congrArg (Int.cast : ℤ → ℚ) (qb_prMu_ph CF y.1 la i y.2.1)
      push_cast at this
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.coe_castRingHom, qb_vecF, ColFam.vec]
      rw [this]
      split_ifs <;> rfl
    have h : Matrix.mulVecLin ((prMu M la).map (Int.castRingHom ℚ)) (∑ y, a y • qb_vecF CF ℚ y) =
        ∑ y, a y • qb_vecF CF ℚ y := hx.1
    rw [map_sum] at h
    simp only [map_smul, Matrix.mulVecLin_apply, hpr, smul_ite, smul_zero] at h
    have h0 := Fintype.linearIndependent_iff.1 hli
      (fun y => (if qb_wtT (CF.mu y.1) y.2.1 = la then a y else 0) - a y) (by
        simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul]
        rw [sub_eq_zero]
        exact h)
    intro y hy
    by_contra hne
    have := h0 y
    simp only [if_neg hne, zero_sub, neg_eq_zero] at this
    exact hy this

  have h3 : ∀ nu, (∀ y, a y ≠ 0 → DomLE nu (CF.mu y.1) → CF.mu y.1 = nu) →
      ∀ y, CF.mu y.1 = nu → a y ≠ 0 → y.2.1 = canT (CF.mu y.1) := by
    intro nu hmax
    have hinv : ∀ (j : {j : CF.J // CF.mu j = nu}) (R' : Type) [CommRing R'] [Algebra ℚ R'] (g u : GL (Fin n) R'),
        (∀ a, u.val a a = 1) → (∀ a b, b < a → u.val a b = 0) →
        evGLR (R := ℚ) (g * u) (qd_f CF a j.1) = evGLR (R := ℚ) g (qd_f CF a j.1) := by
      intro j R' _ _ g u hu1 hu2
      have := qb_indep_ext (k := ℚ) (W := R') _ (CF.indepQ nu)
        (fun j => evGLR (R := ℚ) (g * u) (qd_f CF a j.1) - evGLR (R := ℚ) g (qd_f CF a j.1)) (fun i => ?_) j
      · exact sub_eq_zero.1 this
      · have e := qd_ev_inv M la nu _ hx g u hu1 hu2 i
        rw [qd_ev_expand CF a nu hmax i, map_sum, map_sum] at e
        simp only [smul_sub, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        convert e using 2 <;>
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, qd_ev_algebraMap]
    intro y hy hay
    obtain ⟨c, hc⟩ := eq_smul_canonical_of_unipotent_invariant (CF.mu y.1) (qd_f CF a y.1) (qd_f_mem CF a y.1) (hinv ⟨y.1, hy⟩)
    have hind := hA n (CF.mu y.1) (CF.dom y.1) ℚ
    by_contra hne
    have := Fintype.linearIndependent_iff.1 hind
      (fun I => a ⟨y.1, I⟩ - if I = ⟨canT (CF.mu y.1), qd_canT_std _⟩ then c else 0) (by
        simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
          if_true]
        rw [sub_eq_zero]
        exact hc) y.2
    rw [if_neg (fun h => hne (congrArg Subtype.val h)), sub_zero] at this
    exact hay this
  have h4 : ∀ y, a y ≠ 0 → CF.mu y.1 = la ∧ y.2.1 = canT (CF.mu y.1) := by
    intro y0 hy0
    let s : Finset (Fin n → ℤ) := (univ.filter fun y => a y ≠ 0).image fun y => CF.mu y.1
    have hs0 : CF.mu y0.1 ∈ s := mem_image.2 ⟨y0, by simp [hy0], rfl⟩
    obtain ⟨nu, hnu, hle, hmax⟩ := qb_exists_max_above s hs0
    obtain ⟨y1, hy1, hy1nu⟩ := mem_image.1 hnu
    have hay1 : a y1 ≠ 0 := by simpa using hy1
    have hmax' : ∀ y, a y ≠ 0 → DomLE nu (CF.mu y.1) → CF.mu y.1 = nu :=
      fun y hy hd => hmax _ (mem_image.2 ⟨y, by simp [hy], rfl⟩) hd
    have hcan := h3 nu hmax' y1 hy1nu hay1
    have hw := h1 y1 hay1
    rw [hcan, qb_wtT_can (CF.dom y1.1)] at hw
    have hnula : nu = la := hy1nu.symm.trans hw
    have hle2 : DomLE la (CF.mu y0.1) := by
      rw [← h1 y0 hy0]; exact qb_wtT_le (CF.dom _) _
    have heq : CF.mu y0.1 = la := qb_domLE_antisymm (hnula ▸ hle) hle2
    exact ⟨heq, (qb_wtT_eq_iff (CF.dom _) _).1 ((h1 y0 hy0).trans heq.symm)⟩
  refine Submodule.sum_mem _ fun y _ => ?_
  by_cases hy : a y = 0
  · rw [hy, zero_smul]; exact zero_mem _
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    obtain ⟨e1, e2⟩ := h4 y hy
    refine ⟨y.1, e1, ?_⟩
    funext i
    simp only [qb_vecF]
    rw [e2]

end Formalism.InvariantFactorPaths.ColumnFamilies
