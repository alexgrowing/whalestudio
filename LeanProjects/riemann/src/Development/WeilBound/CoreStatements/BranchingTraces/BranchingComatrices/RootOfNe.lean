import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliAbstractCharacter

open Finset Polynomial

noncomputable section

namespace PositivityTheory.UnitaryDecomposition.Com

open Formalism.REAL Formalism.FourierDecayAlt.P.CapelliAbstractCharacter

section Alg

variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V}
  {m : Fin (N + 1) → ℂ}

theorem th_mul (hE : GlRel E) (hq : ∀ u v, qdet E u v = (∏ j, (u + m j)) • v) {Y : Fin (N + 1) → V} {κ : ℂ}
    (hY : EE E Y = κ • Y) (u : ℂ) : (u - N + κ) • Th E u Y = (∏ j, (u + m j)) • Y := by
  funext i
  have h := comat E hE u Y i
  rw [hY, ← add_smul, map_smul, hq] at h
  exact h

theorem root_of_ne (hE : GlRel E) (hq : ∀ u v, qdet E u v = (∏ j, (u + m j)) • v) {Y : Fin (N + 1) → V} {κ : ℂ}
    (hY : EE E Y = κ • Y) (h0 : Y ≠ 0) : ∃ i, κ = N + m i := by
  have h := th_mul hE hq hY (N - κ)
  rw [show (N : ℂ) - κ - N + κ = 0 by ring, zero_smul, eq_comm, smul_eq_zero, or_iff_left h0, Finset.prod_eq_zero_iff] at h
  obtain ⟨i, -, hi⟩ := h
  exact ⟨i, by linear_combination -hi⟩

theorem th_eig (hE : GlRel E) (hq : ∀ u v, qdet E u v = (∏ j, (u + m j)) • v) {Y : Fin (N + 1) → V} (i : Fin (N + 1))
    (hY : EE E Y = (N + m i) • Y) (u : ℂ) : Th E u Y = (∏ j ∈ univ.erase i, (u + m j)) • Y := by
  obtain ⟨A, hA⟩ := Th_pol E
  have hQ : (∏ j ∈ univ.erase i, ((X : ℂ[X]) + C (m j))).natDegree < N + 1 :=
    lt_of_le_of_lt (deg_prod_lin _ _) (by simp [Finset.card_erase_of_mem])
  have hdiff : ∀ u : ℂ, Th E u Y - (∏ j ∈ univ.erase i, (u + m j)) • Y =
      ∑ s ∈ range (N + 1), u ^ s • (A s Y - (∏ j ∈ univ.erase i, ((X : ℂ[X]) + C (m j))).coeff s • Y) := by
    intro u
    rw [hA, ← eval_prod_lin, Polynomial.eval_eq_sum_range' hQ, Finset.sum_smul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [smul_sub, smul_smul, mul_comm]
  have hz := polyVanish (N + 1)
    (fun s => A s Y - (∏ j ∈ univ.erase i, ((X : ℂ[X]) + C (m j))).coeff s • Y) {-m i}
    (fun u hu => by
      rw [← hdiff]
      have hne : u + m i ≠ 0 := fun h => hu (by simp [eq_neg_of_add_eq_zero_left h])
      have hs := th_mul hE hq hY u
      rw [show u - N + (N + m i) = u + m i by ring] at hs
      have h0 : (u + m i) • (Th E u Y - (∏ j ∈ univ.erase i, (u + m j)) • Y) = 0 := by
        rw [smul_sub, smul_smul, Finset.mul_prod_erase univ (fun j => u + m j) (mem_univ i), hs, sub_self]
      exact (smul_eq_zero.1 h0).resolve_left hne)
  rw [← sub_eq_zero, hdiff]
  exact Finset.sum_eq_zero fun s hs => by rw [hz s hs, smul_zero]

theorem th_proj (hE : GlRel E) (hq : ∀ u v, qdet E u v = (∏ j, (u + m j)) • v) {ι : Type} (S : Finset ι)
    (Y : ι → Fin (N + 1) → V) (κ : ι → ℂ) (hκ : Set.InjOn κ S) (hY : ∀ t ∈ S, EE E (Y t) = κ t • Y t) {s : ι} (hs : s ∈ S)
    (i : Fin (N + 1)) (hi : κ s = N + m i) :
    Th E (-m i) (∑ t ∈ S, Y t) = (∏ j ∈ univ.erase i, (-m i + m j)) • Y s := by
  rw [map_sum, Finset.sum_eq_single_of_mem s hs fun t ht hts => ?_]
  · exact th_eig hE hq i (hi ▸ hY s hs) _
  · have h := th_mul hE hq (hY t ht) (-m i)
    rw [Finset.prod_eq_zero (mem_univ i) (by ring), zero_smul, smul_eq_zero] at h
    refine h.resolve_left fun h0 => hts (hκ ht hs ?_)
    rw [hi]; linear_combination h0

theorem th_single (u : ℂ) (l c : Fin (N + 1)) (v : V) :
    Th E u (Pi.single l v) c = ((-1 : ℂ) ^ ((l : ℕ) + (c : ℕ))) • qminor E l.succAbove c.succAbove u v := by
  rw [Th_apply, Finset.sum_eq_single l (fun a _ ha => by simp [Pi.single_eq_of_ne ha]) (by simp), Pi.single_eq_same]

theorem corner (hE : GlRel E) (z : Fin (N + 1)) (ι : Fin N → Fin (N + 1)) (hι : Function.Injective ι) (hz : ∀ a, ι a ≠ z)
    (u : ℂ) : qminor E z.succAbove z.succAbove u = qdet (fun a b => E (ι a) (ι b)) u := by
  choose f hf using fun a => Fin.exists_succAbove_eq (hz a)
  have hfi : Function.Injective f := fun a b h => hι (by rw [← hf a, ← hf b, h])
  let τ : Equiv.Perm (Fin N) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfi)
  have e : ι = z.succAbove ∘ τ := funext fun a => (hf a).symm
  have h1 : qdet (fun a b => E (ι a) (ι b)) u = qminor E ι ι u := by
    unfold qdet qminor Tm
    simp only [id, hι.eq_iff]
  rw [h1, e, quantumMinorRowSkew_holds, quantumMinorColSkew_holds _ _ _ _ hE, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

end Alg

theorem qdet_int {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}
    {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'} (f : V →ₗ[ℂ] V')
    (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (x : V) : f (qdet E u x) = qdet E' u (f x) := by
  have tm : ∀ w a b y, f (Tm E w a b y) = Tm E' w a b (f y) := fun w a b y => by
    unfold Tm
    split_ifs <;> simp [Module.algebraMap_end_apply, hf]
  have hl : ∀ (L : List (ℂ × Fin n × Fin n)) y, f ((L.map fun p => Tm E p.1 p.2.1 p.2.2).prod y) =
      (L.map fun p => Tm E' p.1 p.2.1 p.2.2).prod (f y) := fun L y => by
    induction L with
    | nil => simp
    | cons p L ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, tm, ih]
  unfold qdet qminor
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul]
  have := hl (List.ofFn fun k : Fin n => (u - (k : ℂ), σ k, k)) x
  simp only [List.map_ofFn] at this
  exact congrArg _ this

section Norm

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V}

theorem prod_bd {v : V} {S : ℕ} {M R : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hW : ∀ W : List (Fin n × Fin n), W.length ≤ S → ‖(W.map fun p => E p.1 p.2).prod v‖ ≤ M ^ W.length * ‖v‖) :
    ∀ (L : List (ℂ × Fin n × Fin n)), (∀ p ∈ L, ‖p.1‖ ≤ R) → ∀ W : List (Fin n × Fin n), W.length + L.length ≤ S →
      ‖(W.map fun p => E p.1 p.2).prod ((L.map fun p => Tm E p.1 p.2.1 p.2.2).prod v)‖ ≤
        (R + M) ^ L.length * M ^ W.length * ‖v‖
  | [], _, W, h => by simpa using hW W (by simpa using h)
  | p :: L, hL, W, h => by
    have hL' : ∀ q ∈ L, ‖q.1‖ ≤ R := fun q hq => hL q (List.mem_cons_of_mem _ hq)
    have h1 := prod_bd hR hM hW L hL' W (by simp at h; omega)
    have h2 := prod_bd hR hM hW L hL' (W ++ [p.2]) (by simp at h ⊢; omega)
    set y := (L.map fun p => Tm E p.1 p.2.1 p.2.2).prod v with hy
    have e : (((p :: L).map fun p => Tm E p.1 p.2.1 p.2.2).prod v) = (if p.2.1 = p.2.2 then p.1 else 0) • y + E p.2.1 p.2.2 y := by
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ← hy]
      unfold Tm
      split_ifs <;> simp [Module.algebraMap_end_apply]
    have hc : ‖(if p.2.1 = p.2.2 then p.1 else 0)‖ ≤ R := by
      split_ifs
      · exact hL p List.mem_cons_self
      · simpa [Function.comp_def] using hR
    simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Module.End.mul_apply, List.length_append, List.length_cons, List.length_nil, zero_add] at h2
    rw [e, map_add, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, List.length_cons]
    calc _ ≤ R * ((R + M) ^ L.length * M ^ W.length * ‖v‖) + (R + M) ^ L.length * M ^ (W.length + 1) * ‖v‖ :=
          add_le_add (mul_le_mul hc h1 (norm_nonneg _) hR) h2
      _ = _ := by ring

theorem qminor_bd {t : ℕ} {v : V} {M R : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hW : ∀ W : List (Fin n × Fin n), W.length ≤ t → ‖(W.map fun p => E p.1 p.2).prod v‖ ≤ M ^ W.length * ‖v‖)
    (a b : Fin t → Fin n) (u : ℂ) (hu : ∀ k : Fin t, ‖u - (k : ℂ)‖ ≤ R) :
    ‖qminor E a b u v‖ ≤ t.factorial * ((R + M) ^ t * ‖v‖) := by
  unfold qminor
  rw [LinearMap.sum_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ ((R + M) ^ t * ‖v‖) fun σ _ => ?_).trans ?_)
  · have h := prod_bd hR hM hW (List.ofFn fun k : Fin t => (u - (k : ℂ), a (σ k), b k))
      (fun p hp => by obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp; exact hu k) [] (by simp)
    simp only [List.map_ofFn, List.map_nil, List.prod_nil, List.length_ofFn, List.length_nil, pow_zero, mul_one,
      Module.End.one_apply] at h
    rw [Module.End.mul_apply, Module.End.intCast_apply]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e]
    · simpa [Function.comp_def] using h
    · simpa [Function.comp_def] using h
  · simp [Fintype.card_perm]

end Norm

end PositivityTheory.UnitaryDecomposition.Com
