import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeneratorImageIsSymbol

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Hom

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] {n : ℕ}

theorem dv_pol_iff (F : MvPolynomial (ι × Fin n) R) (d : ι → ℕ) :
    F ∈ Pol R n d ↔ IsWeightedHomogeneous (letterWeight (ι := ι) (n := n)) F d := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  constructor
  · intro h m hm
    have h' : ∀ i, multideg m i = d i := h (Finset.mem_coe.2 (mem_support_iff.2 hm))
    rw [weight_eq_multidegree_fun]; funext i; exact h' i
  · intro h m hm
    show ∀ i, multideg m i = d i
    intro i
    have := h (mem_support_iff.1 (Finset.mem_coe.1 hm))
    rw [weight_eq_multidegree_fun] at this
    exact congrFun this i

theorem dv_comp_zero (ψ : MvPolynomial (ι × Fin n) R) (d : ι → ℕ)
    (h : ∀ m ∈ ψ.support, (fun i => multideg m i) ≠ d) : multidegreeComponent d ψ = 0 := by
  unfold multidegreeComponent
  apply Finset.sum_eq_zero
  intro m hm
  have hm' := (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).1 hm
  exact absurd hm'.2 (h m hm'.1)

theorem dv_whc_mul (φ ψ : MvPolynomial (ι × Fin n) R) (e d : ι → ℕ) (hφ : φ ∈ Pol R n e) :
    weightedHomogeneousComponent (letterWeight (ι := ι) (n := n)) (e + d) (φ * ψ) = φ * multidegreeComponent d ψ := by
  have hφ' := (dv_pol_iff φ e).1 hφ
  conv_lhs => rw [eq_sum_multidegree_components ψ, Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single d]
  · exact (hφ'.mul ((dv_pol_iff _ _).1 (homogeneous_component_mem d ψ))).weightedHomogeneousComponent_same
  · intro b _ hb
    refine (hφ'.mul ((dv_pol_iff _ _).1 (homogeneous_component_mem b ψ))).weightedHomogeneousComponent_ne _ ?_
    intro h
    exact hb (add_left_cancel h).symm
  · intro h
    rw [dv_comp_zero ψ d (fun m hm he => h ((@Finset.mem_image _ _ (fun _ _ => Classical.propDecidable _) _ _ _).2 ⟨m, hm, he⟩)), mul_zero, map_zero]

theorem dv_quot_hom [IsDomain R] (φ ψ : MvPolynomial (ι × Fin n) R) (e d : ι → ℕ) (hφ : φ ∈ Pol R n e) (hφ0 : φ ≠ 0)
    (h : φ * ψ ∈ Pol R n d) : ψ ∈ Pol R n (d - e) := by
  have key : ∀ d2 : ι → ℕ, e + d2 ≠ d → multidegreeComponent d2 ψ = 0 := by
    intro d2 hne
    have h1 := dv_whc_mul φ ψ e d2 hφ
    rw [((dv_pol_iff _ _).1 h).weightedHomogeneousComponent_ne _ hne] at h1
    rcases mul_eq_zero.1 h1.symm with h2 | h2
    · exact absurd h2 hφ0
    · exact h2
  rw [eq_sum_multidegree_components ψ]
  apply Submodule.sum_mem
  intro d2 _
  by_cases hd : e + d2 = d
  · have : d - e = d2 := by rw [← hd]; simp
    rw [this]; exact homogeneous_component_mem d2 ψ
  · rw [key d2 hd]; exact Submodule.zero_mem _

theorem dv_pol_mul (φ ψ : MvPolynomial (ι × Fin n) R) (e d : ι → ℕ) (hφ : φ ∈ Pol R n e) (hψ : ψ ∈ Pol R n d) :
    φ * ψ ∈ Pol R n (e + d) :=
  (dv_pol_iff _ _).2 (((dv_pol_iff _ _).1 hφ).mul ((dv_pol_iff _ _).1 hψ))

theorem dv_pol_pow (φ : MvPolynomial (ι × Fin n) R) (e : ι → ℕ) (hφ : φ ∈ Pol R n e) (k : ℕ) :
    φ ^ k ∈ Pol R n (k • e) :=
  (dv_pol_iff _ _).2 (((dv_pol_iff _ _).1 hφ).pow k)

end Hom

section Det

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] {r : ℕ}

def dv_eA (A : Fin r → ι) : ι → ℕ := ∑ l : Fin r, Pi.single (A l) 1

theorem dv_detA_hom (A : Fin r → ι) : letterDeterminant R A ∈ Pol R r (dv_eA A) := by
  rw [dv_pol_iff]
  unfold letterDeterminant
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have h1 : IsWeightedHomogeneous (letterWeight (ι := ι) (n := r))
      (∏ i : Fin r, (Matrix.of fun i j : Fin r => (X (A i, j) : MvPolynomial (ι × Fin r) R)) (σ i) i)
      (∑ i : Fin r, (Pi.single (A (σ i)) 1 : ι → ℕ)) := by
    apply IsWeightedHomogeneous.prod
    intro i _
    exact isWeightedHomogeneous_X R (letterWeight (ι := ι) (n := r)) (A (σ i), i)
  have h2 : (∑ i : Fin r, (Pi.single (A (σ i)) 1 : ι → ℕ)) = dv_eA A := by
    unfold dv_eA
    exact Equiv.sum_comp σ (fun l => (Pi.single (A l) 1 : ι → ℕ))
  rw [h2] at h1
  intro m hm
  apply h1
  intro h0
  apply hm
  rw [coeff_smul, h0, smul_zero]

end Det

section Division

variable {R0 : Type} [CommRing R0] [IsDomain R0] {ι : Type} [Fintype ι] {r : ℕ} [NeZero r]

theorem dv_detA_ne (A : Fin r → ι) (hinj : Function.Injective A) : letterDeterminant R0 A ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval (fun v : ι × Fin r => if A v.2 = v.1 then (1 : R0) else 0)) h
  unfold letterDeterminant at h1
  rw [RingHom.map_det, map_zero] at h1
  have h2 : ((MvPolynomial.eval fun v : ι × Fin r => if A v.2 = v.1 then (1 : R0) else 0).mapMatrix
      (Matrix.of fun i j : Fin r => (X (A i, j) : MvPolynomial (ι × Fin r) R0))) = 1 := by
    ext i j
    simp [Matrix.one_apply, hinj.eq_iff, eq_comm]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem dv_map_pol {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {n : ℕ} (d : ι → ℕ)
    (G : MvPolynomial (ι × Fin n) R) (hG : G ∈ Pol R n d) : MvPolynomial.map f G ∈ Pol R' n d := by
  unfold Pol at *
  rw [mem_restrictSupport_iff] at *
  exact fun m hm => hG (Finset.mem_coe.2 (MvPolynomial.support_map_subset f G (Finset.mem_coe.1 hm)))

theorem dv_div_one (hE : FieldMultidegreeDivisibility) (LL : Letters ι) (S : Set ι) (A : Fin r → ι) (hinj : Function.Injective A)
    (hA : ∀ l, A l ∈ S ∧ LL.vec (A l) = true) (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) R0) (hG : G ∈ Pol R0 r d)
    (n : ℕ) (hval : (((otherVectorDegree LL S A d : ℤ) + (n : ℤ) : ℤ) : WithTop ℤ) ≤ valS LL S G) :
    ∃ Qt : MvPolynomial (ι × Fin r) R0, Qt ∈ Pol R0 r (d - n • dv_eA A) ∧ G = letterDeterminant R0 A ^ n * Qt ∧
      ∀ (S' : Set ι) (t : ℤ), ((t : ℤ) : WithTop ℤ) ≤ valS LL S' G → ((t - (n : ℤ) : ℤ) : WithTop ℤ) ≤ valS LL S' Qt := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨G, by simpa using hG, by simp, fun S' t ht => by simpa using ht⟩
  obtain ⟨hE1, hE2⟩ := hE (FractionRing R0) ι LL r S A hinj hA
  have hGm := dv_map_pol (algebraMap R0 (FractionRing R0)) d G hG
  have hv : (((otherVectorDegree LL S A d : ℤ) + (n : ℤ) : ℤ) : WithTop ℤ) ≤
      valS LL S (MvPolynomial.map (algebraMap R0 (FractionRing R0)) G) := by
    rw [valuation_fraction_field_extension R0 ι LL r S G]; exact hval
  have h1 := hE1 d _ hGm _ hv (by omega)
  have hn' : ((otherVectorDegree LL S A d : ℤ) + (n : ℤ) - (otherVectorDegree LL S A d : ℤ)).toNat = n := by omega
  rw [hn'] at h1
  obtain ⟨Qt, hQt⟩ := gauss_quotient_integral R0 ι r A hinj n G h1
  refine ⟨Qt, dv_quot_hom _ _ _ _ (dv_pol_pow _ _ (dv_detA_hom A) n) (pow_ne_zero _ (dv_detA_ne A hinj)) (hQt ▸ hG),
    hQt, ?_⟩
  intro S' t ht
  have hmap : MvPolynomial.map (algebraMap R0 (FractionRing R0)) G =
      letterDeterminant (FractionRing R0) A ^ n * MvPolynomial.map (algebraMap R0 (FractionRing R0)) Qt := by
    conv_lhs => rw [hQt]
    rw [map_mul, map_pow, map_letter_determinant]
  have h2 := hE2 _ _ _ hmap S'
  rw [valuation_fraction_field_extension R0 ι LL r S' G, valuation_fraction_field_extension R0 ι LL r S' Qt] at h2
  have h3 := le_trans ht h2
  cases h : valS LL S' Qt with
  | top => exact le_top
  | coe z =>
    rw [h] at h3
    norm_cast at h3 ⊢
    omega

theorem dv_degOther_mono (LL : Letters ι) (S : Set ι) (A : Fin r → ι) (d d' : ι → ℕ) (h : ∀ i, d' i ≤ d i) :
    otherVectorDegree LL S A d' ≤ otherVectorDegree LL S A d := by
  unfold otherVectorDegree
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact h i
  · exact le_rfl

theorem dv_div_list (hE : FieldMultidegreeDivisibility) (LL : Letters ι) (tasks : List (Set ι × (Fin r → ι) × ℕ)) :
    (∀ t ∈ tasks, Function.Injective t.2.1 ∧ ∀ l, t.2.1 l ∈ t.1 ∧ LL.vec (t.2.1 l) = true) →
    ∀ (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) R0), G ∈ Pol R0 r d →
    (∀ t ∈ tasks, (((otherVectorDegree LL t.1 t.2.1 d : ℤ) + (((tasks.map fun t => t.2.2).sum : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
      valS LL t.1 G) →
    ∃ (d' : ι → ℕ) (Qt : MvPolynomial (ι × Fin r) R0), Qt ∈ Pol R0 r d' ∧
      G = (tasks.map fun t => letterDeterminant R0 t.2.1 ^ t.2.2).prod * Qt ∧
      ∀ (S' : Set ι) (x : ℤ), ((x : ℤ) : WithTop ℤ) ≤ valS LL S' G →
        ((x - (((tasks.map fun t => t.2.2).sum : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ valS LL S' Qt := by
  induction tasks with
  | nil =>
    intro _ d G hG _
    exact ⟨d, G, hG, by simp, fun S' t ht => by simpa using ht⟩
  | cons t ts ih =>
    intro ht d G hG hv
    have h0 := hv t List.mem_cons_self
    have hsum : (((List.map (fun t : Set ι × (Fin r → ι) × ℕ => t.2.2) (t :: ts)).sum : ℕ) : ℤ) =
        (t.2.2 : ℤ) + (((ts.map fun t => t.2.2).sum : ℕ) : ℤ) := by
      rw [List.map_cons, List.sum_cons]; push_cast; ring
    rw [hsum] at h0
    obtain ⟨Q1, hQ1, hG1, hval1⟩ := dv_div_one hE LL t.1 t.2.1 (ht t List.mem_cons_self).1
      (ht t List.mem_cons_self).2 d G hG t.2.2 (le_trans (WithTop.coe_le_coe.2 (by omega)) h0)
    obtain ⟨d', Qt, hQt, hQ1e, hval2⟩ := ih (fun t' h => ht t' (List.mem_cons_of_mem _ h))
      (d - t.2.2 • dv_eA t.2.1) Q1 hQ1 (fun t' h' => by
        have h1 := hv t' (List.mem_cons_of_mem _ h')
        rw [hsum] at h1
        have h2 := hval1 t'.1 _ h1
        have h3 := dv_degOther_mono LL t'.1 t'.2.1 d (d - t.2.2 • dv_eA t.2.1) (fun i => Nat.sub_le _ _)
        exact le_trans (WithTop.coe_le_coe.2 (by omega)) h2)
    refine ⟨d', Qt, hQt, ?_, fun S' x hx => ?_⟩
    · rw [List.map_cons, List.prod_cons, mul_assoc, ← hQ1e]; exact hG1
    · have h4 := hval2 S' _ (hval1 S' x hx)
      rw [hsum]
      exact le_trans (WithTop.coe_le_coe.2 (by omega)) h4

end Division

section Seg

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r)

theorem dv_eL_lt (j : ℤ) (a b : Fin (Mj F j)) : eL F j a < eL F j b ↔ a < b :=
  ((F.letters j).orderEmbOfFin rfl).lt_iff_lt

theorem dv_eL_inj (j : ℤ) : Function.Injective (eL F j) := ((F.letters j).orderEmbOfFin rfl).injective

theorem dv_eL_mem (j : ℤ) (a : Fin (Mj F j)) : eL F j a ∈ F.letters j := Finset.orderEmbOfFin_mem _ rfl a

theorem dv_eL_surj (j : ℤ) (x : ℤ) (hx : x ∈ F.letters j) : ∃ a, eL F j a = x := by
  have h := Finset.range_orderEmbOfFin (F.letters j) rfl
  have hx' : x ∈ Set.range ((F.letters j).orderEmbOfFin rfl) := by rw [h]; exact Finset.mem_coe.2 hx
  exact hx'

theorem dv_ev_dec (x : ℤ) : (evensBefore F x).Pairwise (fun a b => b < a) := by
  unfold evensBefore
  rw [List.pairwise_reverse]
  exact (Finset.sortedLT_sort _).pairwise

theorem dv_ev_mem (x y : ℤ) :
    y ∈ evensBefore F x ↔ (x - (r : ℤ) * n' ≤ y ∧ y < x) ∧ posOf n' y ∈ F.TT ∧ Even y := by
  unfold evensBefore
  rw [List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico]

variable {F} {L₁ N₁ : ℕ}

theorem dv_len (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (x : ℤ) (l : ℕ) (hl : l < r) :
    l < (evensBefore F x).length := by
  by_contra h
  have h1 := (window_holds_even_tops n' r F L₁ N₁ hV hn hr x l hl).2.2
  unfold Arow at h1
  rw [List.getD_eq_default _ _ (not_lt.1 h)] at h1
  exact lt_irrefl _ h1

theorem dv_Arow_get (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (x : ℤ) (l : ℕ) (hl : l < r) :
    Arow F x l = (evensBefore F x)[l]'(dv_len hV hn hr x l hl) := by
  unfold Arow
  rw [List.getD_eq_getElem _ _ (dv_len hV hn hr x l hl)]

theorem dv_Arow_anti (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (x : ℤ) (l l' : ℕ) (h : l < l') (hl : l' < r) :
    Arow F x l' < Arow F x l := by
  rw [dv_Arow_get hV hn hr x l (by omega), dv_Arow_get hV hn hr x l' hl]
  exact (List.pairwise_iff_getElem.1 (dv_ev_dec F x)) l l' _ _ h

theorem dv_Arow_inj (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (x : ℤ) (l l' : ℕ) (hl : l < r) (hl' : l' < r)
    (h : Arow F x l = Arow F x l') : l = l' := by
  rcases lt_trichotomy l l' with g | g | g
  · have := dv_Arow_anti hV hn hr x l l' g hl'; omega
  · exact g
  · have := dv_Arow_anti hV hn hr x l' l g hl; omega

theorem dv_Arow_newer (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (x : ℤ) (l : ℕ) (hl : l < r) (y : ℤ)
    (hy : posOf n' y ∈ F.TT ∧ Even y) (hyx : y < x) (h : Arow F x l < y) : ∃ l' < l, y = Arow F x l' := by
  have hlow := bk_Arow_low F x l
  have hm : y ∈ evensBefore F x := (dv_ev_mem F x y).2 ⟨⟨by omega, hyx⟩, hy⟩
  obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.1 hm
  have hil : i < l := by
    by_contra hc
    rw [dv_Arow_get hV hn hr x l hl] at h
    rcases Nat.eq_or_lt_of_le (not_lt.1 hc) with e | e
    · subst e; omega
    · have := (List.pairwise_iff_getElem.1 (dv_ev_dec F x)) l i (dv_len hV hn hr x l hl) hi e
      omega
  exact ⟨i, hil, by rw [dv_Arow_get hV hn hr x i (by omega)]; exact hiy.symm⟩

theorem dv_Arow_ge (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (j x : ℤ) (hx : F.fr (j - 1) (r - 1) < x)
    (l : ℕ) (hl : l < r) : F.fr (j - 1) 0 ≤ Arow F x l := by
  by_contra hc
  have hc' : Arow F x l < F.fr (j - 1) 0 := not_le.1 hc
  have hex : ∀ i : Fin r, ∃ l' : Fin l, F.fr (j - 1) i.val = Arow F x l'.val := by
    intro i
    have h1 := frame_row_monotone F L₁ N₁ hV (j - 1) i.val i.2
    have h2 := frame_entry_le_last F L₁ N₁ hV (j - 1) i.val i.2
    obtain ⟨l', hl', he⟩ := dv_Arow_newer hV hn hr x l hl (F.fr (j - 1) i.val) (hV.2.2.2.2.1 (j - 1) i.val i.2)
      (by omega) (by omega)
    exact ⟨⟨l', hl'⟩, he⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : F.fr (j - 1) a.val = F.fr (j - 1) b.val := by rw [hf a, hf b, hab]
    rcases lt_trichotomy a.val b.val with g | g | g
    · have := frame_entries_strictMono F L₁ N₁ hV (j - 1) a.val b.val g b.2; omega
    · exact Fin.ext g
    · have := frame_entries_strictMono F L₁ N₁ hV (j - 1) b.val a.val g a.2; omega
  have := Fintype.card_le_of_injective f hinj
  simp at this
  omega

theorem dv_mem_letters (j y : ℤ) : y ∈ F.letters j ↔ (F.fr (j - 1) 0 ≤ y ∧ y ≤ F.fr j (r - 1)) ∧ posOf n' y ∈ F.TT := by
  unfold Frames.letters
  rw [Finset.mem_filter, Finset.mem_Icc]

theorem dv_mem_nonW (j y : ℤ) : y ∈ nonW F j ↔ y ∈ F.letters j ∧ F.fr (j - 1) (r - 1) < y := by
  unfold nonW
  rw [Finset.mem_filter]
  unfold Frames.IsW
  rw [not_le]

theorem dv_Arow_letter (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (j x : ℤ) (hx : x ∈ nonW F j)
    (l : ℕ) (hl : l < r) : Arow F x l ∈ F.letters j := by
  rw [dv_mem_nonW, dv_mem_letters] at hx
  have h1 := window_holds_even_tops n' r F L₁ N₁ hV hn hr x l hl
  rw [dv_mem_letters]
  exact ⟨⟨dv_Arow_ge hV hn hr j x hx.2 l hl, by omega⟩, h1.2.1⟩

theorem dv_frame_lt (hV : F.Valid L₁ N₁) (j : ℤ) : F.fr (j - 1) (r - 1) < F.fr j 0 := by
  have := hV.2.2.2.1 (j - 1)
  rwa [sub_add_cancel] at this

theorem dv_frame_letter (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (l : ℕ) (hl : l < r) :
    F.fr (j - 1) l ∈ F.letters j := by
  rw [dv_mem_letters]
  have h1 := frame_row_monotone F L₁ N₁ hV (j - 1) l hl
  have h2 := frame_entry_le_last F L₁ N₁ hV (j - 1) l hl
  have h3 := dv_frame_lt hV j
  have h4 := frame_row_monotone F L₁ N₁ hV j (r - 1) (by omega)
  exact ⟨⟨h1, by omega⟩, (hV.2.2.2.2.1 (j - 1) l hl).1⟩

theorem dv_last_nonW (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) : F.fr j (r - 1) ∈ nonW F j := by
  rw [dv_mem_nonW, dv_mem_letters]
  have h1 := frame_row_monotone F L₁ N₁ hV (j - 1) (r - 1) (by omega)
  have h3 := dv_frame_lt hV j
  have h4 := frame_row_monotone F L₁ N₁ hV j (r - 1) (by omega)
  exact ⟨⟨⟨by omega, le_rfl⟩, (hV.2.2.2.2.1 j (r - 1) (by omega)).1⟩, by omega⟩

theorem dv_W_frame (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (j y : ℤ) (hy : y ∈ F.letters j) (hW : y ≤ F.fr (j - 1) (r - 1)) :
    ∃ l < r, y = F.fr (j - 1) l := by
  rw [dv_mem_letters] at hy
  have key : ∀ i, i < r → y ≤ F.fr (j - 1) i → ∃ l < r, y = F.fr (j - 1) l := by
    intro i
    induction i with
    | zero => intro h0 h1; exact ⟨0, h0, by omega⟩
    | succ i ih =>
      intro h0 h1
      by_cases h2 : y ≤ F.fr (j - 1) i
      · exact ih (by omega) h2
      · by_cases h3 : y = F.fr (j - 1) (i + 1)
        · exact ⟨i + 1, h0, h3⟩
        · exact absurd hy.2 (hV.2.2.2.2.2.1 (j - 1) i y h0 (by omega) (by omega))
  exact key (r - 1) (by omega) hW

end Seg

section SegDiv

variable {n' r : ℕ} [NeZero n'] {F : Frames n' r} {L₁ N₁ : ℕ}

theorem dv_nonW_of (j : ℤ) (i : Fin (Mj F j)) (h : ¬ F.IsW j (eL F j i)) : eL F j i ∈ nonW F j := by
  unfold nonW
  exact Finset.mem_filter.2 ⟨dv_eL_mem F j i, h⟩

theorem dv_nonW_image (j : ℤ) :
    nonW F j = (univ.filter fun i : Fin (Mj F j) => ¬ F.IsW j (eL F j i)).image (eL F j) := by
  ext x
  rw [Finset.mem_image]
  constructor
  · intro hx
    have hx' := hx
    unfold nonW at hx'
    rw [Finset.mem_filter] at hx'
    obtain ⟨a, ha⟩ := dv_eL_surj F j x hx'.1
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [ha]; exact hx'.2⟩, ha⟩
  · rintro ⟨a, ha, rfl⟩
    exact dv_nonW_of j a (Finset.mem_filter.1 ha).2

variable {O : Type} [CommRing O] {K : ℕ}

theorem dv_plnm_det (j : ℤ) (A : Fin r → Fin (Mj F j)) :
    plnm F j O K (rename (plVar (K := K)) (letterDeterminant O A)) =
      (Matrix.of fun l b : Fin r => (X (eL F j (A l), Fin.castAdd K b) : SegRing O r K)).det := by
  unfold letterDeterminant
  rw [AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext l b
  simp [plnm, plVar]

theorem dv_degOther_le (j : ℤ) (i : Fin (Mj F j)) (A : Fin r → Fin (Mj F j))
    (hA : ∀ l : Fin r, eL F j (A l) = Arow F (eL F j i) l.val) (d' : Fin (Mj F j) → ℕ) (dd : ℤ → ℕ)
    (hdd : ∀ a, d' a ≤ dd (eL F j a)) :
    otherVectorDegree (LLs F j).toLetters {y | y < i} A d' ≤
      ∑ y ∈ (F.letters j).filter (fun y => Even y ∧ y < eL F j i ∧ ∀ l < r, y ≠ Arow F (eL F j i) l), dd y := by
  unfold otherVectorDegree
  calc _ ≤ ∑ a : Fin (Mj F j), (if a ∈ {y | y < i} ∧ (LLs F j).toLetters.vec a = true ∧ a ∉ Set.range A
        then dd (eL F j a) else 0) := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs
        · exact hdd a
        · exact le_rfl
    _ = ∑ a ∈ univ.filter (fun a : Fin (Mj F j) => a ∈ {y | y < i} ∧ (LLs F j).toLetters.vec a = true ∧
          a ∉ Set.range A), dd (eL F j a) := by rw [Finset.sum_filter]
    _ = ∑ y ∈ (univ.filter (fun a : Fin (Mj F j) => a ∈ {y | y < i} ∧ (LLs F j).toLetters.vec a = true ∧
          a ∉ Set.range A)).image (eL F j), dd y := by
        rw [Finset.sum_image (fun a _ b _ h => dv_eL_inj F j h)]
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset
        intro y hy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
        obtain ⟨_, h1, h2, h3⟩ := Finset.mem_filter.1 ha
        refine Finset.mem_filter.2 ⟨dv_eL_mem F j a, ?_, (dv_eL_lt F j a i).2 h1, ?_⟩
        · exact of_decide_eq_true h2
        · intro l hl he
          apply h3
          exact ⟨⟨l, hl⟩, dv_eL_inj F j (by rw [hA ⟨l, hl⟩]; exact he.symm)⟩

variable [IsDomain O] [NeZero r] [NeZero K]

theorem dv_segment (hE : FieldMultidegreeDivisibility) (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (j : ℤ) (m1 m2 ms : ℕ)
    (hms : (F.letters j).card * m1 + m2 ≤ ms) (dd : ℤ → ℕ)
    (d' d'' : Fin (Mj F j) → ℕ) (A : MvPolynomial (Fin (Mj F j) × Fin r) O)
    (G : MvPolynomial (Fin (Mj F j) × Fin K) O) (Mx : Fin (Mj F j) → ℤ)
    (hA : A ∈ Pol O r d') (hG : G ∈ Pol O K d'') (hW : ∀ i, F.IsW j (eL F j i) → d'' i = 0)
    (hC : CondM F j (ms : ℤ) A G Mx) (hdd : ∀ a, d' a ≤ dd (eL F j a))
    (hval : ∀ i, ¬ F.IsW j (eL F j i) →
      ((((∑ y ∈ (F.letters j).filter (fun y => Even y ∧ y < eL F j i ∧ ∀ l < r, y ≠ Arow F (eL F j i) l), dd y : ℕ) : ℤ)
        + (ms : ℤ) : ℤ) : WithTop ℤ) ≤ valS (LLs F j).toLetters {y | y < i} A) :
    ∃ P' ∈ MGen0 F j O K,
      plnm F j O K (rename (plVar (K := K)) A * rename (tanVar (r := r)) G) = Dv F j O K m1 m2 * P' := by
  have hAex : ∀ (i : Fin (Mj F j)) (l : Fin r), ∃ a : Fin (Mj F j),
      ¬ F.IsW j (eL F j i) → eL F j a = Arow F (eL F j i) l.val := by
    intro i l
    by_cases h : F.IsW j (eL F j i)
    · exact ⟨i, fun h' => absurd h h'⟩
    · obtain ⟨a, ha⟩ := dv_eL_surj F j _ (dv_Arow_letter hV hn hr j (eL F j i) (dv_nonW_of j i h) l.val l.2)
      exact ⟨a, fun _ => ha⟩
  choose Ai hAi using hAex
  have hWex : ∀ l : Fin r, ∃ a, eL F j a = F.fr (j - 1) l.val :=
    fun l => dv_eL_surj F j _ (dv_frame_letter hV hr j l.val l.2)
  choose Aw hAw using hWex
  have hne : (nonW F j).Nonempty := ⟨_, dv_last_nonW hV hr j⟩
  have hx0 := (dv_mem_nonW j _).1 (Finset.min'_mem _ hne)
  obtain ⟨i0, hi0⟩ := dv_eL_surj F j ((nonW F j).min' hne) hx0.1
  have hi0W : ¬ F.IsW j (eL F j i0) := by
    rw [hi0]; unfold Frames.IsW; exact not_le.2 hx0.2
  set I := univ.filter fun i : Fin (Mj F j) => ¬ F.IsW j (eL F j i) with hI
  set tasks : List (Set (Fin (Mj F j)) × (Fin r → Fin (Mj F j)) × ℕ) :=
    (I.toList.map fun i => (({y | y < i} : Set (Fin (Mj F j))), Ai i, m1)) ++ [({y | y < i0}, Aw, m2)] with htasks
  have hsum : (tasks.map fun t => t.2.2).sum = I.card * m1 + m2 := by
    rw [htasks, List.map_append, List.sum_append, List.map_map]
    simp [Function.comp_def]
  have hIc : I.card ≤ (F.letters j).card := by
    have := Finset.card_le_univ I
    simpa using this
  have htot : (tasks.map fun t => t.2.2).sum ≤ ms := by
    rw [hsum]
    have := Nat.mul_le_mul_right m1 hIc
    omega
  have hprod : (tasks.map fun t => letterDeterminant O t.2.1 ^ t.2.2).prod =
      (∏ i ∈ I, letterDeterminant O (Ai i) ^ m1) * letterDeterminant O Aw ^ m2 := by
    rw [htasks, List.map_append, List.prod_append, List.map_map, ← Finset.prod_map_toList]
    simp [Function.comp_def]
  have hvalid : ∀ t ∈ tasks, Function.Injective t.2.1 ∧
      ∀ l, t.2.1 l ∈ t.1 ∧ (LLs F j).toLetters.vec (t.2.1 l) = true := by
    intro t ht
    rw [htasks, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ht
      have hiW : ¬ F.IsW j (eL F j i) := (Finset.mem_filter.1 (Finset.mem_toList.1 hi)).2
      refine ⟨?_, fun l => ⟨?_, ?_⟩⟩
      · intro l l' hll
        have h1 : Arow F (eL F j i) l.val = Arow F (eL F j i) l'.val := by
          rw [← hAi i l hiW, ← hAi i l' hiW]; exact congrArg _ hll
        exact Fin.ext (dv_Arow_inj hV hn hr _ _ _ l.2 l'.2 h1)
      · show Ai i l < i
        rw [← dv_eL_lt F j, hAi i l hiW]
        exact (window_holds_even_tops n' r F L₁ N₁ hV hn hr _ l.val l.2).2.2
      · show decide (Even (eL F j (Ai i l))) = true
        rw [hAi i l hiW]
        exact decide_eq_true (window_holds_even_tops n' r F L₁ N₁ hV hn hr _ l.val l.2).1
    · rw [List.mem_singleton] at ht
      subst ht
      refine ⟨?_, fun l => ⟨?_, ?_⟩⟩
      · intro l l' hll
        have h1 : F.fr (j - 1) l.val = F.fr (j - 1) l'.val := by
          rw [← hAw l, ← hAw l']; exact congrArg _ hll
        rcases lt_trichotomy l.val l'.val with g | g | g
        · have := frame_entries_strictMono F L₁ N₁ hV (j - 1) l.val l'.val g l'.2; omega
        · exact Fin.ext g
        · have := frame_entries_strictMono F L₁ N₁ hV (j - 1) l'.val l.val g l.2; omega
      · show Aw l < i0
        rw [← dv_eL_lt F j, hAw l, hi0]
        have := frame_entry_le_last F L₁ N₁ hV (j - 1) l.val l.2
        omega
      · show decide (Even (eL F j (Aw l))) = true
        rw [hAw l]
        exact decide_eq_true (hV.2.2.2.2.1 (j - 1) l.val l.2).2
  have hvals : ∀ t ∈ tasks, (((otherVectorDegree (LLs F j).toLetters t.1 t.2.1 d' : ℤ) +
      (((tasks.map fun t => t.2.2).sum : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ valS (LLs F j).toLetters t.1 A := by
    intro t ht
    rw [htasks, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ht
      have hiW : ¬ F.IsW j (eL F j i) := (Finset.mem_filter.1 (Finset.mem_toList.1 hi)).2
      have h1 := dv_degOther_le j i (Ai i) (fun l => hAi i l hiW) d' dd hdd
      refine le_trans (WithTop.coe_le_coe.2 ?_) (hval i hiW)
      show (otherVectorDegree (LLs F j).toLetters {y | y < i} (Ai i) d' : ℤ) + _ ≤ _
      omega
    · rw [List.mem_singleton] at ht
      subst ht
      have h0 : otherVectorDegree (LLs F j).toLetters {y | y < i0} Aw d' = 0 := by
        unfold otherVectorDegree
        apply Finset.sum_eq_zero
        intro a _
        rw [if_neg]
        rintro ⟨h1, _, h3⟩
        apply h3
        have h4 : eL F j a < (nonW F j).min' hne := by rw [← hi0]; exact (dv_eL_lt F j a i0).2 h1
        have h5 : eL F j a ≤ F.fr (j - 1) (r - 1) := by
          by_contra hc
          have h6 : eL F j a ∈ nonW F j := (dv_mem_nonW j _).2 ⟨dv_eL_mem F j a, not_le.1 hc⟩
          have := Finset.min'_le _ _ h6
          omega
        obtain ⟨l, hl, he⟩ := dv_W_frame hV hr j _ (dv_eL_mem F j a) h5
        exact ⟨⟨l, hl⟩, dv_eL_inj F j (by rw [hAw ⟨l, hl⟩]; exact he.symm)⟩
      refine le_trans (WithTop.coe_le_coe.2 ?_) (hval i0 hi0W)
      show (otherVectorDegree (LLs F j).toLetters {y | y < i0} Aw d' : ℤ) + _ ≤ _
      rw [h0]
      have : (0 : ℤ) ≤ ((∑ y ∈ (F.letters j).filter
        (fun y => Even y ∧ y < eL F j i0 ∧ ∀ l < r, y ≠ Arow F (eL F j i0) l), dd y : ℕ) : ℤ) := Int.natCast_nonneg _
      omega
  obtain ⟨d1, A', hA', hAe, hval2⟩ := dv_div_list hE (LLs F j).toLetters tasks hvalid d' A hA hvals
  have hC' : CondM F j 0 A' G Mx := by
    intro i hiW
    obtain ⟨h1, h2⟩ := hC i hiW
    refine ⟨fun he => ⟨(h1 he).1, ?_⟩, fun he => ⟨(h2 he).1, ?_⟩⟩
    · exact le_trans (WithTop.coe_le_coe.2 (by omega)) (hval2 _ _ (h1 he).2)
    · exact le_trans (WithTop.coe_le_coe.2 (by omega)) (hval2 _ _ (h2 he).2)
  refine ⟨plnm F j O K (rename (plVar (K := K)) A' * rename (tanVar (r := r)) G),
    ⟨d1, d'', A', G, Mx, hA', hG, hW, hC', rfl⟩, ?_⟩
  have hDv : plnm F j O K (rename (plVar (K := K)) ((∏ i ∈ I, letterDeterminant O (Ai i) ^ m1) * letterDeterminant O Aw ^ m2)) =
      Dv F j O K m1 m2 := by
    unfold Dv
    rw [map_mul, map_mul, map_prod, map_prod, map_pow, map_pow, dv_plnm_det, dv_nonW_image,
      Finset.prod_image (fun a _ b _ h => dv_eL_inj F j h)]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      have hiW : ¬ F.IsW j (eL F j i) := (Finset.mem_filter.1 hi).2
      rw [map_pow, map_pow, dv_plnm_det]
      unfold Dseg
      simp only [hAi i _ hiW]
    · unfold Wseg
      simp only [hAw]
  conv_lhs => rw [hAe, hprod]
  rw [map_mul (rename (plVar (K := K))), mul_assoc, map_mul (plnm F j O K), hDv]

end SegDiv

theorem restDivM (hE : FieldMultidegreeDivisibility) : ∃ C : ℝ, 1 ≤ C ∧ (RestGeom → RestDivM C (C + 1) C) := by
  obtain ⟨C, hC, H⟩ := numeric_symbol_bound_real
  refine ⟨C, hC, fun hGeom => ?_⟩
  intro p n' r K _ _ _ _ O _ _ _ _ X deg a Y c0 c'' cStar Dd hII j dd hdd P hP
  obtain ⟨d', d'', A, G, Mx, hA, hG, hsum, hW, hCM, hth, rfl⟩ := hP
  have hp := X.hH.1
  have hr := X.hH.2.1
  have hn := X.hH.2.2.2.2
  have hdeg : ∀ s ∈ X.Fr.TT, (a : ℝ) ≤ deg s ∧ (deg s : ℝ) ≤ 2 * a := by
    have hII' := hII
    unfold Formalism.MainNotions.SourceCleaning.HypII at hII'
    obtain ⟨_, _, g3, _⟩ := hII'
    intro s hs
    obtain ⟨h1, h2⟩ := g3 s hs
    have h0 : (0 : ℝ) ≤ (c'' : ℝ) := Nat.cast_nonneg _
    exact ⟨by linarith, by linarith⟩
  have hms : (X.Fr.letters j).card * X.m1 (cPrime n' r X.Fr.TT.card c0 c'' cStar) +
      X.m2 (cPrime n' r X.Fr.TT.card c0 c'' cStar) ≤
      mStar p X.Fr (r + K) X.N₁ (p ^ X.G') (cPrime n' r X.Fr.TT.card c0 c'' cStar) := by
    unfold Ctx.m1 Ctx.m2 Ctx.Q
    exact segment_divisions_le_bound p X.Fr (r + K) X.L₁ X.N₁ (p ^ X.G') _ X.hV j
  refine dv_segment hE X.hV hn (by omega) j _ _ _ hms dd d' d'' A G Mx hA hG hW hCM
    (fun b => by have := hsum b; omega) ?_
  intro i hiW
  cases hv : valS (LLs X.Fr j).toLetters {y | y < i} A with
  | top => exact le_top
  | coe z =>
    have h1 := hth i hiW z hv
    have hB := hGeom p n' r X.Fr X.L₁ X.N₁ hp hr hn X.hV deg a hdeg j dd hdd _ (dv_nonW_of j i hiW)
    obtain ⟨_, h2⟩ := H n' r p X.Fr (r + K) X.L₁ X.N₁ X.G' deg a Y c0 c'' cStar Dd hp hr X.hV hII X.hT j _
      (dv_eL_mem X.Fr j i) hiW
    obtain ⟨h3, _⟩ := h2 _ (z : ℝ) hB h1
    have h0 := level_degree_nonneg p X.Fr deg j (eL X.Fr j i)
    have h4 : ((∑ y ∈ (X.Fr.letters j).filter
        (fun y => Even y ∧ y < eL X.Fr j i ∧ ∀ l < r, y ≠ Arow X.Fr (eL X.Fr j i) l), dd y : ℕ) : ℝ) +
        (mStar p X.Fr (r + K) X.N₁ (p ^ X.G') (cPrime n' r X.Fr.TT.card c0 c'' cStar) : ℝ) ≤ (z : ℝ) := by
      linarith
    exact WithTop.coe_le_coe.2 (by exact_mod_cast h4)

end Formalism.MainNotions.G.symbolGeneratorData
