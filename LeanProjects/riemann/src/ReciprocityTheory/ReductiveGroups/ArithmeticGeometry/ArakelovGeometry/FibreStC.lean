import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStB

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def psumQ (δ k : ℕ) : MvPolynomial (Fin δ) ℤ :=
  (esymmAlgHom_fin_surjective ℤ (le_refl δ)
    ⟨psum (Fin δ) ℤ k, psum_isSymmetric _ _ _⟩).choose

theorem aeval_psumQ (δ k : ℕ) :
    aeval (fun i : Fin δ => esymm (Fin δ) ℤ (i + 1)) (psumQ δ k) = psum (Fin δ) ℤ k := by
  have h := (esymmAlgHom_fin_surjective ℤ (le_refl δ)
    ⟨psum (Fin δ) ℤ k, psum_isSymmetric _ _ _⟩).choose_spec
  have h2 := congrArg Subtype.val h
  first
  | (rw [esymmAlgHom_apply] at h2; exact h2)
  | exact h2
  | simpa [psumQ, esymmAlgHom_apply] using h2

theorem sum_pow_eq_aeval_psumQ {S : Type*} [CommRing S] {δ : ℕ} (f : Fin δ → S) (k : ℕ) :
    ∑ i, f i ^ k =
      aeval (fun i : Fin δ => (Finset.univ.val.map f).esymm (i + 1)) (psumQ δ k) := by
  have h := congrArg (aeval f) (aeval_psumQ δ k)
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h
  simp only [MvPolynomial.aeval_esymm_eq_multiset_esymm] at h
  rw [h]
  simp [MvPolynomial.psum]

theorem multiset_sum_pow_eq {S : Type*} [CommRing S] (s : Multiset S) {n : ℕ}
    (hn : Multiset.card s = n) (k : ℕ) :
    (s.map (· ^ k)).sum = aeval (fun i : Fin n => s.esymm (i + 1)) (psumQ n k) := by
  obtain ⟨l, rfl⟩ : ∃ l : List S, (l : Multiset S) = s := ⟨_, (Quotient.exists_rep s).choose_spec⟩
  rw [Multiset.coe_card] at hn
  subst hn
  have hs : (Finset.univ.val.map l.get : Multiset S) = (l : Multiset S) := by
    first
    | rw [Fin.univ_val_map, List.ofFn_get]
    | simp [Fin.univ_val_map, List.ofFn_get]
  have key := sum_pow_eq_aeval_psumQ l.get k
  rw [hs] at key
  rw [← key, Finset.sum_eq_multiset_sum, ← hs, Multiset.map_map] <;> rfl

def psumC {R : Type*} [CommRing R] (p : Polynomial R) (n k : ℕ) : R :=
  aeval (fun i : Fin n => (-1) ^ (i.val + 1) * p.coeff (n - (i.val + 1))) (psumQ n k)

theorem map_psumC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : Polynomial R)
    (n k : ℕ) : φ (psumC p n k) = psumC (p.map φ) n k := by
  unfold psumC
  induction psumQ n k using MvPolynomial.induction_on
  next a => simp
  next P1 P2 h1 h2 => simp only [map_add, h1, h2]
  next P1 i h1 => simp [h1, Polynomial.coeff_map]

theorem sum_roots_pow {K : Type*} [Field K] (p : Polynomial K) (hm : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) (k : ℕ) :
    (p.roots.map (· ^ k)).sum = psumC p p.natDegree k := by
  rw [multiset_sum_pow_eq p.roots hroots k, psumC]
  refine congrArg (fun F => aeval F (psumQ _ k)) (funext fun i => ?_)
  have hi : (i : ℕ) + 1 ≤ p.natDegree := i.isLt
  rw [Polynomial.coeff_eq_esymm_roots_of_card hroots (Nat.sub_le _ _), hm.leadingCoeff,
    Nat.sub_sub_self hi, one_mul, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}

def Gen.S (G : Gen x e) (j : ℕ) : MvPolynomial (Fin (D + 1)) ℤ :=
  psumC G.P G.P.natDegree j

def Gen.TrP (G : Gen x e) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)) :
    MvPolynomial (Fin (D + 1)) ℤ :=
  ∑ j ∈ Finset.range (H.natDegree + 1), H.coeff j * G.S j

variable [DecidableEq ι] (G : Gen x e)

theorem Gen.deh_S {w : Fin (D + 1) → ℂ} (j : ℕ) :
    deh w 0 (G.S j) = ((G.P.map (deh w 0)).roots.map (· ^ j)).sum := by
  have hm : (G.P.map (deh w 0)).Monic := G.monic.map _
  have hd : (G.P.map (deh w 0)).natDegree = G.P.natDegree := G.monic.natDegree_map _
  have hc : Multiset.card (G.P.map (deh w 0)).roots = (G.P.map (deh w 0)).natDegree := by
    first
    | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
    | exact (IsAlgClosed.splits _).card_roots
    | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  rw [sum_roots_pow _ hm hc j, hd, Gen.S, map_psumC]

private theorem eval₂_deh_eq_zero_of_mem_roots {w : Fin (D + 1) → ℂ} (hw : G.Good w)
    (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ))
    (hH : H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0) {ρ : ℂ}
    (hρ : ρ ∈ (G.P.map (deh w 0)).roots) : H.eval₂ (deh w 0) ρ = 0 := by
  have hP1 : G.P ≠ 1 := by
    intro h1
    have h2 := G.root
    rw [h1, Polynomial.eval₂_one] at h2
    exact one_ne_zero h2
  have hdecomp : H %ₘ G.P + G.P * (H /ₘ G.P) = H := by
    first
    | exact Polynomial.modByMonic_add_div H G.monic
    | exact Polynomial.modByMonic_add_div H G.P
    | exact Polynomial.modByMonic_add_div H G.P G.monic
  have hr : (H %ₘ G.P).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
    have h1 := congrArg (Polynomial.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) hdecomp
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, G.root, zero_mul, add_zero, hH] at h1
    exact h1
  have hcoef := G.min (H %ₘ G.P) (Polynomial.natDegree_modByMonic_lt H G.monic hP1) hr
  have hrw : (H %ₘ G.P).map (deh w 0) = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact hw.ker _ (hcoef j)
  have hPρ : G.P.eval₂ (deh w 0) ρ = 0 := by
    have h3 := (Polynomial.mem_roots (G.monic.map _).ne_zero).mp hρ
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at h3
  have h2 := congrArg (Polynomial.eval₂ (deh w 0) ρ) hdecomp
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, hPρ, zero_mul, add_zero] at h2
  rw [← h2, ← Polynomial.eval_map, hrw, Polynomial.eval_zero]

private theorem deh_dd_mul_deh_zOf_X_eq_eval₂_Q {w : Fin (D + 1) → ℂ} (hw : G.Good w) (i : ι) {ρ : ℂ}
    (hρ : ρ ∈ (G.P.map (deh w 0)).roots) :
    deh w 0 G.dd * deh (G.zOf w ρ) (e 0) (X i) = (G.Q i).eval₂ (deh w 0) ρ := by
  have hx : ∀ j, deh x (e 0) (X j) = x j / x (e 0) := fun j => by simp [deh]
  have hz : ∀ j, deh (G.zOf w ρ) (e 0) (X j) = G.zOf w ρ j / G.zOf w ρ (e 0) :=
    fun j => by simp [deh]
  have hzj : ∀ j, G.zOf w ρ j = w 0 * ((G.Q j).eval₂ (deh w 0) ρ / deh w 0 G.dd) := fun j => rfl
  have hd := hw.dd
  have h0 := hw.w0
  rw [hz, hzj, hzj]
  by_cases hxe : x (e 0) = 0
  · have hq : ∀ j, (G.Q j).eval₂ (deh w 0) ρ = 0 := by
      intro j
      refine eval₂_deh_eq_zero_of_mem_roots G hw (G.Q j) ?_ hρ
      rw [← G.hQ j, hx, hxe, div_zero, mul_zero]
    simp [hq]
  · have hxs : (G.Q (e 0) - Polynomial.C G.dd).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, ← G.hQ (e 0), hx, div_self hxe, mul_one,
        sub_self]
    have h1 := eval₂_deh_eq_zero_of_mem_roots G hw _ hxs hρ
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, sub_eq_zero] at h1
    rw [h1]
    field_simp
    first | done | ring

private theorem exists_pow_mul_eq_eval₂_theta {w : Fin (D + 1) → ℂ} (hw : G.Good w) (f : MvPolynomial ι ℤ) :
    ∃ (N : ℕ) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)),
      deh (x ∘ e) 0 G.dd ^ N * deh x (e 0) f = H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) ∧
      ∀ ρ ∈ (G.P.map (deh w 0)).roots,
        deh w 0 G.dd ^ N * deh (G.zOf w ρ) (e 0) f = H.eval₂ (deh w 0) ρ := by
  induction f using MvPolynomial.induction_on
  next a =>
    refine ⟨0, Polynomial.C (MvPolynomial.C a), ?_, fun ρ _ => ?_⟩ <;>
      (rw [pow_zero, one_mul, Polynomial.eval₂_C]; simp [deh])
  next f1 f2 h1 h2 =>
    obtain ⟨N1, H1, hx1, hw1⟩ := h1
    obtain ⟨N2, H2, hx2, hw2⟩ := h2
    refine ⟨N1 + N2, Polynomial.C (G.dd ^ N2) * H1 + Polynomial.C (G.dd ^ N1) * H2, ?_,
      fun ρ hρ => ?_⟩
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hx1, ← hx2, map_add, map_pow, map_pow]
      ring
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hw1 ρ hρ, ← hw2 ρ hρ, map_add, map_pow, map_pow]
      ring
  next f1 i h1 =>
    obtain ⟨N, H, hx1, hw1⟩ := h1
    refine ⟨N + 1, H * G.Q i, ?_, fun ρ hρ => ?_⟩
    · rw [Polynomial.eval₂_mul, ← hx1, ← G.hQ i, map_mul]
      ring
    · rw [Polynomial.eval₂_mul, ← hw1 ρ hρ, ← deh_dd_mul_deh_zOf_X_eq_eval₂_Q G hw i hρ, map_mul]
      ring

theorem Gen.trace_w {w : Fin (D + 1) → ℂ} (hw : G.Good w) (Tr : Ω → Ω)
    (hTr : ∀ H, Tr (H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) = deh (x ∘ e) 0 (G.TrP H))
    (hsc : ∀ (m : MvPolynomial (Fin (D + 1)) ℤ) (F : MvPolynomial ι ℤ),
      Tr (deh (x ∘ e) 0 m * deh x (e 0) F) = deh (x ∘ e) 0 m * Tr (deh x (e 0) F))
    {f : MvPolynomial ι ℤ} {g : MvPolynomial (Fin (D + 1)) ℤ}
    (h : deh (x ∘ e) 0 g = Tr (deh x (e 0) f)) :
    deh w 0 g = ((G.P.map (deh w 0)).roots.map fun ρ => deh (G.zOf w ρ) (e 0) f).sum := by
  obtain ⟨N, H, hx, hwr⟩ := exists_pow_mul_eq_eval₂_theta G hw f
  have hker : deh (x ∘ e) 0 (G.dd ^ N * g - G.TrP H) = 0 := by
    rw [map_sub, map_mul, h, ← hTr H, ← hx, ← hsc, map_pow, sub_self]
  have hwk := hw.ker _ hker
  rw [map_sub, map_mul, map_pow, sub_eq_zero] at hwk
  have hTrw : deh w 0 (G.TrP H) =
      ((G.P.map (deh w 0)).roots.map fun ρ => H.eval₂ (deh w 0) ρ).sum := by
    rw [Gen.TrP, map_sum]
    simp only [map_mul, G.deh_S, Polynomial.eval₂_eq_sum_range]
    generalize (G.P.map (deh w 0)).roots = s
    refine Multiset.induction_on s ?_ ?_
    · simp
    · intro a s ih
      simp [Multiset.map_cons, Multiset.sum_cons, mul_add, Finset.sum_add_distrib, ih]
  have hdN : deh w 0 G.dd ^ N ≠ 0 := pow_ne_zero _ hw.dd
  apply mul_left_cancel₀ hdN
  rw [hwk, hTrw, ← Multiset.sum_map_mul_left]
  congr 1
  exact Multiset.map_congr rfl fun ρ hρ => (hwr ρ hρ).symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open Polynomial IntermediateField

private lemma exists_int_primitive_element_pair {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero E] [Finite (IntermediateField F E)] (α β : E) :
    ∃ n : ℤ, α ∈ F⟮α + (n : E) * β⟯ ∧ β ∈ F⟮α + (n : E) * β⟯ := by
  obtain ⟨a, b, hab, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℤ => F⟮α + (n : E) * β⟯)
  have ha : α + (a : E) * β ∈ F⟮α + (b : E) * β⟯ := by
    rw [← heq]; exact IntermediateField.mem_adjoin_simple_self F _
  have hb : α + (b : E) * β ∈ F⟮α + (b : E) * β⟯ := IntermediateField.mem_adjoin_simple_self F _
  have hne : (a : E) - b ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hab
  have hβ : β ∈ F⟮α + (b : E) * β⟯ := by
    have hsub := sub_mem ha hb
    have h1 : (α + (a : E) * β) - (α + (b : E) * β) = ((a : E) - b) * β := by ring
    rw [h1] at hsub
    have hc : (a : E) - b ∈ F⟮α + (b : E) * β⟯ := sub_mem (intCast_mem _ a) (intCast_mem _ b)
    have := mul_mem (inv_mem hc) hsub
    rwa [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at this
  refine ⟨b, ?_, hβ⟩
  have := sub_mem hb (mul_mem (intCast_mem _ b) hβ)
  simpa using this

theorem exists_int_primitive {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero F]
    [CharZero E] [FiniteDimensional F E] {ι : Type*} [Fintype ι] (v : ι → E)
    (hv : adjoin F (Set.range v) = ⊤) : ∃ c : ι → ℤ, F⟮∑ i, (c i : E) * v i⟯ = ⊤ := by
  classical
  haveI hfinite : Finite (IntermediateField F E) := by
    first
    | exact inferInstance
    | exact Field.finite_intermediateField_of_exists_primitive_element F E
        (Field.exists_primitive_element F E)
    | exact Field.finite_intermediateField_of_exists_primitive_element
        (Field.exists_primitive_element F E)
    | exact (Field.exists_primitive_element_iff_finite_intermediateField F E).mp
        ⟨inferInstance, Field.exists_primitive_element F E⟩
    | exact Field.exists_primitive_element_iff_finite_intermediateField.mp
        ⟨inferInstance, Field.exists_primitive_element F E⟩
  have key : ∀ s : Finset ι, ∃ c : ι → ℤ, ∀ i ∈ s, v i ∈ F⟮∑ j, (c j : E) * v j⟯ := by
    intro s
    refine Finset.induction_on s ⟨0, by simp⟩ ?_
    intro j s _ ih
    obtain ⟨c, hc⟩ := ih
    obtain ⟨n, hα, hβ⟩ := exists_int_primitive_element_pair (F := F) (∑ i, (c i : E) * v i) (v j)
    refine ⟨c + Pi.single j n, ?_⟩
    have h2 : ∑ i, (((Pi.single j n : ι → ℤ) i : ℤ) : E) * v i = (n : E) * v j := by
      rw [Fintype.sum_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
      simp
    have hsum : ∑ i, (((c + Pi.single j n : ι → ℤ) i : ℤ) : E) * v i =
        ∑ i, (c i : E) * v i + (n : E) * v j := by
      simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, h2]
    rw [hsum]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hβ
    · exact (IntermediateField.adjoin_simple_le_iff.mpr hα) (hc i hi)
  obtain ⟨c, hc⟩ := key Finset.univ
  refine ⟨c, top_le_iff.mp ?_⟩
  rw [← hv, IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact hc i (Finset.mem_univ i)

theorem trace_pow_eq_psumC {K E : Type*} [Field K] [Field E] [Algebra K E] [CharZero K]
    [FiniteDimensional K E] {θ : E} (hθ : K⟮θ⟯ = ⊤) (j : ℕ) :
    Algebra.trace K E (θ ^ j) = psumC (minpoly K θ) (minpoly K θ).natDegree j := by
  classical
  have hint : IsIntegral K θ := IsIntegral.of_finite K θ
  have hmon := minpoly.monic hint
  have hsep : (minpoly K θ).Separable := Algebra.IsSeparable.isSeparable K θ
  have hc : Multiset.card ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots =
      ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).natDegree := by
    first
    | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
    | exact (IsAlgClosed.splits _).card_roots
    | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  have hnd : ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.Nodup :=
    Polynomial.nodup_roots hsep.map
  have hadj : Algebra.adjoin K {θ} = ⊤ := by
    first
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint, hθ,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
          (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hint.isAlgebraic), hθ,
        IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) := by
    intro σ τ h
    exact AlgHom.ext_of_adjoin_eq_top hadj (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h)
  have hfin : Module.finrank K E = (minpoly K θ).natDegree := by
    rw [← IntermediateField.finrank_top', ← hθ, IntermediateField.adjoin.finrank hint]
  have himg : Finset.univ.image (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) =
      ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmon.map _).ne_zero]
      first
      | rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
          Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
      | simp [Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply]
    · rw [Multiset.toFinset_card_of_nodup hnd, hc, hmon.natDegree_map,
        Finset.card_image_of_injective _ hinj, Finset.card_univ, ← hfin]
      exact (AlgHom.card K E (AlgebraicClosure K)).ge
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [map_psumC, ← hmon.natDegree_map (algebraMap K (AlgebraicClosure K)),
    ← sum_roots_pow _ (hmon.map _) hc j]
  first
  | rw [trace_eq_sum_embeddings (AlgebraicClosure K)]
  | rw [trace_eq_sum_embeddings]
  | rw [Algebra.trace_eq_sum_embeddings (AlgebraicClosure K)]
  simp only [map_pow]
  have hsum := Finset.sum_image (s := Finset.univ)
    (g := fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) (f := fun y => y ^ j)
    (fun σ _ τ _ h => hinj h)
  rw [himg] at hsum
  rw [← hsum, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

theorem exists_clear {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {ι : Type*} [Fintype ι] (q : ι → K[X]) :
    ∃ (b : A) (Q : ι → A[X]), b ≠ 0 ∧
      ∀ i, (Q i).map (algebraMap A K) = C (algebraMap A K b) * q i := by
  classical
  choose b hb using fun i =>
    IsLocalization.integerNormalization_map_to_map (M := nonZeroDivisors A) (q i)
  refine ⟨∏ i, (b i : A), fun i => C (∏ j ∈ Finset.univ.erase i, (b j : A)) *
    IsLocalization.integerNormalization (nonZeroDivisors A) (q i), ?_, fun i => ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => nonZeroDivisors.coe_ne_zero (b i)
  · rw [Polynomial.map_mul, hb i, Polynomial.map_C, ← algebraMap_smul K (b i : A) (q i),
      Polynomial.smul_eq_C_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp only [map_mul, Polynomial.C_mul, mul_assoc]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
