import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace GenericLinearTrdeg

theorem coeff_X_pow_mul_linear_pow {R : Type*} [CommRing R] (e c : R) (a b D : ℕ) (h : a + b ≤ D) :
    (Polynomial.X ^ a * (Polynomial.C e * Polynomial.X + Polynomial.C c) ^ b).coeff D =
      if a + b = D then e ^ b else 0 := by
  have hlin : (Polynomial.C e * Polynomial.X + Polynomial.C c).natDegree ≤ 1 :=
    Polynomial.natDegree_linear_le
  split_ifs with hD
  · subst hD
    rw [Polynomial.coeff_X_pow_mul', if_pos (by omega), show a + b - a = b * 1 by omega,
      Polynomial.coeff_pow_of_natDegree_le hlin]
    simp
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc _ ≤ a + b * 1 := by
          refine (Polynomial.natDegree_mul_le).trans (add_le_add ?_ ?_)
          · exact Polynomial.natDegree_X_pow_le a
          · exact Polynomial.natDegree_pow_le_of_le b hlin
      _ < D := by omega

theorem algebraicIndependent_pair_linear {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] {η r x : A} (hη : Transcendental R η)
    (hx : Transcendental (Algebra.adjoin R ({η, r} : Set A)) x) :
    AlgebraicIndependent R ![x, x * η + r] := by
  classical
  set B' := Algebra.adjoin R ({η, r} : Set A)
  let η' : B' := ⟨η, Algebra.subset_adjoin (by simp)⟩
  let r' : B' := ⟨r, Algebra.subset_adjoin (by simp)⟩
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hp0
  set D := p.totalDegree
  let f : Fin 2 → Polynomial B' := ![Polynomial.X, Polynomial.C η' * Polynomial.X + Polynomial.C r']
  let Q : Polynomial B' := MvPolynomial.aeval f p
  have hQ : Polynomial.aeval x Q = 0 := by
    have : Polynomial.aeval x Q =
        MvPolynomial.aeval (fun i => (Polynomial.aeval x).restrictScalars R (f i)) p := by
      rw [← MvPolynomial.comp_aeval]
      rfl
    have hf : (fun i => (Polynomial.aeval x).restrictScalars R (f i)) = ![x, x * η + r] := by
      funext i
      fin_cases i <;> simp [f, η', r'] <;> ring
    rw [this, hf, hp]
  have hQ0 : Q = 0 := transcendental_iff.mp hx Q hQ
  have hdeg : ∀ μ ∈ p.support, μ 0 + μ 1 ≤ D := fun μ hμ => by
    have := MvPolynomial.le_totalDegree hμ
    rwa [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
  have hcoeff : Q.coeff D = ∑ μ ∈ p.support,
      algebraMap R B' (p.coeff μ) * (if μ 0 + μ 1 = D then η' ^ (μ 1) else 0) := by
    simp only [Q, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Fin.prod_univ_two,
      Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [Polynomial.algebraMap_apply, Polynomial.coeff_C_mul]
    congr 1
    exact coeff_X_pow_mul_linear_pow η' r' (μ 0) (μ 1) D (hdeg μ hμ)
  let g : Polynomial R := ∑ μ ∈ p.support,
    if μ 0 + μ 1 = D then Polynomial.C (p.coeff μ) * Polynomial.X ^ (μ 1) else 0
  have hg : Polynomial.aeval η g = ((Q.coeff D : B') : A) := by
    rw [hcoeff]
    simp only [g, map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs <;> simp [η']
  have hg0 : g ≠ 0 := by
    obtain ⟨μ, hμ, hμD⟩ := Finset.exists_mem_eq_sup p.support
      (MvPolynomial.support_nonempty.mpr hp0) (fun s => s.sum fun _ e => e)
    have hμD' : μ 0 + μ 1 = D := by
      rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hμD
      exact hμD.symm
    intro h0
    have hc := congrArg (fun q => Polynomial.coeff q (μ 1)) h0
    simp only [g, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single μ] at hc
    · rw [if_pos hμD', Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
      exact (MvPolynomial.mem_support_iff.mp hμ) hc
    · intro ν _ hνμ
      split_ifs with hν
      · rw [Polynomial.coeff_C_mul_X_pow, if_neg]
        intro h1
        apply hνμ
        ext i
        fin_cases i
        · simp only [Fin.zero_eta]; omega
        · exact h1.symm
      · simp
    · intro h; exact absurd hμ h
  have := transcendental_iff.mp hη g (by rw [hg, hQ0]; simp)
  exact hg0 this

theorem transcendental_of_subset {A R₁ R₂ : Type*} [CommRing A] [CommRing R₁] [CommRing R₂]
    [Algebra R₁ A] [Algebra R₂ A] (S₁ : Subalgebra R₁ A) (S₂ : Subalgebra R₂ A)
    (h : (S₁ : Set A) ⊆ S₂) {x : A} (hx : Transcendental S₂ x) : Transcendental S₁ x := by
  let f : S₁ →+* S₂ :=
    { toFun := fun y => ⟨y, h y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra S₁ S₂ := f.toAlgebra
  have : IsScalarTower S₁ S₂ A := .of_algebraMap_eq fun _ => rfl
  refine hx.restrictScalars ?_
  intro a b hab
  apply Subtype.ext
  have hab' := congrArg Subtype.val hab
  exact hab'

theorem adjoin_subset {A R : Type*} [CommRing A] [CommRing R] [Algebra R A] (T : Subring A)
    (s : Set A) (h1 : ∀ c : R, algebraMap R A c ∈ T) (h2 : s ⊆ T) :
    (Algebra.adjoin R s : Set A) ⊆ T := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem a ha => exact h2 ha
  | algebraMap c => exact h1 c
  | add a b _ _ ha hb => exact T.add_mem ha hb
  | mul a b _ _ ha hb => exact T.mul_mem ha hb

theorem algebraicIndependent_rows (F E : Type) [Field F] [Field E] [Algebra F E] (N k r : ℕ)
    (η : Fin N → E) (hrk : r ≤ k) (j : Fin r → Fin N) (hind : AlgebraicIndependent F (η ∘ j)) :
    AlgebraicIndependent F (Sum.elim (fun ij : Fin k × Fin N => (X ij : MvPolynomial (Fin k × Fin N) E))
      (fun l : Fin r => ∑ m, X (Fin.castLE hrk l, m) * C (η m))) := by
  classical
  let sf : Fin k → MvPolynomial (Fin k × Fin N) E := fun i => ∑ m, X (i, m) * C (η m)
  let g : ℕ → (Fin k × Fin N) ⊕ Fin r → MvPolynomial (Fin k × Fin N) E := fun i =>
    Sum.elim X (fun l => if (l : ℕ) < i then sf (Fin.castLE hrk l) else C (η (j l)))
  have key : ∀ i ≤ r, AlgebraicIndependent F (g i) := by
    intro i
    induction i with
    | zero =>
      intro _
      have := AlgebraicIndependent.sumElim_comp (S := E) hind
        (MvPolynomial.algebraicIndependent_X (Fin k × Fin N) E)
      convert this using 1
      funext t
      rcases t with t | l
      · rfl
      · simp [g, MvPolynomial.algebraMap_eq]
    | succ i ih =>
      intro hi
      have IH := ih (by omega)
      let il : Fin r := ⟨i, by omega⟩
      let i' : Fin k := Fin.castLE hrk il
      let m0 : Fin N := j il
      have hgt : ∀ t, t ≠ Sum.inr il → g (i+1) t = g i t := by
        rintro (t | l) ht
        · rfl
        · have hl : (l : ℕ) ≠ i := fun h => ht (by rw [show l = il from Fin.ext h])
          simp only [g, Sum.elim_inr]
          rcases Nat.lt_or_ge l i with h | h
          · rw [if_pos h, if_pos (by omega)]
          · rw [if_neg (by omega), if_neg (by omega)]
      rw [AlgebraicIndependent.iff_transcendental_adjoin_image (Sum.inr il)]
      refine ⟨?_, ?_⟩
      · have h1 := ((AlgebraicIndependent.iff_transcendental_adjoin_image (Sum.inr il)).mp IH).1
        convert h1 using 1
        funext t
        exact hgt t.1 t.2
      · have himg : g (i+1) '' {Sum.inr il}ᶜ = g i '' {Sum.inr il}ᶜ :=
          Set.image_congr (fun t ht => hgt t ht)
        rw [himg]
        have hval : g (i+1) (Sum.inr il) = sf i' := by simp [g, il, i']
        rw [hval]
        let U : Set ((Fin k × Fin N) ⊕ Fin r) := {Sum.inr il, Sum.inl (i', m0)}ᶜ
        let B := Algebra.adjoin F (g i '' U)
        let x : MvPolynomial (Fin k × Fin N) E := X (i', m0)
        let η0 : MvPolynomial (Fin k × Fin N) E := C (η m0)
        let rr : MvPolynomial (Fin k × Fin N) E := ∑ m ∈ Finset.univ.erase m0, X (i', m) * C (η m)
        have hsplit : sf i' = x * η0 + rr := (Finset.add_sum_erase _ _ (Finset.mem_univ m0)).symm
        have hη : Transcendental B η0 := by
          have := IH.transcendental_adjoin (s := U) (i := Sum.inr il) (by simp [U])
          simpa [g, il] using this
        let T : Subalgebra E (MvPolynomial (Fin k × Fin N) E) :=
          Algebra.adjoin E (X '' {(i', m0)}ᶜ)
        have hXT : ∀ ab, ab ≠ (i', m0) → (X ab : MvPolynomial (Fin k × Fin N) E) ∈ T :=
          fun ab h => Algebra.subset_adjoin ⟨ab, h, rfl⟩
        have hCT : ∀ e : E, (C e : MvPolynomial (Fin k × Fin N) E) ∈ T := fun e => T.algebraMap_mem e
        have hBT : (B : Set (MvPolynomial (Fin k × Fin N) E)) ⊆ T := by
          apply adjoin_subset T.toSubring
          · intro c
            exact hCT (algebraMap F E c)
          · rintro _ ⟨t, ht, rfl⟩
            rcases t with ab | l
            · exact hXT ab (fun h => ht (by simp [h]))
            · have hl : l ≠ il := fun h => ht (by simp [h])
              simp only [g, Sum.elim_inr]
              split_ifs with hli
              · apply T.sum_mem
                intro m _
                apply T.mul_mem _ (hCT _)
                apply hXT
                intro h
                have := congrArg (fun p => (p.1 : ℕ)) h
                simp [i', il] at this
                omega
              · exact hCT _
        have hx : Transcendental (Algebra.adjoin B ({η0, rr} : Set _)) x := by
          refine transcendental_of_subset _ T ?_
            ((MvPolynomial.algebraicIndependent_X _ E).transcendental_adjoin
              (s := {(i', m0)}ᶜ) (i := (i', m0)) (by simp))
          apply adjoin_subset T.toSubring
          · intro c
            exact hBT c.2
          · intro z hz
            rcases hz with rfl | hz
            · exact hCT _
            · rw [Set.mem_singleton_iff] at hz
              subst hz
              apply T.sum_mem
              intro m hm
              exact T.mul_mem (hXT _ (by simpa using (Finset.ne_of_mem_erase hm))) (hCT _)
        have hOV := algebraicIndependent_pair_linear hη hx
        have htr := hOV.transcendental_adjoin (s := {0}) (i := 1) (by simp)
        have htr' : Transcendental (Algebra.adjoin B (![x, x * η0 + rr] '' {0})) (x * η0 + rr) := htr
        rw [hsplit]
        refine transcendental_of_subset _ _ ?_ htr'
        apply adjoin_subset (Algebra.adjoin B (![x, x * η0 + rr] '' {0})).toSubring
        · intro c
          exact (Algebra.adjoin B (![x, x * η0 + rr] '' {0})).algebraMap_mem
            (⟨algebraMap F _ c, B.algebraMap_mem c⟩ : B)
        · rintro _ ⟨t, ht, rfl⟩
          by_cases htx : t = Sum.inl (i', m0)
          · subst htx
            exact Algebra.subset_adjoin ⟨0, rfl, rfl⟩
          · have htU : t ∈ U := by
              simp only [U, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              exact ⟨ht, htx⟩
            exact (Algebra.adjoin B (![x, x * η0 + rr] '' {0})).algebraMap_mem
              (⟨g i t, Algebra.subset_adjoin ⟨t, htU, rfl⟩⟩ : B)
  have := key r le_rfl
  convert this using 1
  funext t
  rcases t with t | l
  · rfl
  · simp [g, sf, l.2]

theorem exists_indep {F E : Type} [Field F] [Field E] [Algebra F E] {N : ℕ} (η : Fin N → E) (d : ℕ)
    (hd : Algebra.trdeg F (Algebra.adjoin F (Set.range η)) = d) :
    ∃ j : Fin d → Fin N, AlgebraicIndependent F (η ∘ j) := by
  classical
  set D := Algebra.adjoin F (Set.range η)
  let ηD : Fin N → D := fun m => ⟨η m, Algebra.subset_adjoin ⟨m, rfl⟩⟩
  have htop : Algebra.adjoin F (Set.range ηD) = ⊤ := by
    apply Subalgebra.map_injective (f := D.val) Subtype.val_injective
    rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
    rfl
  have : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range ηD)) D :=
    ⟨fun y => isAlgebraic_algebraMap (R := Algebra.adjoin F (Set.range ηD))
      (⟨y, by rw [htop]; trivial⟩ : Algebra.adjoin F (Set.range ηD))⟩
  have : FaithfulSMul F D :=
    (faithfulSMul_iff_algebraMap_injective F D).mpr (algebraMap F D).injective
  obtain ⟨t, hts, hb⟩ := exists_isTranscendenceBasis_subset (R := F) (Set.range ηD)
  have hcard : Cardinal.mk t = d := hb.cardinalMk_eq_trdeg.trans hd
  have hfin : t.Finite := (Set.finite_range ηD).subset hts
  have := hfin.fintype
  have hc : Fintype.card t = d := by
    rw [Cardinal.mk_fintype] at hcard
    exact_mod_cast hcard
  let e : Fin d ≃ t := (Fintype.equivFinOfCardEq hc).symm
  have hpre : ∀ l, ∃ m, ηD m = (e l : D) := fun l => hts (e l).2
  choose j hj using hpre
  refine ⟨j, ?_⟩
  have h1 : AlgebraicIndependent F (fun l => ((e l : t) : D)) := hb.1.comp e e.injective
  have h2 := h1.map' (f := D.val) Subtype.val_injective
  convert h2 using 1
  funext l
  simp only [Function.comp_apply]
  rw [← hj l]
  rfl

end GenericLinearTrdeg

theorem GenericLinearTrdeg.proof : GenericLinearTrdeg.Statement := by
  intro F E _ _ _ N k d η hd
  classical
  set S := Algebra.adjoin F
    (Set.range (fun ij : Fin k × Fin N => (X ij : MvPolynomial (Fin k × Fin N) E)) ∪
      Set.range (fun i : Fin k => ∑ m, X (i, m) * C (η m))) with hSdef
  obtain ⟨j, hj⟩ := GenericLinearTrdeg.exists_indep η d hd
  have hrk : min k d ≤ k := min_le_left _ _
  have hrd : min k d ≤ d := min_le_right _ _
  have hind := GenericLinearTrdeg.algebraicIndependent_rows F E N k (min k d) η hrk
    (j ∘ Fin.castLE hrd) (hj.comp _ (Fin.castLE_injective hrd))
  have hlow : ((k * N + min k d : ℕ) : Cardinal) ≤ Algebra.trdeg F S := by
    have hmem : ∀ t, Sum.elim (fun ij : Fin k × Fin N => (X ij : MvPolynomial (Fin k × Fin N) E))
        (fun l : Fin (min k d) => ∑ m, X (Fin.castLE hrk l, m) * C (η m)) t ∈ S := by
      rintro (ab | l)
      · exact Algebra.subset_adjoin (Or.inl ⟨ab, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inr ⟨Fin.castLE hrk l, rfl⟩)
    let G' : (Fin k × Fin N) ⊕ Fin (min k d) → S := fun t => ⟨_, hmem t⟩
    have hG : AlgebraicIndependent F G' := AlgebraicIndependent.of_comp S.val hind
    have := hG.cardinalMk_le_trdeg
    have hc : Cardinal.mk ((Fin k × Fin N) ⊕ Fin (min k d)) = ((k * N + min k d : ℕ) : Cardinal) := by
      rw [Cardinal.mk_fintype]
      simp
    rwa [hc] at this
  have hup1 : Algebra.trdeg F S ≤ ((k * N + k : ℕ) : Cardinal) := by
    let G : (Fin k × Fin N) ⊕ Fin k → MvPolynomial (Fin k × Fin N) E :=
      Sum.elim (fun ij => X ij) (fun i => ∑ m, X (i, m) * C (η m))
    have hS : S = (MvPolynomial.aeval (R := F) G).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval, Set.Sum.elim_range]
    have h1 := trdeg_le_of_surjective (MvPolynomial.aeval (R := F) G).rangeRestrict
      (AlgHom.rangeRestrict_surjective _)
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype] at h1
    rw [hS]
    convert h1 using 1
    simp
  have hup2 : Algebra.trdeg F S ≤ ((k * N + d : ℕ) : Cardinal) := by
    set D := Algebra.adjoin F (Set.range η)
    let φ : MvPolynomial (Fin k × Fin N) D →ₐ[F] MvPolynomial (Fin k × Fin N) E :=
      MvPolynomial.mapAlgHom D.val
    have hle : S ≤ φ.range := by
      rw [hSdef, Algebra.adjoin_le_iff]
      rintro _ (⟨ab, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨X ab, by simp [φ]⟩
      · refine ⟨∑ m, X (i, m) * C ⟨η m, Algebra.subset_adjoin ⟨m, rfl⟩⟩, ?_⟩
        simp [φ]
    have h1 := trdeg_le_of_injective (Subalgebra.inclusion hle) (Subalgebra.inclusion_injective hle)
    have h2 := trdeg_le_of_surjective φ.rangeRestrict (AlgHom.rangeRestrict_surjective _)
    have : FaithfulSMul F D :=
      (faithfulSMul_iff_algebraMap_injective F D).mpr (algebraMap F D).injective
    have : FaithfulSMul D (MvPolynomial (Fin k × Fin N) D) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (MvPolynomial.C_injective _ _)
    have h3 := trdeg_add_eq F D (A := MvPolynomial (Fin k × Fin N) D)
    rw [MvPolynomial.trdeg_of_isDomain, hd, Cardinal.lift_id, Cardinal.mk_fintype] at h3
    refine h1.trans (h2.trans (le_of_eq ?_))
    rw [← h3]
    simp [add_comm]
  refine le_antisymm ?_ hlow
  rcases le_total k d with h | h
  · rw [min_eq_left h]; exact hup1
  · rw [min_eq_right h]; exact hup2

end GroundTheory.Heights₂.Heights
