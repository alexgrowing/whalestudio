import Mathlib

open scoped BigOperators
open Polynomial

namespace GlobalTheory.SplittingAlgebra

theorem exists_monomials_span (t : ℕ) : ∃ e : Fin t.factorial → Fin t → ℕ,
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (y : Fin t → A),
      (∏ c, (X - C (y c))) ∈ Polynomial.lifts (algebraMap R A) →
      ∀ a ∈ Algebra.adjoin R (Set.range y),
        ∃ cf : Fin t.factorial → R, a = ∑ k, cf k • ∏ c, y c ^ e k c := by
  induction t with
  | zero =>
    refine ⟨fun _ _ => 0, fun R A _ _ _ y _ a ha => ?_⟩
    rw [Set.range_eq_empty, Algebra.adjoin_empty, Algebra.mem_bot] at ha
    obtain ⟨r, rfl⟩ := ha
    refine ⟨fun _ => r, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [Algebra.algebraMap_eq_smul_one]
  | succ t ih =>
    obtain ⟨e, he⟩ := ih
    let E : Fin (t + 1).factorial ≃ Fin (t + 1) × Fin t.factorial :=
      (finCongr (Nat.factorial_succ t)).trans finProdFinEquiv.symm
    refine ⟨fun k => Fin.cons ((E k).1 : ℕ) (e (E k).2), fun R A _ _ _ y hP a ha => ?_⟩
    have hPm : (∏ c, (X - C (y c))).Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C _
    obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hP hPm
    have hdeg : q.natDegree ≤ t + 1 := by
      rw [hqd]
      refine (natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => 1) fun c _ => natDegree_X_sub_C_le _).trans ?_
      simp
    have hq0 : aeval (y 0) q = 0 := by
      rw [← eval_map_algebraMap, hq, Fin.prod_univ_succ]
      simp
    set R1 := Algebra.adjoin R {y 0} with hR1
    have hR1s : ∀ s ∈ R1, ∃ d : Fin (t + 1) → R, s = ∑ i, d i • y 0 ^ (i : ℕ) := by
      intro s hs
      classical
      have h1 : s ∈ Subalgebra.toSubmodule R1 := hs
      rw [hR1, ← Submodule.span_range_natDegree_eq_adjoin hqm hq0] at h1
      have h2 : s ∈ Submodule.span R (Set.range fun i : Fin (t + 1) => y 0 ^ (i : ℕ)) := by
        refine Submodule.span_mono ?_ h1
        intro z hz
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hz
        obtain ⟨i, hi, rfl⟩ := hz
        exact ⟨⟨i, by omega⟩, rfl⟩
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
      exact ⟨d, hd.symm⟩
    have hQ : (∏ c : Fin t, (X - C (y c.succ))) ∈ Polynomial.lifts (algebraMap R1 A) := by
      let y0 : R1 := ⟨y 0, Algebra.self_mem_adjoin_singleton R _⟩
      refine ⟨(q.map (algebraMap R R1)) /ₘ (X - C y0), ?_⟩
      rw [coe_mapRingHom, map_divByMonic _ (monic_X_sub_C _), Polynomial.map_map,
        ← IsScalarTower.algebraMap_eq, hq, Fin.prod_univ_succ]
      have : Polynomial.map (algebraMap R1 A) (X - C y0) = X - C (y 0) := by
        simp [y0]
      rw [this, mul_divByMonic_cancel_left _ (monic_X_sub_C _)]
    have ha' : a ∈ Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ) := by
      have : Algebra.adjoin R (Set.range y) ≤
          (Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ)).restrictScalars R := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨c, rfl⟩
        refine Fin.cases ?_ (fun c => ?_) c
        · exact Subalgebra.algebraMap_mem (Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ))
            (⟨y 0, Algebra.self_mem_adjoin_singleton R _⟩ : R1)
        · exact Algebra.subset_adjoin (R := R1) (s := Set.range fun c : Fin t => y c.succ) ⟨c, rfl⟩
      exact this ha
    obtain ⟨cf, hcf⟩ := he R1 A (fun c => y c.succ) hQ a ha'
    choose d hd using fun k => hR1s (cf k) (cf k).2
    refine ⟨fun k => d (E k).2 (E k).1, ?_⟩
    rw [hcf, ← E.symm.sum_comp, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, hd k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Fin.prod_univ_succ]

theorem adjoin_perm_eq_top {K : Type} [Field K] {t : ℕ} (α : Fin t → K)
    (hα : Function.Injective α) (f : Equiv.Perm (Fin t) → K) :
    f ∈ Algebra.adjoin K (Set.range fun (c : Fin t) (σ : Equiv.Perm (Fin t)) => α (σ c)) := by
  classical
  set S := Algebra.adjoin K (Set.range fun (c : Fin t) (σ : Equiv.Perm (Fin t)) => α (σ c))
  have h1 : ∀ σ : Equiv.Perm (Fin t), (Pi.single σ (1 : K) : Equiv.Perm (Fin t) → K) ∈ S := by
    intro σ
    have : (Pi.single σ (1 : K) : Equiv.Perm (Fin t) → K) =
        ∏ c, aeval (fun τ : Equiv.Perm (Fin t) => α (τ c)) (Lagrange.basis Finset.univ α (σ c)) := by
      funext τ
      rw [Finset.prod_apply]
      simp only [aeval_pi_apply₂, coe_aeval_eq_eval]
      by_cases h : τ = σ
      · subst h
        rw [Pi.single_eq_same]
        exact (Finset.prod_eq_one fun c _ =>
          Lagrange.eval_basis_self hα.injOn (Finset.mem_univ _)).symm
      · rw [Pi.single_eq_of_ne h]
        obtain ⟨c, hc⟩ : ∃ c, σ c ≠ τ c := by
          by_contra hh
          push_neg at hh
          exact h (Equiv.ext fun c => (hh c).symm)
        exact (Finset.prod_eq_zero (Finset.mem_univ c)
          (Lagrange.eval_basis_of_ne hc (Finset.mem_univ _))).symm
    rw [this]
    refine Subalgebra.prod_mem _ fun c _ => ?_
    refine Algebra.adjoin_mono ?_ (aeval_mem_adjoin_singleton K _)
    rintro _ rfl
    exact ⟨c, rfl⟩
  rw [pi_eq_sum_univ' f]
  exact Subalgebra.sum_mem _ fun σ _ => Subalgebra.smul_mem _ (h1 σ) _

theorem coeff_prod_apply {O I : Type} [CommRing O] {t : ℕ} (y : Fin t → I → O) (i : I) (j : ℕ) :
    (∏ c, (X - C (y c))).coeff j i = (∏ c, (X - C (y c i))).coeff j := by
  have := coeff_map (p := ∏ c, (X - C (y c))) (Pi.evalRingHom (fun _ : I => O) i) j
  rw [Polynomial.map_prod] at this
  simpa using this.symm

theorem main : ∀ {O X : Type} [CommRing O] [IsDomain O] [Finite X] (T : Subalgebra O (X → O)) (t : ℕ) (α : X → Fin t → O), (∀ x, Function.Injective (α x)) → (∀ x y, x ≠ y → ∃ f ∈ T, f x ≠ f y) → (∀ j, (fun x => (∏ c, (Polynomial.X - Polynomial.C (α x c))).coeff j) ∈ T) → let T' : Subalgebra O (X × Equiv.Perm (Fin t) → O) := Algebra.adjoin O ((fun f : X → O => fun x' => f x'.1) '' (T : Set (X → O)) ∪ Set.range fun c : Fin t => fun x' => α x'.1 (x'.2 c)); ∃ b : Fin t.factorial → X × Equiv.Perm (Fin t) → O, (∀ k, b k ∈ T') ∧ ∀ f ∈ T', ∃! cf : Fin t.factorial → T, f = ∑ k, (fun x' => (cf k : X → O) x'.1) * b k := by
  intro O Y _ _ _ T t α hα _ hT T'
  obtain ⟨e, he⟩ := exists_monomials_span t
  let y : Fin t → Y × Equiv.Perm (Fin t) → O := fun c x' => α x'.1 (x'.2 c)
  refine ⟨fun k => ∏ c, y c ^ e k c, fun k => ?_, fun f hf => ?_⟩
  · have hy : ∀ c, y c ∈ T' := fun c =>
      Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_range_self c))
    exact Subalgebra.prod_mem _ fun c _ => Subalgebra.pow_mem _ (hy c) _
  have hind : ∀ (x : Y) (d : Fin t.factorial → O),
      (∀ σ : Equiv.Perm (Fin t), ∑ k, d k * ∏ c, α x (σ c) ^ e k c = 0) → ∀ k, d k = 0 := by
    intro x d hd k
    let K := FractionRing O
    have hi : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
    let β : Fin t → K := fun c => algebraMap O K (α x c)
    let z : Fin t → Equiv.Perm (Fin t) → K := fun c σ => β (σ c)
    have hl : (∏ c, (X - C (z c))) ∈ Polynomial.lifts (algebraMap K (Equiv.Perm (Fin t) → K)) := by
      rw [lifts_iff_coeff_lifts]
      intro j
      refine ⟨(∏ c, (X - C (β c))).coeff j, funext fun σ => ?_⟩
      rw [coeff_prod_apply, Equiv.prod_comp σ (fun c => X - C (β c))]
      rfl
    have hli : LinearIndependent K (fun k => ∏ c, z c ^ e k c) := by
      refine linearIndependent_of_top_le_span_of_card_eq_finrank (fun g _ => ?_) ?_
      · obtain ⟨cf, hcf⟩ := he K _ z hl g (adjoin_perm_eq_top β (hi.comp (hα x)) g)
        exact (Submodule.mem_span_range_iff_exists_fun K).2 ⟨cf, hcf.symm⟩
      · simp [Fintype.card_perm]
    have := Fintype.linearIndependent_iff.1 hli (fun k => algebraMap O K (d k)) (by
      funext σ
      have := congrArg (algebraMap O K) (hd σ)
      simpa [z, β, Finset.sum_apply, Finset.prod_apply, Algebra.smul_def] using this) k
    exact hi (by simpa using this)
  let φ : T →+* (Y × Equiv.Perm (Fin t) → O) :=
    Pi.ringHom fun x' => (Pi.evalRingHom (fun _ : Y => O) x'.1).comp T.val.toRingHom
  letI : Algebra T (Y × Equiv.Perm (Fin t) → O) := φ.toAlgebra
  have hl : (∏ c, (X - C (y c))) ∈
      Polynomial.lifts (algebraMap T (Y × Equiv.Perm (Fin t) → O)) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    refine ⟨⟨_, hT j⟩, funext fun x' => ?_⟩
    rw [coeff_prod_apply, Equiv.prod_comp x'.2 (fun c => X - C (α x'.1 c))]
    rfl
  have hf' : f ∈ Algebra.adjoin T (Set.range y) := by
    induction hf using Algebra.adjoin_induction with
    | mem g hg =>
      rcases hg with ⟨g, hg, rfl⟩ | hg
      · exact Subalgebra.algebraMap_mem _ (⟨g, hg⟩ : T)
      · exact Algebra.subset_adjoin hg
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (algebraMap O T r)
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  obtain ⟨cf, hcf⟩ := he T _ y hl f hf'
  refine ⟨cf, hcf, fun cg hcg => ?_⟩
  funext k
  ext x
  refine sub_eq_zero.1 (hind x (fun k => (cg k : Y → O) x - (cf k : Y → O) x) (fun σ => ?_) k)
  have h1 : f = ∑ k, (fun x' => (cf k : Y → O) x'.1) * ∏ c, y c ^ e k c := hcf
  have h2 := congrFun (hcg.symm.trans h1) (x, σ)
  simp only [Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.pow_apply, y] at h2
  simp only [sub_mul, Finset.sum_sub_distrib, h2, sub_self]

end GlobalTheory.SplittingAlgebra
