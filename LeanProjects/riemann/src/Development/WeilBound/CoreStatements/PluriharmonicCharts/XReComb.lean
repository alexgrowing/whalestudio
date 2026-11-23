import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.WeilBound.CoreStatements.FlagImmersions.IntersectionMultilinearExpansion

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

private theorem isSmoothHerm_combLine' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type}
    [Fintype σ] (A : σ → HermLine ι) (hA : ∀ a, IsSmoothHerm (A a)) (d : σ → ℤ) :
    IsSmoothHerm (combLine A d) := by
  classical
  unfold IsSmoothHerm
  have hfun : (combLine A d).h = fun z => ∏ x : σ, (A x).h z ^ d x := funext (combLine_h A d)
  rw [hfun]
  apply contDiffOn_prod
  intro x _
  rcases Int.eq_nat_or_neg (d x) with ⟨m, hm | hm⟩
  · simp_rw [hm, zpow_natCast]
    exact (hA x).pow m
  · simp_rw [hm, zpow_neg, zpow_natCast]
    exact ((hA x).pow m).inv (fun z hz => pow_ne_zero _ ((A x).pos z hz).ne')

private theorem II_update_combLine (hML : MetricLocalStatement) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι)
    (hA : ∀ a, IsSmoothHerm (A a)) (hP : IsArithVar P n) (L : Fin n → HermLine ι)
    (hL : ∀ r, IsSmoothHerm (L r)) (j : Fin n) (d : σ → ℤ) :
    II K ι P n (Function.update L j (combLine A d)) =
      ∑ a, (d a : ℝ) * II K ι P n (Function.update L j (A a)) := by
  classical
  have hsm : ∀ (M : HermLine ι), IsSmoothHerm M → ∀ r, IsSmoothHerm (Function.update L j M r) := by
    intro M hM r
    by_cases h : r = j
    · subst h
      simpa using hM
    · simpa [Function.update_of_ne h] using hL r
  have hloc : ∀ M M' : HermLine ι, IsSmoothHerm M → IsSmoothHerm M' → M.a = M'.a →
      (∀ z ∈ mcPts P, M.h z = M'.h z) →
      II K ι P n (Function.update L j M) = II K ι P n (Function.update L j M') := by
    intro M M' hM hM' ha hh
    apply hML K ι (II K ι) (hII.1 K ι) P n _ _ hP (hsm M hM) (hsm M' hM')
    · intro r
      by_cases h : r = j
      · subst h
        simp [ha]
      · simp [Function.update_of_ne h]
    · intro r z hz
      by_cases h : r = j
      · subst h
        simpa using hh z hz
      · simp [Function.update_of_ne h]
  let G : (σ → ℤ) → ℝ := fun d => II K ι P n (Function.update L j (combLine A d))
  have hadd : ∀ d d', G (d + d') = G d + G d' := by
    intro d d'
    have h1 : G (d + d') =
        II K ι P n (Function.update L j ((combLine A d).tensor (combLine A d'))) := by
      apply hloc _ _ (isSmoothHerm_combLine' A hA _)
        (by unfold IsSmoothHerm; exact (isSmoothHerm_combLine' A hA d).mul (isSmoothHerm_combLine' A hA d'))
      · funext k
        show (combLine A (d + d')).a k = (combLine A d).a k + (combLine A d').a k
        rw [combLine_a, combLine_a, combLine_a, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Pi.add_apply]
        ring
      · intro z hz
        show (combLine A (d + d')).h z = (combLine A d).h z * (combLine A d').h z
        rw [combLine_h, combLine_h, combLine_h, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun x _ => ?_
        exact zpow_add₀ ((A x).pos z hz.1).ne' _ _
    rw [h1]
    exact hII.2.1 K ι P n L j _ _ hP hL (isSmoothHerm_combLine' A hA d) (isSmoothHerm_combLine' A hA d')
  have hsingle : ∀ a, G (Pi.single a 1) = II K ι P n (Function.update L j (A a)) := by
    intro a
    apply hloc _ _ (isSmoothHerm_combLine' A hA _) (hA a)
    · funext k
      rw [combLine_a]
      simp [Pi.single_apply]
    · intro z _
      rw [combLine_h, Finset.prod_eq_single a]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
  let Gh : (σ → ℤ) →+ ℝ := AddMonoidHom.mk' G hadd
  have hd : d = ∑ a, d a • Pi.single a (1 : ℤ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  show G d = _
  calc G d = Gh d := rfl
    _ = Gh (∑ a, d a • Pi.single a (1 : ℤ)) := by rw [← hd]
    _ = ∑ a, (d a : ℝ) * G (Pi.single a 1) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_zsmul, zsmul_eq_mul]
      rfl
    _ = _ := by simp_rw [hsingle]

private theorem II_combLine_eq_polar (hML : MetricLocalStatement) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ)
    (hP : IsArithVar P n) (hA : ∀ a, IsSmoothHerm (A a)) :
    II K ι P n (fun r => combLine A (c r)) =
      polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) := by
  classical
  unfold polar
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨a0⟩⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Fintype.sum_unique]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
      congr 1
      funext r
      exact r.elim0
    · obtain ⟨j⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      haveI : IsEmpty (Fin n → σ) := ⟨fun w => hσ.elim (w j)⟩
      have e : (fun r => combLine A (c r)) =
          Function.update (fun r => combLine A (c r)) j (combLine A (c j)) := by simp
      rw [e, II_update_combLine hML II hII K ι σ P n A hA hP _ (fun r => isSmoothHerm_combLine' A hA (c r)) j (c j)]
      simp [Finset.univ_eq_empty]
  · let t : Finset (Fin n) → Fin n → Finset σ := fun S r => if r ∈ S then Finset.univ else {a0}
    let line : Finset (Fin n) → (Fin n → σ) → Fin n → HermLine ι :=
      fun S w r => if r ∈ S then A (w r) else combLine A (c r)
    have hsm : ∀ S w r, IsSmoothHerm (line S w r) := by
      intro S w r
      simp only [line]
      split_ifs
      · exact hA _
      · exact isSmoothHerm_combLine' A hA _
    have key : ∀ S : Finset (Fin n), II K ι P n (fun r => combLine A (c r)) =
        ∑ w ∈ Fintype.piFinset (t S), (∏ r ∈ S, (c r (w r) : ℝ)) * II K ι P n (line S w) := by
      intro S
      refine Finset.induction_on S ?_ ?_
      · have h0 : Fintype.piFinset (t ∅) = {fun _ => a0} := by
          ext w
          simp [t, Fintype.mem_piFinset, funext_iff]
        rw [h0, Finset.sum_singleton]
        simp [line]
      · intro j S hj ih
        rw [ih]
        have hexp : ∀ w ∈ Fintype.piFinset (t S),
            (∏ r ∈ S, (c r (w r) : ℝ)) * II K ι P n (line S w) =
              ∑ a, (∏ r ∈ insert j S, (c r (Function.update w j a r) : ℝ)) *
                II K ι P n (line (insert j S) (Function.update w j a)) := by
          intro w _
          have hl : line S w = Function.update (line S w) j (combLine A (c j)) := by
            funext r
            by_cases h : r = j
            · subst h
              simp [line, hj]
            · simp [Function.update_of_ne h]
          rw [hl, II_update_combLine hML II hII K ι σ P n A hA hP _ (hsm S w) j (c j), Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          have hupd : Function.update (line S w) j (A a) = line (insert j S) (Function.update w j a) := by
            funext r
            by_cases h : r = j
            · subst h
              simp [line]
            · simp [line, Function.update_of_ne h, Finset.mem_insert, h]
          rw [hupd, Finset.prod_insert hj, Function.update_self]
          have hprod : ∏ r ∈ S, (c r (Function.update w j a r) : ℝ) = ∏ r ∈ S, (c r (w r) : ℝ) :=
            Finset.prod_congr rfl fun r hr => by
              have hrj : r ≠ j := fun h => hj (h ▸ hr)
              rw [Function.update_of_ne hrj]
          rw [hprod]
          ring
        rw [Finset.sum_congr rfl hexp, ← Finset.sum_product']
        apply Finset.sum_nbij' (fun p => Function.update p.1 j p.2) (fun w => (Function.update w j a0, w j))
        · rintro ⟨w, a⟩ hp
          simp only [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset] at hp ⊢
          intro r
          by_cases h : r = j
          · subst h
            simp [t]
          · rw [Function.update_of_ne h]
            have := hp.1 r
            simpa [t, Finset.mem_insert, h] using this
        · intro w hw
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true, Fintype.mem_piFinset] at hw ⊢
          intro r
          by_cases h : r = j
          · subst h
            simp [t, hj]
          · rw [Function.update_of_ne h]
            have := hw r
            simpa [t, Finset.mem_insert, h] using this
        · rintro ⟨w, a⟩ hp
          simp only [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset] at hp
          have hwj : w j = a0 := by simpa [t, hj] using hp.1 j
          simp [Function.update_idem, ← hwj]
        · intro w _
          simp [Function.update_idem]
        · intro p _
          rfl
    rw [key Finset.univ]
    have hu : Fintype.piFinset (t Finset.univ) = Finset.univ := by
      ext w
      simp [t]
    rw [hu]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [line]

theorem PositivityTheory.Xgp.t_re_comb : MetricLocalStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ), IsArithVar P n → (∀ a, IsSmoothHerm (A a)) → (∀ r, IsSmoothHerm (combLine A (c r))) ∧ II K ι P n (fun r => combLine A (c r)) = polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) := by
  intro hML II hII K _ ι _ σ _ P n A c hP hA
  exact ⟨fun r => isSmoothHerm_combLine' A hA (c r), II_combLine_eq_polar hML II hII K ι σ P n A c hP hA⟩
