import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreLie

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

section Gen

variable {σ κ : Type} [Fintype κ]

private theorem coeff_pderiv_real_seminorm_filtration (l : σ) (P : MvPolynomial σ ℂ) (γ : σ →₀ ℕ) :
    coeff γ (pderiv l P) = coeff (γ + Finsupp.single l 1) P * ((γ l : ℂ) + 1) := by
  classical
  refine MvPolynomial.induction_on' P (fun s a => ?_) (fun p q hp hq => ?_)
  · rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases hs : s = γ + Finsupp.single l 1
    · subst hs
      simp
    · rw [if_neg hs, zero_mul]
      rcases Nat.eq_zero_or_pos (s l) with h0 | hpos
      · simp [h0]
      · rw [if_neg]
        intro h
        apply hs
        rw [← h]
        exact (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hpos)).symm
  · simp [hp, hq, add_mul]

theorem supp_wt_term (w : σ → ℕ) (l l' : σ) (P : MvPolynomial σ ℂ) (γ : σ →₀ ℕ)
    (h : coeff γ (X l * pderiv l' P) ≠ 0) :
    ∃ β ∈ P.support, Finsupp.weight w β + w l = Finsupp.weight w γ + w l' := by
  classical
  rw [coeff_X_mul'] at h
  split_ifs at h with hl
  · rw [coeff_pderiv_real_seminorm_filtration] at h
    refine ⟨γ - Finsupp.single l 1 + Finsupp.single l' 1, ?_, ?_⟩
    · rw [mem_support_iff]
      intro h0
      apply h
      rw [h0, zero_mul]
    · have hle : Finsupp.single l 1 ≤ γ := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hl)
      have hsw : ∀ y, Finsupp.weight w (Finsupp.single y 1) = w y := by
        intro y
        simp [Finsupp.weight_apply]
      have key := congrArg (Finsupp.weight w) (tsub_add_cancel_of_le hle)
      rw [map_add, hsw] at key
      rw [map_add, hsw]
      omega
  · exact absurd rfl h

private theorem weight_le_of_mem_support_mul_of_right (w : σ → ℕ) (k : ℕ) (F G : MvPolynomial σ ℂ)
    (hG : ∀ γ ∈ G.support, k ≤ Finsupp.weight w γ) :
    ∀ γ ∈ (F * G).support, k ≤ Finsupp.weight w γ := by
  classical
  intro γ hγ
  obtain ⟨a, _, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul F G hγ)
  rw [map_add]
  exact le_add_left (hG b hb)

private theorem weight_le_of_mem_support_sum {ι : Type} (w : σ → ℕ) (k : ℕ) (s : Finset ι)
    (F : ι → MvPolynomial σ ℂ) (hF : ∀ i ∈ s, ∀ γ ∈ (F i).support, k ≤ Finsupp.weight w γ) :
    ∀ γ ∈ (∑ i ∈ s, F i).support, k ≤ Finsupp.weight w γ := by
  classical
  intro γ hγ
  obtain ⟨i, hi, hγi⟩ := Finset.mem_biUnion.mp (support_sum hγ)
  exact hF i hi γ hγi

private theorem exists_mem_support_mul_weight_eq_of_weight_zero (w : σ → ℕ) (b : ℕ) (D g : MvPolynomial σ ℂ) (hD0 : D ≠ 0)
    (hD : ∀ γ ∈ D.support, Finsupp.weight w γ = 0)
    (hg : ∀ γ ∈ g.support, b ≤ Finsupp.weight w γ) (γ0 : σ →₀ ℕ) (hγ0 : γ0 ∈ g.support)
    (hb : Finsupp.weight w γ0 = b) :
    ∃ γ ∈ (D * g).support, Finsupp.weight w γ = b := by
  classical
  let g0 : MvPolynomial σ ℂ :=
    ∑ x ∈ g.support.filter (fun x => Finsupp.weight w x = b), monomial x (coeff x g)
  have hc0 : ∀ γ, coeff γ g0 = if Finsupp.weight w γ = b then coeff γ g else 0 := by
    intro γ
    by_cases hγ : coeff γ g = 0 <;>
      simp [g0, coeff_sum, coeff_monomial, Finset.mem_filter, mem_support_iff, hγ]
  have hg0 : g0 ≠ 0 := by
    intro h
    have h1 := hc0 γ0
    rw [h, if_pos hb, coeff_zero] at h1
    exact (mem_support_iff.mp hγ0) h1.symm
  obtain ⟨γ, hγ⟩ := PI.FJMP.exists_mem_support (mul_ne_zero hD0 hg0)
  have hwγ : Finsupp.weight w γ = b := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp (support_mul D g0 hγ)
    rw [← hxy, map_add, hD x hx, zero_add]
    have h2 := mem_support_iff.mp hy
    rw [hc0] at h2
    by_contra hne
    exact h2 (if_neg hne)
  refine ⟨γ, ?_, hwγ⟩
  have hsplit : D * g = D * g0 + D * (g - g0) := by ring
  have hrest : ∀ δ ∈ (D * (g - g0)).support, b + 1 ≤ Finsupp.weight w δ := by
    apply weight_le_of_mem_support_mul_of_right
    intro δ hδ
    rw [mem_support_iff, coeff_sub, hc0] at hδ
    by_cases hδb : Finsupp.weight w δ = b
    · rw [if_pos hδb, sub_self] at hδ
      exact absurd rfl hδ
    · rw [if_neg hδb, sub_zero] at hδ
      have h3 := hg δ (mem_support_iff.mpr hδ)
      omega
  rw [mem_support_iff, hsplit, coeff_add]
  have h4 : coeff γ (D * (g - g0)) = 0 := by
    by_contra hne
    have h5 := hrest γ (mem_support_iff.mpr hne)
    omega
  rw [h4, add_zero]
  exact mem_support_iff.mp hγ

theorem supp_gen_pos {N : ℕ} (pos : κ → Bool) (ρ : Fin N → κ) (hρ : ∀ c, pos c = true ↔ ∃ i, ρ i = c)
    (hρi : Function.Injective ρ) (u : Fin N → κ → σ) (v : κ → σ)
    (hu : Function.Injective (fun x : Fin N × Fin N => u x.1 (ρ x.2)))
    (huv : ∀ j c c', u j c ≠ v c') (hv : Function.Injective v) (P : MvPolynomial σ ℂ) (hP : P ≠ 0)
    (hR : ∀ j, PI.FJMP.gR (u j) v pos P = 0) : ∃ e ∈ P.support, PI.FJMP.sw e v pos ≤ 0 := by
  classical
  suffices key : ∃ e ∈ P.support, ∀ c, pos c = true → e (v c) = 0 by
    obtain ⟨e, he, hz⟩ := key
    refine ⟨e, he, ?_⟩
    unfold PI.FJMP.sw
    apply Finset.sum_nonpos
    intro c _
    by_cases hc : pos c = true
    · rw [if_pos hc, hz c hc]
      simp
    · rw [if_neg hc]
      simp
  by_contra hk
  push_neg at hk
  let w : σ → ℕ := fun y => if ∃ c, pos c = false ∧ v c = y then 1 else 0
  have hwu : ∀ j c, w (u j c) = 0 := by
    intro j c
    simp only [w]
    rw [if_neg]
    rintro ⟨c', _, hc'⟩
    exact huv j c c' hc'.symm
  have hwpos : ∀ c, pos c = true → w (v c) = 0 := by
    intro c hc
    simp only [w]
    rw [if_neg]
    rintro ⟨c', hc', h'⟩
    rw [hv h', hc] at hc'
    exact absurd hc' (by decide)
  have hwneg : ∀ c, ¬ pos c = true → w (v c) = 1 := by
    intro c hc
    simp only [w]
    rw [if_pos]
    exact ⟨c, by simpa using hc, rfl⟩
  have hsw : ∀ y, Finsupp.weight w (Finsupp.single y 1) = w y := by
    intro y
    simp [Finsupp.weight_apply]
  obtain ⟨e1, he1⟩ := PI.FJMP.exists_mem_support hP
  obtain ⟨e0, he0, hmin⟩ := Finset.exists_min_image P.support (Finsupp.weight w) ⟨e1, he1⟩
  obtain ⟨c0, hc0, he0c⟩ := hk e0 he0
  obtain ⟨i0, hi0⟩ := (hρ c0).mp hc0
  have hpos0 : pos (ρ i0) = true := by rw [hi0]; exact hc0
  have himg : Finset.univ.filter (fun c => pos c = true) = Finset.univ.image ρ := by
    ext c
    simp [hρ c]
  let g : Fin N → MvPolynomial σ ℂ := fun i => pderiv (v (ρ i)) P
  let R : Fin N → MvPolynomial σ ℂ := fun j =>
    ∑ c ∈ Finset.univ.filter (fun c => ¬ pos c = true), X (v c) * pderiv (u j c) P
  have hid : ∀ j, ∑ i, X (u j (ρ i)) * g i = R j := by
    intro j
    have h := hR j
    unfold PI.FJMP.gR at h
    rw [Finset.sum_ite, himg, Finset.sum_image (fun a _ b _ hab => hρi hab),
      Finset.sum_neg_distrib, add_neg_eq_zero] at h
    exact h
  let f : Fin N × Fin N → σ := fun x => u x.1 (ρ x.2)
  have hfi : Function.Injective f := hu
  let M : Matrix (Fin N) (Fin N) (MvPolynomial σ ℂ) :=
    (rename f).mapMatrix (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ)
  have hM : ∀ j i, M j i = X (u j (ρ i)) := by
    intro j i
    simp [M, f, AlgHom.mapMatrix_apply, Matrix.mvPolynomialX_apply, rename_X]
  have hMv : M *ᵥ g = R := by
    funext j
    change ∑ i, M j i * g i = R j
    simp only [hM]
    exact hid j
  have hdet : M.det * g i0 = ∑ j, M.adjugate i0 j * R j := by
    have h1 := congrArg (fun x => M.adjugate *ᵥ x) hMv
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul] at h1
    have h2 := congrFun h1 i0
    have h3 : ((M.det • (1 : Matrix (Fin N) (Fin N) (MvPolynomial σ ℂ))) *ᵥ g) i0 = M.det * g i0 := by
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
    rw [← h3, h2]
    rfl
  have hdetM : M.det = rename f (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).det :=
    (AlgHom.map_det (rename f) _).symm
  have hD0 : M.det ≠ 0 := by
    rw [hdetM]
    exact (map_ne_zero_iff _ (rename_injective f hfi)).mpr (Matrix.det_mvPolynomialX_ne_zero _ _)
  have hD : ∀ γ ∈ M.det.support, Finsupp.weight w γ = 0 := by
    intro γ hγ
    rw [hdetM, support_rename_of_injective hfi, Finset.mem_image] at hγ
    obtain ⟨δ, _, rfl⟩ := hγ
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • w i)
      (fun b => zero_smul ℕ (w b)) (fun b m1 m2 => add_smul m1 m2 (w b))]
    simp [Finsupp.sum, f, hwu]
  have hR1 : ∀ j, ∀ γ ∈ (R j).support, Finsupp.weight w e0 + 1 ≤ Finsupp.weight w γ := by
    intro j
    exact weight_le_of_mem_support_sum w _ _ _ (fun c hc γ hγ => by
      have hc' : ¬ pos c = true := (Finset.mem_filter.mp hc).2
      obtain ⟨β, hβ, hβw⟩ := supp_wt_term w (v c) (u j c) P γ (mem_support_iff.mp hγ)
      rw [hwneg c hc', hwu j c] at hβw
      have h1 := hmin β hβ
      omega)
  have hRHS : ∀ γ ∈ (∑ j, M.adjugate i0 j * R j).support,
      Finsupp.weight w e0 + 1 ≤ Finsupp.weight w γ :=
    weight_le_of_mem_support_sum w _ _ _ (fun j _ => weight_le_of_mem_support_mul_of_right w _ _ _ (hR1 j))
  have hg : ∀ γ ∈ (g i0).support, Finsupp.weight w e0 ≤ Finsupp.weight w γ := by
    intro γ hγ
    have h1 := mem_support_iff.mp hγ
    change coeff γ (pderiv (v (ρ i0)) P) ≠ 0 at h1
    rw [coeff_pderiv_real_seminorm_filtration] at h1
    have hmem : γ + Finsupp.single (v (ρ i0)) 1 ∈ P.support := by
      rw [mem_support_iff]
      intro h0
      apply h1
      rw [h0, zero_mul]
    have h2 := hmin _ hmem
    rw [map_add, hsw, hwpos _ hpos0] at h2
    omega
  have hle : Finsupp.single (v (ρ i0)) 1 ≤ e0 := by
    rw [Finsupp.single_le_iff, hi0]
    exact Nat.one_le_iff_ne_zero.mpr he0c
  have hadd : e0 - Finsupp.single (v (ρ i0)) 1 + Finsupp.single (v (ρ i0)) 1 = e0 :=
    tsub_add_cancel_of_le hle
  have hγ0 : e0 - Finsupp.single (v (ρ i0)) 1 ∈ (g i0).support := by
    rw [mem_support_iff]
    change coeff _ (pderiv (v (ρ i0)) P) ≠ 0
    rw [coeff_pderiv_real_seminorm_filtration, hadd]
    exact mul_ne_zero (mem_support_iff.mp he0) (Nat.cast_add_one_ne_zero _)
  have hwγ0 : Finsupp.weight w (e0 - Finsupp.single (v (ρ i0)) 1) = Finsupp.weight w e0 := by
    have h1 := congrArg (Finsupp.weight w) hadd
    rw [map_add, hsw, hwpos _ hpos0, add_zero] at h1
    exact h1
  obtain ⟨γ, hγ, hγw⟩ := exists_mem_support_mul_weight_eq_of_weight_zero w _ M.det (g i0) hD0 hD hg _ hγ0 hwγ0
  rw [hdet] at hγ
  have h1 := hRHS γ hγ
  omega

theorem supp_gen_neg {N : ℕ} (pos : κ → Bool) (ρ : Fin N → κ) (hρ : ∀ c, pos c = false ↔ ∃ i, ρ i = c)
    (hρi : Function.Injective ρ) (u : Fin N → κ → σ) (v : κ → σ)
    (hu : Function.Injective (fun x : Fin N × Fin N => u x.1 (ρ x.2)))
    (huv : ∀ j c c', u j c ≠ v c') (hv : Function.Injective v) (P : MvPolynomial σ ℂ) (hP : P ≠ 0)
    (hR : ∀ j, PI.FJMP.gR v (u j) pos P = 0) : ∃ e ∈ P.support, 0 ≤ PI.FJMP.sw e v pos := by
  have hR' : ∀ j, PI.FJMP.gR (u j) v (fun c => !pos c) P = 0 := by
    intro j
    have h := PI.FJMP.gR_swap (u j) v (fun c => !pos c) P
    simp only [Bool.not_not] at h
    rw [hR j] at h
    exact neg_eq_zero.mp h.symm
  obtain ⟨e, he, hsw⟩ := supp_gen_pos (fun c => !pos c) ρ
    (by intro c; rw [← hρ c]; simp) hρi u v hu huv hv P hP hR'
  refine ⟨e, he, ?_⟩
  have hneg : PI.FJMP.sw e v (fun c => !pos c) = - PI.FJMP.sw e v pos := by
    unfold PI.FJMP.sw
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rcases Bool.eq_false_or_eq_true (pos c) with hc | hc <;> simp [hc]
  omega

end Gen

section Col

variable {p q r s : ℕ} {ν : Ix r s → ℚ} {g : Pol p q r s}

theorem supp_lp {c d : Ix r s} (h : posC c d) (a : Ix p q) :
    linePos ((a, d) : Ln p q r s) = linePos ((a, c) : Ln p q r s) := by
  rcases c with c | c <;> rcases d with d | d <;> simp only [posC] at h <;> rcases a with a | a <;> rfl

theorem supp_gR (hg : IsHW (fockAct2 p q r s) ν g) {c d : Ix r s} (h : posC c d) :
    PI.FJMP.gR (fun a : Ix p q => ((a, c) : Ln p q r s)) (fun a => (a, d))
      (fun a => linePos ((a, c) : Ln p q r s)) g = 0 := by
  have hg' : g ≠ 0 ∧ g ∈ hwSub (fockAct2 p q r s) ν := hg
  have hcd : c ≠ d := PI.FJMP.ne_of_posC h
  have h0 := PI.FJMP.ker_of_hw hg'.2 c d h
  rw [PI.WFJM.fockAct2_Eab] at h0
  rw [← PI.FJMP.rightRootOperator_eq_signedPolarization c d hcd (fun a => supp_lp h a) g]
  have e : (∑ a : Ix p q, omE ((a, c) : Ln p q r s) (a, d)) = PI.FJM.rai2 c d := by
    unfold PI.FJM.rai2
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold omE
    rw [if_neg (fun hh => hcd (Prod.ext_iff.mp hh).2), add_zero]
  rw [← e]
  exact h0

theorem supp_col_pos (hg : IsHW (fockAct2 p q r s) ν g) {N : ℕ} (d : Ix r s) (ρ : Fin N → Ix p q)
    (hρ : ∀ a, linePos ((a, d) : Ln p q r s) = true ↔ ∃ i, ρ i = a) (hρi : Function.Injective ρ)
    (κ : Fin N → Ix r s) (hκ : Function.Injective κ) (hκd : ∀ j, posC (κ j) d) :
    shiftNu (cPair p q) ν d ≤ 0 := by
  have hg' : g ≠ 0 ∧ g ∈ hwSub (fockAct2 p q r s) ν := hg
  obtain ⟨e, he, hsw⟩ := supp_gen_pos (fun a : Ix p q => linePos ((a, d) : Ln p q r s)) ρ hρ hρi
    (fun j a => ((a, κ j) : Ln p q r s)) (fun a => ((a, d) : Ln p q r s))
    (by
      rintro ⟨j1, i1⟩ ⟨j2, i2⟩ h
      simp only [Prod.mk.injEq] at h
      rw [hρi h.1, hκ h.2])
    (fun j c c' h => PI.FJMP.ne_of_posC (hκd j) (congrArg Prod.snd h))
    (fun a b h => congrArg Prod.fst h) g hg'.1
    (by
      intro j
      have h := supp_gR hg (hκd j)
      have hl : (fun a : Ix p q => linePos ((a, κ j) : Ln p q r s))
          = fun a => linePos ((a, d) : Ln p q r s) := by
        funext a
        exact (supp_lp (hκd j) a).symm
      rw [hl] at h
      exact h)
  have hw := PI.FJMP.monomialRightWeight_eq_weight_sub PI.FJM.rightDiagonalActionFormula hg'.2 e he d
  have hs : PI.FJMP.sw e (fun a => ((a, d) : Ln p q r s)) (fun a => linePos ((a, d) : Ln p q r s))
      = PI.FJM.wt2 e d := rfl
  rw [hs] at hsw
  have hq : (PI.FJM.wt2 e d : ℚ) ≤ 0 := by exact_mod_cast hsw
  rw [hw] at hq
  exact hq

theorem supp_col_neg (hg : IsHW (fockAct2 p q r s) ν g) {N : ℕ} (d : Ix r s) (ρ : Fin N → Ix p q)
    (hρ : ∀ a, linePos ((a, d) : Ln p q r s) = false ↔ ∃ i, ρ i = a) (hρi : Function.Injective ρ)
    (κ : Fin N → Ix r s) (hκ : Function.Injective κ) (hκd : ∀ j, posC d (κ j)) :
    0 ≤ shiftNu (cPair p q) ν d := by
  have hg' : g ≠ 0 ∧ g ∈ hwSub (fockAct2 p q r s) ν := hg
  obtain ⟨e, he, hsw⟩ := supp_gen_neg (fun a : Ix p q => linePos ((a, d) : Ln p q r s)) ρ hρ hρi
    (fun j a => ((a, κ j) : Ln p q r s)) (fun a => ((a, d) : Ln p q r s))
    (by
      rintro ⟨j1, i1⟩ ⟨j2, i2⟩ h
      simp only [Prod.mk.injEq] at h
      rw [hρi h.1, hκ h.2])
    (fun j c c' h => PI.FJMP.ne_of_posC (hκd j) (congrArg Prod.snd h).symm)
    (fun a b h => congrArg Prod.fst h) g hg'.1
    (fun j => supp_gR hg (hκd j))
  have hw := PI.FJMP.monomialRightWeight_eq_weight_sub PI.FJM.rightDiagonalActionFormula hg'.2 e he d
  have hs : PI.FJMP.sw e (fun a => ((a, d) : Ln p q r s)) (fun a => linePos ((a, d) : Ln p q r s))
      = PI.FJM.wt2 e d := rfl
  rw [hs] at hsw
  have hq : (0 : ℚ) ≤ (PI.FJM.wt2 e d : ℚ) := by exact_mod_cast hsw
  rw [hw] at hq
  exact hq

end Col

theorem supp2 {p q r s : ℕ} {ν : Ix r s → ℚ} {g : Pol p q r s} (hg : IsHW (fockAct2 p q r s) ν g) :
    Supp p q ν := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    exact supp_col_pos hg (Sum.inl k) (Sum.inl : Fin p → Ix p q)
      (by intro a; cases a <;> simp [linePos]) Sum.inl_injective
      (fun j => (Sum.inl ⟨j, by have := j.isLt; have := k.isLt; omega⟩ : Ix r s))
      (by intro j1 j2 h; simp only [Sum.inl.injEq, Fin.mk.injEq] at h; exact Fin.ext h)
      (by intro j; simp only [posC, Fin.lt_iff_val_lt_val]; have := j.isLt; omega)
  · intro l hl
    exact supp_col_pos hg (Sum.inr l) (Sum.inr : Fin q → Ix p q)
      (by intro a; cases a <;> simp [linePos]) Sum.inr_injective
      (fun j => (Sum.inr ⟨j, by have := j.isLt; have := l.isLt; omega⟩ : Ix r s))
      (by intro j1 j2 h; simp only [Sum.inr.injEq, Fin.mk.injEq] at h; exact Fin.ext h)
      (by intro j; simp only [posC, Fin.lt_iff_val_lt_val]; have := j.isLt; omega)
  · intro k hk
    exact supp_col_neg hg (Sum.inl k) (Sum.inr : Fin q → Ix p q)
      (by intro a; cases a <;> simp [linePos]) Sum.inr_injective
      (fun j => (Sum.inl ⟨k + 1 + j, by have := j.isLt; omega⟩ : Ix r s))
      (by intro j1 j2 h; simp only [Sum.inl.injEq, Fin.mk.injEq] at h; exact Fin.ext (by omega))
      (by intro j; simp only [posC, Fin.lt_iff_val_lt_val]; omega)
  · intro l hl
    exact supp_col_neg hg (Sum.inr l) (Sum.inl : Fin p → Ix p q)
      (by intro a; cases a <;> simp [linePos]) Sum.inl_injective
      (fun j => (Sum.inr ⟨l + 1 + j, by have := j.isLt; omega⟩ : Ix r s))
      (by intro j1 j2 h; simp only [Sum.inr.injEq, Fin.mk.injEq] at h; exact Fin.ext (by omega))
      (by intro j; simp only [posC, Fin.lt_iff_val_lt_val]; omega)

end PositivityTheory.KReal

end
