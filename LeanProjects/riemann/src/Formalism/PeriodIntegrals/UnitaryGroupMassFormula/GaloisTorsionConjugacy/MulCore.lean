import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.MulMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeierstrassUniformization.PairIsLat

noncomputable section

namespace PI.GalTorsConj.W

open PI.GalTorsConj Formalism.L2.Th1.F

section core

variable {L L' : PeriodPair} {M₁ : IntermediateField ℚ ℂ} {ρ₁ : M₁ →ₐ[ℚ] ℂ}

theorem conj_velu_isogeny (hg2 : L.g₂ ∈ M₁) (hg2' : L'.g₂ = ρ₁ ⟨_, hg2⟩) {S : Finset ℂ} {f : ℂ → ℂ}
    (hf : ∀ P ∈ S, St L L' M₁ ρ₁ P (f P)) (hinj : Set.InjOn f S)
    (hSL : ∀ P ∈ S, P ∉ L.lattice) {z z' : ℂ} (hz : St L L' M₁ ρ₁ z z')
    (hU : z ∈ veluU L S) :
    Cj1 M₁ ρ₁ (veluF L S z) (veluF L' (S.image f) z') ∧
      Cj1 M₁ ρ₁ (veluD L S z) (veluD L' (S.image f) z') := by
  have hzP : ∀ P ∈ S, St L L' M₁ ρ₁ (z + P) (z' + f P) := fun P hP =>
    st_add addLaw dblLaw hg2 hg2' hz (hf P hP)
  have e0 := conj_weierstrassP hz hU.1
  have eP : ∀ P ∈ S, Cj1 M₁ ρ₁ (L.weierstrassP (z + P)) (L'.weierstrassP (z' + f P)) ∧
      Cj1 M₁ ρ₁ (L.derivWeierstrassP (z + P)) (L'.derivWeierstrassP (z' + f P)) :=
    fun P hP => conj_weierstrassP (hzP P hP) (hU.2 P hP)
  have eQ : ∀ P ∈ S, Cj1 M₁ ρ₁ (L.weierstrassP P) (L'.weierstrassP (f P)) :=
    fun P hP => (conj_weierstrassP (hf P hP) (hSL P hP)).1
  unfold veluF veluD
  rw [Finset.sum_image hinj, Finset.sum_image hinj]
  exact ⟨conj_add_alt e0.1 (conj_sum_alt S _ _ fun P hP => conj_sub_alt (eP P hP).1 (eQ P hP)),
    conj_add_alt e0.2 (conj_sum_alt S _ _ fun P hP => (eP P hP).2)⟩

theorem core (hD : IsogD) (hO : IsogODE) (hDn : TorsDense)
    (hg2 : L.g₂ ∈ M₁) (hg3 : L.g₃ ∈ M₁) (hg2' : L'.g₂ = ρ₁ ⟨_, hg2⟩) (hg3' : L'.g₃ = ρ₁ ⟨_, hg3⟩)
    (htors : ∀ (n : ℕ) (t : ℂ), 0 < n → (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      L.weierstrassP t ∈ M₁ ∧ L.derivWeierstrassP t ∈ M₁)
    {c : ℂ} (hc0 : c ≠ 0) (hcL : MulStable L c) (hc : c ∈ M₁) (hρc : ρ₁ ⟨c, hc⟩ = c)
    {t t' : ℂ} (h : St L L' M₁ ρ₁ t t') : St L L' M₁ ρ₁ (c * t) (c * t') := by
  obtain ⟨S, hS⟩ := kerRepsExist L c hc0 hcL
  have hSL : ∀ P ∈ S, P ∉ L.lattice := fun P hP => (hS.1 P hP).2
  have hex : ∀ P ∈ S, ∃ P', St L L' M₁ ρ₁ P P' := by
    intro P hP
    obtain ⟨m, hm, hmP⟩ := tors_of_ker hc0 hcL (hS.1 P hP).1
    exact st_exists pOnto hg2 hg3 hg2' hg3' P (Or.inr (htors m P hm hmP (hSL P hP)))
  choose! f hf using hex
  have hinj : Set.InjOn f S := by
    intro P hP Q hQ e
    have h2 : St L L' M₁ ρ₁ Q (f P) := by rw [e]; exact hf Q hQ
    exact hS.2.1 P hP Q hQ (st_inj (hf P hP) h2)
  have hS'L : ∀ P' ∈ S.image f, P' ∉ L'.lattice := by
    intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hP'
    exact fun h' => hSL P hP ((st_mem_iff (hf P hP)).2 h')
  have hS'd : ∀ P' ∈ S.image f, ∀ Q' ∈ S.image f, P' - Q' ∈ L'.lattice → P' = Q' := by
    intro P' hP' Q' hQ' hd
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hP'
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hQ'
    have h2 : St L L' M₁ ρ₁ Q (f P) := by
      have := st_add_right (hf Q hQ) hd
      rwa [show f Q + (f P - f Q) = f P by ring] at this
    rw [hS.2.1 P hP Q hQ (st_inj (hf P hP) h2)]
  have cc : Cj1 M₁ ρ₁ c c := ⟨hc, hρc⟩
  have cg2 : Cj1 M₁ ρ₁ L.g₂ L'.g₂ := ⟨hg2, hg2'.symm⟩
  have cg3 : Cj1 M₁ ρ₁ L.g₃ L'.g₃ := ⟨hg3, hg3'.symm⟩

  have hodeT : ∀ z' ∈ veluU L' (S.image f) ∩
      {t : ℂ | ∃ n : ℕ, 0 < n ∧ (n : ℂ) * t ∈ L'.lattice},
      veluD L' (S.image f) z' ^ 2 = 4 * veluF L' (S.image f) z' ^ 3
        - c ^ 4 * L'.g₂ * veluF L' (S.image f) z' - c ^ 6 * L'.g₃ := by
    rintro z' ⟨hU', n, hn, hnz'⟩
    obtain ⟨z, -, hz⟩ := st_onto addLaw dblLaw pOnto hg2 hg3 hg2' hg3' n hn
      (fun t h1 h2 => htors n t hn h1 h2) z' hnz'
    have hzL : z ∉ L.lattice := fun h' => hU'.1 ((st_mem_iff hz).1 h')
    have hzP : ∀ P ∈ S, z + P ∉ L.lattice := fun P hP h' =>
      hU'.2 (f P) (Finset.mem_image_of_mem f hP)
        ((st_mem_iff (st_add addLaw dblLaw hg2 hg2' hz (hf P hP))).1 h')
    have hU : z ∈ veluU L S := ⟨hzL, hzP⟩
    have hcz := mul_notMem hS hzL hzP
    have eF : veluF L S z = c ^ 2 * L.weierstrassP (c * z) := (isogenyP L c S hc0 hcL hS z hcz).symm
    have eD : veluD L S z = c ^ 3 * L.derivWeierstrassP (c * z) := (hD L c S hc0 hcL hS z hcz).symm
    have curve := L.derivWeierstrassP_sq (c * z) hcz
    have ode : veluD L S z ^ 2 =
        4 * veluF L S z ^ 3 - c ^ 4 * L.g₂ * veluF L S z - c ^ 6 * L.g₃ := by
      rw [eF, eD]
      linear_combination c ^ 6 * curve
    obtain ⟨cF, cD⟩ := conj_velu_isogeny hg2 hg2' hf hinj hSL hz hU
    have lhs := conj_pow_alt cD 2
    have rhs := conj_sub_alt (conj_sub_alt (conj_mul_alt (conj_natCast_alt 4) (conj_pow_alt cF 3))
      (conj_mul_alt (conj_mul_alt (conj_pow_alt cc 4) cg2) cF)) (conj_mul_alt (conj_pow_alt cc 6) cg3)
    have e := conj_eq_alt lhs rhs (by rw [ode]; push_cast; ring)
    rw [e]
    push_cast
    ring

  have hode : ∀ z' ∈ veluU L' (S.image f), veluD L' (S.image f) z' ^ 2 =
      4 * veluF L' (S.image f) z' ^ 3 - c ^ 4 * L'.g₂ * veluF L' (S.image f) z' - c ^ 6 * L'.g₃ := by
    have hF := continuousOn_veluF L' (S.image f)
    have hDc := continuousOn_veluD L' (S.image f)
    have hcont1 : ContinuousOn (fun z => veluD L' (S.image f) z ^ 2) (veluU L' (S.image f)) :=
      hDc.pow 2
    have hcont2 : ContinuousOn (fun z => 4 * veluF L' (S.image f) z ^ 3
        - c ^ 4 * L'.g₂ * veluF L' (S.image f) z - c ^ 6 * L'.g₃) (veluU L' (S.image f)) :=
      ((continuousOn_const.mul (hF.pow 3)).sub (continuousOn_const.mul hF)).sub continuousOn_const
    have heq := Set.EqOn.of_subset_closure (fun z hz => hodeT z hz) hcont1 hcont2
      Set.inter_subset_left ((hDn L').open_subset_closure_inter (isOpen_veluU L' (S.image f)))
    exact fun z hz => heq hz
  obtain ⟨hcL', hcS', hU'⟩ := hO L' c (S.image f) hc0 hS'L hS'd hode
  by_cases ht : t ∈ L.lattice
  · exact Or.inl ⟨hcL t ht, hcL' t' ((st_mem_iff h).1 ht)⟩
  by_cases hct : c * t ∈ L.lattice
  · obtain ⟨Q, hQ, htQ⟩ := hS.2.2 t hct ht
    have h2 : St L L' M₁ ρ₁ t (f Q) := by
      have := st_add_left (hf Q hQ) htQ
      rwa [show Q + (t - Q) = t by ring] at this
    have d := st_unique h h2
    refine Or.inl ⟨hct, ?_⟩
    have := L'.lattice.add_mem (hcL' _ d) (hcS' (f Q) (Finset.mem_image_of_mem f hQ))
    rwa [show c * (t' - f Q) + c * f Q = c * t' by ring] at this
  have htP : ∀ P ∈ S, t + P ∉ L.lattice := by
    intro P hP h'
    apply hct
    have := L.lattice.sub_mem (hcL _ h') (hS.1 P hP).1
    rwa [show c * (t + P) - c * P = c * t by ring] at this
  have hU : t ∈ veluU L S := ⟨ht, htP⟩
  have ht' : t' ∉ L'.lattice := fun h' => ht ((st_mem_iff h).2 h')
  have hU'' : t' ∈ veluU L' (S.image f) := by
    refine ⟨ht', fun P' hP' h' => ?_⟩
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hP'
    exact htP P hP ((st_mem_iff (st_add addLaw dblLaw hg2 hg2' h (hf P hP))).2 h')
  obtain ⟨cF, cD⟩ := conj_velu_isogeny hg2 hg2' hf hinj hSL h hU
  obtain ⟨hct', eF', eD'⟩ := hU' t' hU''
  have eF : veluF L S t = c ^ 2 * L.weierstrassP (c * t) := (isogenyP L c S hc0 hcL hS t hct).symm
  have eD : veluD L S t = c ^ 3 * L.derivWeierstrassP (c * t) := (hD L c S hc0 hcL hS t hct).symm
  have cinv : Cj1 M₁ ρ₁ c⁻¹ c⁻¹ := by
    refine ⟨M₁.inv_mem hc, ?_⟩
    have e : ((⟨c, hc⟩ : M₁)⁻¹) = ⟨c⁻¹, M₁.inv_mem hc⟩ := rfl
    rw [← e, map_inv₀, hρc]
  have qX : Cj1 M₁ ρ₁ (L.weierstrassP (c * t)) (L'.weierstrassP (c * t')) := by
    have p := conj_mul_alt (conj_pow_alt cinv 2) cF
    have e1 : c⁻¹ ^ 2 * veluF L S t = L.weierstrassP (c * t) := by rw [eF]; field_simp
    have e2 : c⁻¹ ^ 2 * veluF L' (S.image f) t' = L'.weierstrassP (c * t') := by
      rw [← eF']; field_simp
    rwa [e1, e2] at p
  have qY : Cj1 M₁ ρ₁ (L.derivWeierstrassP (c * t)) (L'.derivWeierstrassP (c * t')) := by
    have p := conj_mul_alt (conj_pow_alt cinv 3) cD
    have e1 : c⁻¹ ^ 3 * veluD L S t = L.derivWeierstrassP (c * t) := by rw [eD]; field_simp
    have e2 : c⁻¹ ^ 3 * veluD L' (S.image f) t' = L'.derivWeierstrassP (c * t') := by
      rw [← eD']; field_simp
    rwa [e1, e2] at p
  obtain ⟨hx, vx⟩ := qX
  obtain ⟨hy, vy⟩ := qY
  exact Or.inr ⟨hct, hct', hx, hy, vx.symm, vy.symm⟩

end core

end PI.GalTorsConj.W

end
