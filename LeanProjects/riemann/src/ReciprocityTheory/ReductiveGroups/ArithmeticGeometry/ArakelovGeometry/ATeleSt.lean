import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

noncomputable def ratioLine (m₀ m₁ : ConeMetric ℂ (Ix κ)) : HermLine (GlobalTheory κ) where
  a := 0
  h z := m₁.ρ z / m₀.ρ z
  pos z hz := by
    have hz0 : z ≠ 0 := fun h0 => by
      obtain ⟨i, hi⟩ := hz ()
      exact hi (congrFun h0 _)
    exact div_pos (m₁.pos z hz0) (m₀.pos z hz0)
  smul c z hc := by
    have : (fun p : Ix κ => c p.1 * z p) = c () • z := by
      funext p
      rfl
    have hc0 : ‖c ()‖ ≠ 0 := norm_ne_zero_iff.mpr (hc ())
    rw [this, m₀.smul, m₁.smul, mul_div_mul_left _ _ hc0]
    simp

theorem tele_ptsIntegral_neg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ (fun z => - g z) = - ptsIntegral P φ g := by
  have hsd : ∀ (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> ring
  unfold ptsIntegral
  split_ifs with h
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_neg]
    congr 1
    funext y
    simp_rw [hsd]
    rw [finsum_mem_def, finsum_mem_def, ← finsum_neg_distrib]
    congr 1
    funext w
    by_cases hw : w ∈ fibre P h.choose y <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hw]
  · simp

theorem tele_one_homog {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] :
    IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
  classical
  intro m hm k
  have h0 : m = 0 := by
    by_contra hne
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hm
    exact hm rfl
  subst h0
  simp

theorem tele_divSupp_one {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) : divSupp P 1 = ∅ := by
  ext W
  simp only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hW, -⟩
  have h1 := hW.1
  rw [Ideal.span_singleton_one, sup_top_eq] at h1
  exact h1.1.ne_top (top_le_iff.1 h1.2)

theorem fam_degZero (I : AllFam) (hI : I.IsFamily) {P : Ideal (MRing (GlobalTheory κ))} {n : ℕ}
    (hP : IsArithVar P (n + 1)) (L : Fin n → HermLine (GlobalTheory κ)) (hL : ∀ j, IsSmoothHerm (L j))
    (B : HermLine (GlobalTheory κ)) (hB : IsSmoothHerm B) (hB0 : B.a = 0) :
    I Unit (GlobalTheory κ) P (n + 1) (Fin.snoc L B) = ptsIntegral P (pot L) fun z => Real.log (B.h z) := by
  obtain ⟨-, -, h3⟩ := hI Unit (GlobalTheory κ)
  have hP1 : (1 : MRing (GlobalTheory κ)) ∉ P := by
    intro h1
    have htop : P = ⊤ := (Ideal.eq_top_iff_one P).2 h1
    have h4 := hP.2.2.2
    rw [htop] at h4
    haveI : Subsingleton (MRing (GlobalTheory κ) ⧸ (⊤ : Ideal (MRing (GlobalTheory κ)))) :=
      Ideal.Quotient.subsingleton_iff.2 rfl
    rw [ringKrullDim_eq_bot_of_subsingleton] at h4
    exact WithBot.bot_ne_coe h4
  rw [h3 P n L B 1 0 hP hL hB (fun k => by rw [hB0]; simp) tele_one_homog hP1]
  unfold recR
  rw [tele_divSupp_one, finsum_mem_empty, zero_sub]
  unfold arInt
  have hln : logNorm B 1 = fun z => -Real.log (B.h z) := by
    funext z
    simp [logNorm, Real.log_inv]
  rw [hln, tele_ptsIntegral_neg, neg_neg]
  rfl

theorem tele_herm_ext {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  obtain ⟨a, h, _, _⟩ := A
  obtain ⟨a', h', _, _⟩ := B
  simp only at ha hh
  subst ha
  subst hh
  rfl

theorem tele_rho_zero (m : ConeMetric ℂ (Ix κ)) : m.ρ 0 = 0 := by
  have h := m.smul 0 0
  simpa using h

theorem tele_ofCone_tensor (m₀ m₁ : ConeMetric ℂ (Ix κ)) :
    HermLine.ofCone m₁ = (HermLine.ofCone m₀).tensor (ratioLine m₀ m₁) := by
  apply tele_herm_ext
  · show (1 : Unit → ℤ) = 1 + 0
    simp
  · funext z
    show m₁.ρ z = m₀.ρ z * (m₁.ρ z / m₀.ρ z)
    by_cases hz : z = 0
    · subst hz
      rw [tele_rho_zero, tele_rho_zero]
      simp
    · rw [mul_div_cancel₀ _ (m₀.pos z hz).ne']

theorem tele_smooth_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  show ContDiffOn ℝ _ m.ρ _
  refine hm.mono fun z hz h0 => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact hi (congrFun h0 _)

theorem tele_smooth_ratio {m₀ m₁ : ConeMetric ℂ (Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) : IsSmoothHerm (ratioLine m₀ m₁) := by
  have hsub : {z : Ix κ → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ⊆ {z | z ≠ 0} := by
    intro z hz h0
    obtain ⟨i, hi⟩ := hz ()
    exact hi (congrFun h0 _)
  show ContDiffOn ℝ _ (fun z => m₁.ρ z / m₀.ρ z) _
  exact (h₁.mono hsub).div (h₀.mono hsub) fun z hz => (m₀.pos z (hsub hz)).ne'

def tele_perm {n : ℕ} (i : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv' i).symm

theorem tele_comp_perm {α : Type*} {n : ℕ} (F : Fin (n + 1) → α) (i : Fin (n + 1)) :
    F ∘ tele_perm i = Fin.snoc (F ∘ i.succAbove) (F i) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [tele_perm]
  · simp [tele_perm]

def tele_fam (m₀ m₁ : ConeMetric ℂ (Ix κ)) (N i : ℕ) : Fin N → HermLine (GlobalTheory κ) :=
  fun j => if j.val < i then HermLine.ofCone m₁ else HermLine.ofCone m₀

theorem tele_fam_succAbove (m₀ m₁ : ConeMetric ℂ (Ix κ)) (D i : ℕ) (hi : i < D + 1) (k : ℕ)
    (hk : k = i ∨ k = i + 1) :
    tele_fam m₀ m₁ (D + 1) k ∘ (⟨i, hi⟩ : Fin (D + 1)).succAbove = tele_fam m₀ m₁ D i := by
  funext j
  simp only [Function.comp, tele_fam]
  have hv : (Fin.succAbove (⟨i, hi⟩ : Fin (D + 1)) j).val = if j.val < i then j.val else j.val + 1 := by
    unfold Fin.succAbove
    split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def] <;> omega
  rw [hv]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem tele_fam_smooth {m₀ m₁ : ConeMetric ℂ (Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) (N i : ℕ) (j : Fin N) : IsSmoothHerm (tele_fam m₀ m₁ N i j) := by
  unfold tele_fam
  split_ifs
  · exact tele_smooth_ofCone h₁
  · exact tele_smooth_ofCone h₀

theorem top_sub_top (I : AllFam) (hI : I.IsFamily) {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    {μ : Measure (Ix κ → ℂ)} (hg₀ : IsGood D x m₀ μ) (hg₁ : IsGood D x m₁ μ) :
    top I x m₁ D - top I x m₀ D = ∑ i ∈ Finset.range (D + 1),
      ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ x) (mixPot m₀ m₁ D i) (logRatio m₀ m₁) := by
  have h₀ : IsSmoothMetric m₀ := hg₀.semipos.1
  have h₁ : IsSmoothMetric m₁ := hg₁.semipos.1
  have hP := hg₀.arith
  obtain ⟨hperm, hadd, -⟩ := hI Unit (GlobalTheory κ)
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ, F = fun i => I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i) :=
    ⟨_, rfl⟩
  have hF0 : F 0 = top I x m₀ D := by
    rw [hF, top]
    show I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) 0) = _
    congr 1
    try (funext j; simp [tele_fam])
  have hFD : F (D + 1) = top I x m₁ D := by
    rw [hF, top]
    show I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) (D + 1)) = _
    congr 1
    try (funext j; simp [tele_fam, j.isLt])
  have hstep : ∀ i ∈ Finset.range (D + 1), F (i + 1) - F i =
      ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ x) (mixPot m₀ m₁ D i) (logRatio m₀ m₁) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsm : ∀ k j, IsSmoothHerm (tele_fam m₀ m₁ (D + 1) k j) := tele_fam_smooth h₀ h₁ (D + 1)
    have hσ : ∀ k, F k = I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (tele_fam m₀ m₁ (D + 1) k ∘ tele_perm ⟨i, hi⟩) := by
      intro k
      rw [hF]
      exact (hperm _ _ _ _ hP (hsm k)).symm
    rw [hσ (i + 1), hσ i, tele_comp_perm, tele_comp_perm,
      tele_fam_succAbove m₀ m₁ D i hi (i + 1) (Or.inr rfl), tele_fam_succAbove m₀ m₁ D i hi i (Or.inl rfl)]
    have e1 : tele_fam m₀ m₁ (D + 1) (i + 1) ⟨i, hi⟩ = HermLine.ofCone m₁ := by simp [tele_fam]
    have e2 : tele_fam m₀ m₁ (D + 1) i ⟨i, hi⟩ = HermLine.ofCone m₀ := by simp [tele_fam]
    rw [e1, e2, tele_ofCone_tensor m₀ m₁, hadd _ _ _ _ _ hP (tele_fam_smooth h₀ h₁ D i)
      (tele_smooth_ofCone h₀) (tele_smooth_ratio h₀ h₁), add_sub_cancel_left,
      fam_degZero I hI hP (tele_fam m₀ m₁ D i) (tele_fam_smooth h₀ h₁ D i) (ratioLine m₀ m₁)
        (tele_smooth_ratio h₀ h₁) rfl]
    congr 1
    all_goals first
      | rfl
      | (funext j z
         simp only [pot, mixPot, tele_fam]
         split_ifs <;> rfl)
  rw [← hFD, ← hF0, ← Finset.sum_range_sub F (D + 1)]
  exact Finset.sum_congr rfl hstep

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
