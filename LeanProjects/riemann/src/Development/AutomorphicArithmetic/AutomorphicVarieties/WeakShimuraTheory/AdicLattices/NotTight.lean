import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

namespace UpperTheory.V.Ws.Lat

private theorem col0 {R : Type} [CommRing R] (n X : M4 R) (hn : IsLow n) (hu : IsUp (adj n * X * n)) (i : Fin 4) :
    X i 0 + X i 1 * n 1 0 + X i 2 * n 2 0 + X i 3 * n 3 0 = n i 0 * (adj n * X * n) 0 0 := by
  have h1 : adj n * n = 1 := by
    have := hn.1
    unfold IsGSp at this
    rwa [one_smul] at this
  have h2 : n * adj n = 1 := mul_eq_one_comm.1 h1
  have h3 : X * n = n * (adj n * X * n) := by
    rw [← mul_assoc, ← mul_assoc, h2, one_mul]
  have h4 := congrFun (congrFun h3 i) 0
  rw [Matrix.mul_apply, Matrix.mul_apply (M := n), Fin.sum_univ_four, Fin.sum_univ_four, hu 1 0 (by decide),
    hu 2 0 (by decide), hu 3 0 (by decide), hn.2.1 0] at h4
  linear_combination h4

private theorem notTight {ι Γ R : Type} [Group Γ] [CommRing R] {P : PD ι Γ R} {w : ℤ × ℤ} (hw : w ∈ roots)
    (h : w ∉ Tight P) : (∀ g i j, wt i j = w → P.r g i j = 0) ∧ ∀ v, nCo (P.n v) w = 0 := by
  simp only [Tight, Set.mem_setOf_eq, not_and, Ent, not_or, not_exists, not_not] at h
  obtain ⟨h1, h2⟩ := h hw
  refine ⟨fun g i j hij => ?_, h2⟩
  by_contra hne
  simp_all

private theorem nCo_al {R : Type} [CommRing R] (X : M4 R) : nCo X (-wAl) = X 1 0 := by
  simp [nCo]

private theorem nCo_th {R : Type} [CommRing R] (X : M4 R) : nCo X (-wTh) = X 3 0 := by
  simp [nCo, wAl, wBe, wPs, wTh]

private theorem wt_th : ∀ i j : Fin 4, wt i j = -wTh → i = 3 ∧ j = 0 := by decide

private theorem wt_al : ∀ i j : Fin 4, wt i j = -wAl → (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2) := by decide

end UpperTheory.V.Ws.Lat

private theorem entry_one_zero_eq_zero_of_nCo_neg_wAl_eq_zero {R : Type} [CommRing R] {X : M4 R} (h : nCo X (-wAl) = 0) : X 1 0 = 0 := by
  rwa [nCo_al] at h

theorem UpperTheory.V.Ws.Lat.noNeg :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k) (P : PD Φ.ι Γ k), PreRes Φ a P → EntVan Φ a P →
      (-wAl ∉ Tight P → -wTh ∉ Tight P) ∧ (wBe ∉ Tight P → wPs ∉ Tight P → -wAl ∉ Tight P) := by
  intro O Γ _ _ _ Φ k _ a P hP hE
  have col : ∀ v, ∀ s ∈ Φ.Gv v, ∀ i, P.r s i 0 + P.r s i 1 * P.n v 1 0 + P.r s i 2 * P.n v 2 0
      + P.r s i 3 * P.n v 3 0 = P.n v i 0 * a ↑((Φ.χ 0) s) := by
    intro v s hs i
    rw [col0 (P.n v) (P.r s) (hP.pair.low v) (hP.pair.flag v s hs) i]
    congr 1
    exact hP.char v s hs 0
  constructor
  · intro hA
    obtain ⟨hAr, hAn⟩ := notTight (by decide) hA
    have r10 : ∀ g, P.r g 1 0 = 0 := fun g => hAr g 1 0 (by decide)
    have r32 : ∀ g, P.r g 3 2 = 0 := fun g => hAr g 3 2 (by decide)
    have n10 : ∀ v, P.n v 1 0 = 0 := fun v => entry_one_zero_eq_zero_of_nCo_neg_wAl_eq_zero (hAn v)
    obtain ⟨hr30, hm⟩ := hE 3 0 (by decide) (by
        intro g h x hx3 hx0
        fin_cases x <;> simp [r10, r32] at hx0 hx3 ⊢) (fun v => P.n v 3 0) (by
        intro v s hs
        have c := col v s hs 3
        rw [n10 v, r32 s, hP.diag s 3] at c
        linear_combination c)
    intro hmem
    obtain ⟨-, hEnt | ⟨v, hv⟩⟩ := hmem
    · obtain ⟨g, i, j, hij, hne⟩ := hEnt
      obtain ⟨rfl, rfl⟩ := wt_th i j hij
      exact hne (hr30 g)
    · rw [nCo_th] at hv
      exact hv (congrFun hm v)
  · intro hB hPs
    obtain ⟨hBr, -⟩ := notTight (by decide) hB
    obtain ⟨hPr, -⟩ := notTight (by decide) hPs
    have r12 : ∀ g, P.r g 1 2 = 0 := fun g => hBr g 1 2 (by decide)
    have r13 : ∀ g, P.r g 1 3 = 0 := fun g => hPr g 1 3 (by decide)
    obtain ⟨hr10, hm⟩ := hE 1 0 (by decide) (by
        intro g h x hx1 hx0
        fin_cases x <;> simp [r12, r13] at hx0 hx1 ⊢) (fun v => P.n v 1 0) (by
        intro v s hs
        have c := col v s hs 1
        rw [r12 s, r13 s, hP.diag s 1] at c
        linear_combination c)
    have hr32 : ∀ g, P.r g 3 2 = 0 := by
      intro g
      obtain ⟨-, -, -, -, -, -, hinv, -⟩ := grp k
      have e := hinv _ (P.r g) (P.r g⁻¹) (hP.pair.mult g) (by rw [← map_mul, mul_inv_cancel, map_one])
      have e' := congrFun (congrFun e 1) 0
      rw [adj_apply] at e'
      simpa [sgn, Fin.rev, hr10] using e'
    intro hmem
    obtain ⟨-, hEnt | ⟨v, hv⟩⟩ := hmem
    · obtain ⟨g, i, j, hij, hne⟩ := hEnt
      rcases wt_al i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne (hr10 g)
      · exact hne (hr32 g)
    · rw [nCo_al] at hv
      exact hv (congrFun hm v)
