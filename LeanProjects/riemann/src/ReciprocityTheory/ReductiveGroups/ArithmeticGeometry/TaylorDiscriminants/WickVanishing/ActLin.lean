import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpLaw

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

def ActLinSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O)
    (ℓ ε : Pt k 1 d), (∀ i, constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
    comp1 ℓ (B.G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
    IsInvPair ε ℓ → ∀ (a : O) (i : Fin d),
      comp1 ℓ (comp1 (B.A.act a) ε) i = ∑ j, C (dLin (B.A.act a) i j) * X ((0 : Fin 1), j)

namespace WickVanishing

variable {k : Type} [CommRing k] [Algebra ℚ k]

theorem hom_at {d : ℕ} {O : Type} [CommRing O] (G : FGLaw k d) (A : OAct O G) (a : O) {n : ℕ}
    (u v : Pt k n d) (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    comp1 (A.act a) (addOf G.F u v) = addOf G.F (comp1 (A.act a) u) (comp1 (A.act a) v) := by
  have huv : ∀ j i, constantCoeff ((![u, v] : Fin 2 → Pt k n d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact hu i
    · exact hv i
  have hpt : ∀ (m : ℕ) (j : Fin m) (i : Fin d), constantCoeff (pt k (n := m) d j i) = 0 := fun m j i =>
    MvPowerSeries.constantCoeff_X _
  have hp01 : ∀ j i, constantCoeff ((![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j <;> exact hpt _ _ _
  have hp0 : ∀ j i, constantCoeff ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact hpt _ _ _
  have hp1 : ∀ j i, constantCoeff ((![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact hpt _ _ _
  have hadd01 : ∀ j i, constantCoeff ((![addOf G.F (pt k (n := 2) d 0) (pt k (n := 2) d 1)] :
      Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact cc_ev _ hp01 (G.const i)
  have hc01 : ∀ j i, constantCoeff ((![comp1 (A.act a) (pt k (n := 2) d 0), comp1 (A.act a) (pt k (n := 2) d 1)] :
      Fin 2 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_ev _ hp0 (A.const a i)
    · exact cc_ev _ hp1 (A.const a i)
  have hev2 : ∀ (j : Fin 2) (l : Fin d), ev (![u, v] : Fin 2 → Pt k n d)
      ((![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) j l) = (![u, v] : Fin 2 → Pt k n d) j l := by
    intro j l
    fin_cases j
    · exact ev_X _ huv 0 l
    · exact ev_X _ huv 1 l
  funext i
  have h := congrArg (ev (![u, v] : Fin 2 → Pt k n d)) (congrFun (A.hom a) i)
  simp only [comp1, FGLaw.add, addOf] at h ⊢
  rw [ev_ev _ _ hadd01 huv, ev_ev _ _ hc01 huv] at h
  convert h using 2
  · funext j l
    fin_cases j
    simp only [addOf, Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
    rw [ev_ev _ _ hp01 huv]
    congr 1
    funext j' l'
    exact (hev2 j' l').symm
  · funext j l
    fin_cases j
    · simp only [comp1, Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
      rw [ev_ev _ _ hp0 huv]
      congr 1
      funext j' l'
      fin_cases j'
      exact (ev_X _ huv 0 l').symm
    · simp only [comp1, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Fin.mk_one, Fin.isValue]
      rw [ev_ev _ _ hp1 huv]
      congr 1
      funext j' l'
      fin_cases j'
      exact (ev_X _ huv 1 l').symm

theorem dLin_pt {d : ℕ} : dLin (pt k (n := 1) d 0) = 1 := by
  ext i j
  simp only [dLin, pt, Matrix.one_apply, MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg, if_neg h]
    intro h2
    apply h
    have h3 := (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h2
    exact (Prod.mk.inj h3).2.symm

open Formalism.FG.SolveVAux in
theorem action_linear : ActLinSt := by
  have single_of_degree : ∀ {σ : Type} (n : σ →₀ ℕ), n.degree = 1 → ∃ p, n = Finsupp.single p 1 := by
    intro σ n h
    classical
    have hc : Multiset.card (Finsupp.toMultiset n) = 1 := by
      rw [Finsupp.card_toMultiset, ← h]
      rfl
    obtain ⟨p, hp⟩ := Multiset.card_eq_one.mp hc
    refine ⟨p, ?_⟩
    have h2 := congrArg Multiset.toFinsupp hp
    rw [Finsupp.toMultiset_toFinsupp, Multiset.toFinsupp_singleton] at h2
    exact h2
  intro k _ _ d O _ _ B ℓ ε hℓ0 hℓ1 hadd hinv a i
  obtain ⟨hε0, -, hεℓ, hℓε⟩ := hinv
  have hA0 : ∀ i, constantCoeff (B.A.act a i) = 0 := B.A.const a
  have hcc1 : ∀ {n : ℕ} (φ : Pt k 1 d) (w : Pt k n d), (∀ i, constantCoeff (φ i) = 0) →
      (∀ i, constantCoeff (w i) = 0) → ∀ i, constantCoeff (comp1 φ w i) = 0 := fun φ w hφ hw i =>
    cc_ev _ (fun j l => by fin_cases j; exact hw l) (hφ i)
  have hccA : ∀ {n : ℕ} (u v : Pt k n d), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (addOf B.G.F u v i) = 0 := fun u v hu hv i =>
    cc_ev _ (fun j l => by
      fin_cases j
      · exact hu l
      · exact hv l) (B.G.const i)
  have hpt : ∀ {n : ℕ} (w : Pt k n d), (∀ i, constantCoeff (w i) = 0) → comp1 (pt k (n := 1) d 0) w = w := by
    intro n w hw
    funext i
    exact ev_X _ (fun j l => by fin_cases j; exact hw l) 0 i
  have hx : ∀ i, constantCoeff (pt k (n := 2) d 0 i) = 0 := fun i => MvPowerSeries.constantCoeff_X _
  have hy : ∀ i, constantCoeff (pt k (n := 2) d 1 i) = 0 := fun i => MvPowerSeries.constantCoeff_X _
  have hxy : ∀ i, constantCoeff ((pt k (n := 2) d 0 + pt k (n := 2) d 1) i) = 0 := fun i => by
    simp [pt]
  have hεx := hcc1 ε _ hε0 hx
  have hεy := hcc1 ε _ hε0 hy
  have hAε : ∀ i, constantCoeff (comp1 (B.A.act a) ε i) = 0 := hcc1 _ _ hA0 hε0
  have S1 : comp1 ℓ (addOf B.G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1))) =
      pt k (n := 2) d 0 + pt k (n := 2) d 1 := by
    rw [add_at B.G ℓ hadd _ _ hεx hεy, germComp1_germComp1_eq_substitute ℓ ε _ hε0 hx, germComp1_germComp1_eq_substitute ℓ ε _ hε0 hy, hℓε, hpt _ hx, hpt _ hy]
  have S2 : comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      addOf B.G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) := by
    rw [← S1, germComp1_germComp1_eq_substitute ε ℓ _ hℓ0 (hccA _ _ hεx hεy), hεℓ, hpt _ (hccA _ _ hεx hεy)]
  have S4 : comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1))) =
      comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 0))) +
        comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 1))) := by
    rw [S2, hom_at B.G B.A a _ _ hεx hεy, add_at B.G ℓ hadd _ _ (hcc1 _ _ hA0 hεx) (hcc1 _ _ hA0 hεy)]
  have hF : ∀ w : Pt k 2 d, (∀ i, constantCoeff (w i) = 0) →
      comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) w = comp1 ℓ (comp1 (B.A.act a) (comp1 ε w)) := by
    intro w hw
    rw [← germComp1_germComp1_eq_substitute _ _ _ hAε hw, ← germComp1_germComp1_eq_substitute _ _ _ hε0 hw]
  have hfadd : comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 0) +
        comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 1) := by
    rw [hF _ hxy, hF _ hx, hF _ hy]
    exact S4
  have hlin := addition_linear k d (comp1 ℓ (comp1 (B.A.act a) ε) i) (congrFun hfadd i)
  have hdε : dLin ε = 1 := by
    have h := dLin_comp1 ε ℓ hℓ0
    rw [hεℓ, dLin_pt, hℓ1, mul_one] at h
    exact h.symm
  have hdf : dLin (comp1 ℓ (comp1 (B.A.act a) ε)) = dLin (B.A.act a) := by
    rw [dLin_comp1 ℓ _ hAε, dLin_comp1 _ ε hε0, hℓ1, hdε, one_mul, mul_one]
  ext n
  rw [map_sum]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  by_cases hn : n.degree = 1
  · obtain ⟨p, rfl⟩ := single_of_degree n hn
    obtain ⟨z, j0⟩ := p
    obtain rfl : z = 0 := Subsingleton.elim _ _
    have h1 : MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j0) 1) (comp1 ℓ (comp1 (B.A.act a) ε) i) =
        dLin (B.A.act a) i j0 := by
      rw [← hdf]
      rfl
    rw [h1, Finset.sum_eq_single j0]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      apply hj
      have h2 := (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h
      exact (Prod.mk.inj h2).2.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [hlin n hn]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg, mul_zero]
    rintro rfl
    exact hn (Finsupp.degree_single _ _)

end WickVanishing

end ReciprocityTheory.ChartRestriction.G.TB
