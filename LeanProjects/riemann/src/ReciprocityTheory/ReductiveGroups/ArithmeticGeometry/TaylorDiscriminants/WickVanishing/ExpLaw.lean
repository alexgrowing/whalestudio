import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcAdd
import ReciprocityTheory.ReductiveGroups.Models.FiniteGeneration.FiniteGenerationProofs.SolveV
import ReciprocityTheory.ReductiveGroups.Models.FiniteGeneration.FiniteGenerationProofs.Imports

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

variable {k : Type} [CommRing k] [Algebra ℚ k]

def ExpLawSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ : Pt k 1 d), (∀ i, constantCoeff (ℓ i) = 0) →
    dLin ℓ = 1 →
    comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) = comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
    ∃ ε : Pt k 1 d, IsInvPair ε ℓ ∧ transF G.F ε ℓ = pt k (n := 2) d 0 + pt k (n := 2) d 1

theorem idMod2_of {d : ℕ} (ℓ : Pt k 1 d) (h0 : ∀ i, constantCoeff (ℓ i) = 0) (h1 : dLin ℓ = 1) :
    Formalism.FG.IsIdMod2 (fun p : Fin 1 × Fin d => ℓ p.2) := by
  refine ⟨fun p => h0 p.2, fun j i => ?_⟩
  obtain ⟨j1, j2⟩ := j
  obtain ⟨i1, i2⟩ := i
  have hj : j1 = 0 := Subsingleton.elim _ _
  have hi : i1 = 0 := Subsingleton.elim _ _
  subst hj hi
  have := congrFun (congrFun h1 j2) i2
  simp only [dLin, Matrix.one_apply] at this
  simp only [this, Prod.mk.injEq, true_and]
  by_cases h : i2 = j2
  · simp [h]
  · simp [h, Ne.symm h]

theorem subst_single_point_family {d : ℕ} {τ : Type} (ε : Fin d → MvPowerSeries τ k) :
    (fun p : Fin 1 × Fin d => (![ε] : Fin 1 → Fin d → MvPowerSeries τ k) p.1 p.2) = fun p => ε p.2 := by
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

theorem cc_ev {n m d : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j i, constantCoeff (a j i) = 0) {f : PS k m d}
    (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 := by
  unfold ev
  exact constantCoeff_subst_eq_zero (hasSubst_pts a ha) (fun p => ha p.1 p.2) hf

theorem cc_pt {n d : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt k d j i) = 0 := by simp [pt]

theorem cc_comp1 {n d : ℕ} (φ : Pt k 1 d) (a : Pt k n d) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) : constantCoeff (comp1 φ a i) = 0 :=
  cc_ev _ (fun j i => by fin_cases j; exact ha i) (hφ i)

theorem germComp1_germComp1_eq_substitute {n d : ℕ} (φ ψ : Pt k 1 d) (a : Pt k n d) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (ha : ∀ i, constantCoeff (a i) = 0) : comp1 φ (comp1 ψ a) = comp1 (comp1 φ ψ) a := by
  funext i
  unfold comp1
  rw [ev_ev (![ψ] : Fin 1 → Pt k 1 d) (![a] : Fin 1 → Pt k n d) (fun j i => by fin_cases j; exact hψ i)
    (fun j i => by fin_cases j; exact ha i)]
  congr 1
  funext j
  fin_cases j
  rfl

theorem germCompOne_identityPoint_left {n d : ℕ} (a : Pt k n d) (ha : ∀ i, constantCoeff (a i) = 0) : comp1 (pt k d 0) a = a := by
  funext i
  unfold comp1
  exact ev_X (![a] : Fin 1 → Pt k n d) (fun j i => by fin_cases j; exact ha i) 0 i

theorem formal_exp_law : ExpLawSt := by
  intro k _ _ d G ℓ h0 h1 hadd
  have hid := idMod2_of ℓ h0 h1
  obtain ⟨h, hh0, hh⟩ := Formalism.FG.solve_exists_vector k (Fin 1 × Fin d) (Fin 1 × Fin d) (fun p => ℓ p.2) X hid
    (fun j => by simp)
  let ε : Pt k 1 d := fun i => h (0, i)
  have hε0 : ∀ i, constantCoeff (ε i) = 0 := fun i => hh0 (0, i)
  have hhε : h = fun p => ε p.2 := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j
    rfl
  have hLε : comp1 ℓ ε = pt k d 0 := by
    funext i
    show ev ![ε] (ℓ i) = X (0, i)
    unfold ev
    rw [subst_single_point_family, ← hhε]
    exact hh (0, i)
  have hsL : HasSubst (fun p : Fin 1 × Fin d => ℓ p.2) := hasSubst_of_constantCoeff_zero fun p => h0 p.2
  have hsh : HasSubst h := hasSubst_of_constantCoeff_zero hh0
  have hinj := Formalism.FG.subst_injective_vector k (Fin 1 × Fin d) (Fin 1 × Fin d) (fun p => ℓ p.2)
    (fun p => subst (fun q : Fin 1 × Fin d => ℓ q.2) (h p)) X hid
    (fun p => constantCoeff_subst_eq_zero hsL (fun q => h0 q.2) (hh0 p)) (fun p => by simp) (fun j => by
      rw [← subst_comp_subst_apply hsh hsL, hh j, subst_X hsL, subst_self]
      rfl)
  have hεL : comp1 ε ℓ = pt k d 0 := by
    funext i
    show ev ![ℓ] (ε i) = X (0, i)
    unfold ev
    rw [subst_single_point_family]
    exact congrFun hinj (0, i)
  refine ⟨ε, ⟨hε0, h0, hεL, hLε⟩, ?_⟩
  funext i
  have e : ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (ℓ i) =
      ev (n := 2) ![pt k d 0] (ℓ i) + ev (n := 2) ![pt k d 1] (ℓ i) := congrFun hadd i
  let b : Fin 2 → Pt k 2 d := ![comp1 ε (pt k d 0), comp1 ε (pt k d 1)]
  have hb : ∀ j i, constantCoeff (b j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_comp1 ε _ hε0 (cc_pt 0) i
    · exact cc_comp1 ε _ hε0 (cc_pt 1) i
  have hadd0 : ∀ j i, constantCoeff ((![G.add (pt k d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact cc_ev _ (fun j i => by fin_cases j <;> exact cc_pt _ i) (G.const i)
  have hp0 : ∀ (l : Fin 2) j i, constantCoeff ((![pt k d l] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro l j i
    fin_cases j
    exact cc_pt l i
  have e2 := congrArg (ev b) e
  rw [ev_ev _ _ hadd0 hb, ev_add' _ hb, ev_ev _ _ (hp0 0) hb, ev_ev _ _ (hp0 1) hb] at e2
  have L1 : (fun (j : Fin 1) (m : Fin d) => ev b ((![G.add (pt k d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) j m)) =
      ![addOf G.F (comp1 ε (pt k d 0)) (comp1 ε (pt k d 1))] := by
    funext j m
    fin_cases j
    show ev b (ev ![pt k d 0, pt k d 1] (G.F m)) = ev b (G.F m)
    rw [ev_ev _ _ (fun j i => by fin_cases j <;> exact cc_pt _ i) hb]
    congr 1
    funext j' m'
    fin_cases j' <;> exact ev_X b hb _ m'
  have L2 : ∀ l : Fin 2, (fun (j : Fin 1) (m : Fin d) => ev b ((![pt k d l] : Fin 1 → Pt k 2 d) j m)) =
      ![comp1 ε (pt k d l)] := by
    intro l
    funext j m
    fin_cases j
    fin_cases l <;> exact ev_X b hb _ m
  have L3 : ∀ l : Fin 2, ev (n := 2) ![comp1 ε (pt k d l)] (ℓ i) = pt k d l i := by
    intro l
    have := congrFun (germComp1_germComp1_eq_substitute ℓ ε (pt k (n := 2) d l) hε0 (cc_pt l)) i
    rw [hLε, germCompOne_identityPoint_left _ (cc_pt l)] at this
    exact this
  rw [L1, L2 0, L2 1, L3 0, L3 1] at e2
  exact e2

open Formalism.FG.SolveVAux in

theorem dLin_comp1 {d : ℕ} (φ ψ : Pt k 1 d) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    dLin (comp1 φ ψ) = dLin φ * dLin ψ := by
  classical
  refine Matrix.ext fun i j => ?_
  simp only [dLin, Matrix.mul_apply]
  show coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![ψ] (φ i)) = _
  unfold ev
  rw [subst_single_point_family]
  have hs : HasSubst (fun p : Fin 1 × Fin d => ψ p.2) := hasSubst_of_constantCoeff_zero fun p => hψ p.2
  have hlow : ∀ p : Fin 1 × Fin d, Low 1 (ψ p.2) := fun p => (low_one_iff _).2 (hψ p.2)
  rw [coeff_subst hs, finsum_eq_sum_of_support_subset _
    (s := Finset.univ.image (fun p : Fin 1 × Fin d => Finsupp.single p 1))]
  · rw [Finset.sum_image (fun p _ q _ h => Finsupp.single_left_injective one_ne_zero h), Fintype.sum_prod_type,
      Fin.sum_univ_one]
    refine Finset.sum_congr rfl fun j' _ => ?_
    dsimp only
    rw [Finsupp.prod_single_index (h := fun (s : Fin 1 × Fin d) (e : ℕ) => ψ s.2 ^ e) (pow_zero _), pow_one,
      smul_eq_mul]
  · intro e he
    rw [Function.mem_support] at he
    by_contra hne
    apply he
    have hz : coeff (Finsupp.single ((0 : Fin 1), j) 1) (e.prod fun s n => (fun p : Fin 1 × Fin d => ψ p.2) s ^ n) =
        0 := by
      rcases Nat.lt_or_ge e.degree 2 with hd | hd
      · rcases Nat.lt_or_ge e.degree 1 with hd1 | hd1
        · have he0 : e = 0 := by
            have : e.degree = 0 := by omega
            exact (Finsupp.degree_eq_zero_iff e).1 this
          rw [he0, Finsupp.prod_zero_index, coeff_one, if_neg]
          exact Finsupp.single_ne_zero.2 one_ne_zero
        · obtain ⟨p, rfl⟩ := degree_eq_one e (by omega)
          exact absurd (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ p))) hne
      · have hl := low_P hlow e
        exact hl _ (by rw [Finsupp.degree_single]; omega)
    rw [hz, smul_zero]

theorem composition_identity_point_right {d : ℕ} (φ : Pt k 1 d) : comp1 φ (pt k d 0) = φ := by
  funext i
  unfold comp1
  have := ev_pt (k := k) (n := 1) (d := d) (φ i)
  convert this using 2
  funext j
  fin_cases j
  rfl

theorem add_at {d : ℕ} (G : FGLaw k d) (ℓ : Pt k 1 d)
    (hadd : comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1))
    {n : ℕ} (u v : Pt k n d) (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    comp1 ℓ (addOf G.F u v) = comp1 ℓ u + comp1 ℓ v := by
  funext i
  have e : ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (ℓ i) =
      ev (n := 2) ![pt k d 0] (ℓ i) + ev (n := 2) ![pt k d 1] (ℓ i) := congrFun hadd i
  let b : Fin 2 → Pt k n d := ![u, v]
  have hb : ∀ j i, constantCoeff (b j i) = 0 := by
    intro j i
    fin_cases j
    · exact hu i
    · exact hv i
  have hadd0 : ∀ j i, constantCoeff ((![G.add (pt k d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact cc_ev _ (fun j i => by fin_cases j <;> exact cc_pt _ i) (G.const i)
  have hp0 : ∀ (l : Fin 2) j i, constantCoeff ((![pt k d l] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro l j i
    fin_cases j
    exact cc_pt l i
  have e2 := congrArg (ev b) e
  rw [ev_ev _ _ hadd0 hb, ev_add' _ hb, ev_ev _ _ (hp0 0) hb, ev_ev _ _ (hp0 1) hb] at e2
  have L1 : (fun (j : Fin 1) (m : Fin d) => ev b ((![G.add (pt k d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) j m)) =
      ![addOf G.F u v] := by
    funext j m
    fin_cases j
    show ev b (ev ![pt k d 0, pt k d 1] (G.F m)) = ev b (G.F m)
    rw [ev_ev _ _ (fun j i => by fin_cases j <;> exact cc_pt _ i) hb]
    congr 1
    funext j' m'
    fin_cases j' <;> exact ev_X b hb _ m'
  have L2 : (fun (j : Fin 1) (m : Fin d) => ev b ((![pt k d 0] : Fin 1 → Pt k 2 d) j m)) = ![u] := by
    funext j m
    fin_cases j
    exact ev_X b hb 0 m
  have L3 : (fun (j : Fin 1) (m : Fin d) => ev b ((![pt k d 1] : Fin 1 → Pt k 2 d) j m)) = ![v] := by
    funext j m
    fin_cases j
    exact ev_X b hb 1 m
  rw [L1, L2, L3] at e2
  exact e2

def LogUniqueSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ ℓ' : Pt k 1 d),
    (∀ i, constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
    comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) = comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
    (∀ i, constantCoeff (ℓ' i) = 0) → dLin ℓ' = 1 →
    comp1 ℓ' (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ' (pt k (n := 2) d 0) + comp1 ℓ' (pt k (n := 2) d 1) → ℓ = ℓ'

open Formalism.FG.SolveVAux in
theorem formal_log_unique : LogUniqueSt := by
  intro k _ _ d G ℓ ℓ' h0 h1 hadd h0' h1' hadd'
  classical
  obtain ⟨ε, ⟨hε0, -, hεL, hLε⟩, htr⟩ := formal_exp_law k d G ℓ h0 h1 hadd
  have hp2 : ∀ (l : Fin 2) (i : Fin d), constantCoeff (pt k (n := 2) d l i) = 0 := fun l i => cc_pt l i
  have hsum0 : ∀ i, constantCoeff ((pt k (n := 2) d 0 + pt k (n := 2) d 1) i) = 0 := fun i => by simp [pt]
  have hεp : ∀ (l : Fin 2) i, constantCoeff (comp1 ε (pt k (n := 2) d l) i) = 0 := fun l i =>
    cc_comp1 ε _ hε0 (hp2 l) i

  have hA : addOf G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) =
      comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1) := by
    have hAc : ∀ i, constantCoeff (addOf G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) i) = 0 :=
      fun i => cc_ev _ (fun j i => by fin_cases j <;> exact hεp _ i) (G.const i)
    have e : comp1 ℓ (addOf G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1))) =
        pt k (n := 2) d 0 + pt k (n := 2) d 1 := htr
    have e2 := congrArg (comp1 ε) e
    rw [germComp1_germComp1_eq_substitute ε ℓ _ h0 hAc, hεL, germCompOne_identityPoint_left _ hAc] at e2
    exact e2
  set δ := comp1 ℓ' ε with hδ
  have hδ0 : ∀ i, constantCoeff (δ i) = 0 := fun i => cc_comp1 ℓ' ε h0' hε0 i
  have hδadd : comp1 δ (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      comp1 δ (pt k (n := 2) d 0) + comp1 δ (pt k (n := 2) d 1) := by
    rw [hδ, ← germComp1_germComp1_eq_substitute ℓ' ε _ hε0 hsum0, ← germComp1_germComp1_eq_substitute ℓ' ε _ hε0 (hp2 0), ← germComp1_germComp1_eq_substitute ℓ' ε _ hε0 (hp2 1), ← hA]
    exact add_at G ℓ' hadd' _ _ (hεp 0) (hεp 1)
  have hdε : dLin ε = 1 := by
    have := dLin_comp1 ℓ ε hε0
    rw [hLε, h1, _root_.one_mul] at this
    rw [← this]
    refine Matrix.ext fun i j => ?_
    simp only [dLin, pt, Matrix.one_apply, coeff_X, Finsupp.single_left_inj one_ne_zero, Prod.mk.injEq, true_and]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hdδ : dLin δ = 1 := by rw [hδ, dLin_comp1 ℓ' ε hε0, h1', hdε, _root_.one_mul]
  have hδid : δ = pt k d 0 := by
    funext i
    ext e
    rcases eq_or_ne e.degree 1 with he | he
    · obtain ⟨⟨j0, j⟩, rfl⟩ := degree_eq_one e he
      have hj0 : j0 = 0 := Subsingleton.elim _ _
      subst hj0
      have := congrFun (congrFun hdδ i) j
      simp only [dLin, Matrix.one_apply] at this
      rw [this]
      simp only [pt, coeff_X, Finsupp.single_left_inj one_ne_zero, Prod.mk.injEq, true_and]
      by_cases h : i = j
      · simp [h]
      · simp [h, Ne.symm h]
    · rw [addition_linear k d (δ i) (congrFun hδadd i) e he]
      simp only [pt, coeff_X]
      rw [if_neg]
      rintro rfl
      exact he (Finsupp.degree_single _ _)
  calc ℓ = comp1 (pt k d 0) ℓ := (germCompOne_identityPoint_left ℓ h0).symm
    _ = comp1 (comp1 ℓ' ε) ℓ := by rw [← hδ, hδid]
    _ = comp1 ℓ' (comp1 ε ℓ) := (germComp1_germComp1_eq_substitute ℓ' ε ℓ hε0 h0).symm
    _ = ℓ' := by rw [hεL, composition_identity_point_right]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
