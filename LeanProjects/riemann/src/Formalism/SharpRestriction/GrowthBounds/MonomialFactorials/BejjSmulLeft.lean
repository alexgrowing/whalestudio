import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PlusAWICondition
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestPlusOf

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Gen

variable (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]

theorem gc_bdd_gen (be : V → V → ℚ_[p]) (hsm : ∀ (c : ℚ_[p]) u v, be (c • u) v = c * be u v)
    (hsum : ∀ (n : ℕ) (s : Finset (Fin n)) (f : Fin n → V) v, be (∑ i ∈ s, f i) v = ∑ i ∈ s, be (f i) v)
    (L : Submodule ℤ_[p] V) (W : Submodule ℚ_[p] V) [FiniteDimensional ℚ_[p] W] (hLW : ∀ x ∈ L, x ∈ W) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → V, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i k, be (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  refine ⟨Module.finrank ℚ_[p] W, ?_⟩
  rintro n ⟨x, y, hx, hy, hxy⟩
  have hpD : (p : ℚ_[p]) ^ D ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hz : ∀ v, be 0 v = 0 := by
    intro v
    simpa using hsm 0 0 v

  let x' : Fin n → W := fun i => ⟨x i, hLW _ (hx i)⟩
  have hli : LinearIndependent ℚ_[p] x' := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hg' : ∑ j ∈ s, g j • x j = 0 := by
      have := congrArg Subtype.val hg
      simpa [x'] using this
    have h1 := congrArg (fun u => be u (y i)) hg'
    rw [hsum n s (fun j => g j • x j) (y i), hz] at h1
    simp only [hsm, hxy] at h1
    rw [Finset.sum_eq_single i] at h1
    · simpa [hpD] using h1
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd hi h
  simpa using hli.fintype_card_le_finrank

theorem bad_le_sub (be : V → V → ℚ_[p]) (L L₁ : Submodule ℤ_[p] V) (hle : L₁ ≤ L) (D : ℤ) (n₁ : ℕ)
    (hn : Module.finrank ℤ_[p] L₁ = n₁)
    (hb : BddAbove {n | ∃ x y : Fin n → V, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i k, be (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0}) :
    Formalism.GM.M.bad p be L D ≤ (Module.finrank ℤ_[p] L - n₁) + Formalism.GM.M.bad p be L₁ D := by
  have hgc : Formalism.GM.M.goodCount p be L₁ D ≤ Formalism.GM.M.goodCount p be L D := by
    unfold Formalism.GM.M.goodCount
    apply csSup_le_csSup hb
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    · rintro n ⟨x, y, hx, hy, h⟩
      exact ⟨x, y, fun i => hle (hx i), fun i => hle (hy i), h⟩
  unfold Formalism.GM.M.bad
  rw [hn]
  omega

end Gen

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

private theorem fockK_eq_lemma {k σ : Type} [Field k] (F G : MvPolynomial σ k) (s : Finset (σ →₀ ℕ))
    (hs : F.support ⊆ s) :
    Formalism.GM.M.fockK F G = ∑ m ∈ s, F.coeff m * G.coeff m * (m.prod fun _ j => (j.factorial : k)) := by
  unfold Formalism.GM.M.fockK
  apply Finset.sum_subset hs
  intro m _ hm
  have h0 : F.coeff m = 0 := by simpa using hm
  rw [h0, zero_mul, zero_mul]

theorem bejj_smul_left (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bejj p (r := r) G j jp (c • u) v = c * bejj p (r := r) G j jp u v := by
  unfold bejj
  rw [map_smul, fockK_eq_lemma _ v _ MvPolynomial.support_smul]
  unfold Formalism.GM.M.fockK
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem bejj_sum_left (j : Fin G.T.t → ℕ) (jp : ℕ) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) (v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bejj p (r := r) G j jp (∑ i ∈ s, f i) v = ∑ i ∈ s, bejj p (r := r) G j jp (f i) v := by
  classical
  unfold bejj
  rw [map_sum, ← Finset.sum_div]
  congr 1
  set S := (∑ i ∈ s, G.phiAll p (r := r) j jp (f i)).support ∪
    s.biUnion (fun i => (G.phiAll p (r := r) j jp (f i)).support) with hS
  rw [fockK_eq_lemma _ v S Finset.subset_union_left]
  rw [Finset.sum_congr rfl (fun i hi => fockK_eq_lemma (G.phiAll p (r := r) j jp (f i)) v S
    ((Finset.subset_biUnion_of_mem (fun i => (G.phiAll p (r := r) j jp (f i)).support) hi).trans
      Finset.subset_union_right))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_sum, Finset.sum_mul, Finset.sum_mul]

theorem bejj_bdd (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G j jp) ∧ (∀ i, y i ∈ Ljj p (r := r) G j jp) ∧
      ∀ i k, bejj p (r := r) G j jp (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  obtain ⟨W, hW, hLW⟩ := exists_fd_Ljj p (r := r) G j jp
  haveI := hW
  exact gc_bdd_gen p (bejj p (r := r) G j jp) (bejj_smul_left p G j jp)
    (fun n s f v => bejj_sum_left p G j jp s f v) (Ljj p (r := r) G j jp) W hLW D

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestOrth (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∃ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      (∀ a, e a ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ∧ LinearIndependent ℤ_[X.p] e ∧
      (∀ a b, a ≠ b → bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e b) = 0) ∧
      (∀ a, bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a) ≠ 0 ∧
        (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a)).valuation ≤
          ⌊D1r C0 CE1 CE2 X CM⌋) ∧
      n₁ ≤ Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ∧
      Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ≤
        n₁ + Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
          (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋

def RestWin (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∀ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      (∀ a, e a ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) → LinearIndependent ℤ_[X.p] e →
      (∀ a b, a ≠ b → bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e b) = 0) →
      (∀ a, bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a) ≠ 0 ∧
        (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a)).valuation ≤
          ⌊D1r C0 CE1 CE2 X CM⌋) →
      (∑ aPlus ∈ X.winA, (Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
          (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ)) ≤
        (X.winA.card : ℝ) * (5 / X.L.Y * n₁)

variable {C0 CE1 CE2 X}

theorem restPlusB_of (CM : ℝ) (hY : 0 < X.L.Y) (hO : RestOrth C0 CE1 CE2 X CM) (hW : RestWin C0 CE1 CE2 X CM) :
    RestPlusB C0 CE1 CE2 X CM := by
  intro dl hdl aTop haTop x hx
  obtain ⟨n₁, e, he, hli, horth, hval, hn1, hrk⟩ := hO dl hdl aTop haTop x hx
  have hwin := hW dl hdl aTop haTop x hx n₁ e he hli horth hval
  have hspan : Submodule.span ℤ_[X.p] (Set.range e) ≤
      Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 :=
    Submodule.span_le.2 (by
      rintro _ ⟨a, rfl⟩
      exact he a)
  have hrank : Module.finrank ℤ_[X.p] (Submodule.span ℤ_[X.p] (Set.range e)) = n₁ := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hstep : ∀ aPlus ∈ X.winA, (bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) ≤
      ((Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁ : ℕ) : ℝ) +
        (Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
          (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    intro aPlus _
    have h := bad_le_sub X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
      (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
      (Submodule.span ℤ_[X.p] (Set.range e)) hspan ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ n₁ hrank
      (bejj_bdd X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2 _)
    have h' : bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ ≤
        (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁) +
          Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
            (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ := h
    exact_mod_cast h'
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h1 : ((Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁ : ℕ) : ℝ) ≤
      (Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
        (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    exact_mod_cast (by omega)
  have hc : (0 : ℝ) ≤ 5 / X.L.Y := div_nonneg (by norm_num) hY.le
  have h2 : 5 / X.L.Y * (n₁ : ℝ) ≤ 5 / X.L.Y *
      (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hn1) hc
  have hcard : (0 : ℝ) ≤ (X.winA.card : ℝ) := Nat.cast_nonneg _
  have h3 := mul_le_mul_of_nonneg_left h1 hcard
  have h4 := mul_le_mul_of_nonneg_left h2 hcard
  nlinarith [hwin, h3, h4]

end Formalism.MainNotions.G.SymmetricFormBlocks

end
