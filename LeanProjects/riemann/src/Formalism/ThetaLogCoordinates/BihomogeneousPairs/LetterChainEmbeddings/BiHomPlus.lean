import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.ChainEmbInj

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section lat2
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

theorem wv_ne_xi (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : wv D i c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [wv, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  have h1 := congrArg Fin.val h.1
  rw [finPos_pos_val hB, Fin.val_last] at h1
  have := pos_succ_lt hB i
  omega

theorem ev_ne_xi (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : ev D i c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [ev, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  have h1 := congrArg Fin.val h.1
  rw [finPos_succ_val hB, Fin.val_last] at h1
  have := pos_succ_lt hB i
  omega

theorem wU_ne_xi (c d : Fin r) : wU D c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [wU, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact (Fin.castSucc_lt_last _).ne h.1

theorem yz_pol {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ Pol p r LL :=
  (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).1).1

theorem yz_y {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ Y p (r := r) LL J M :=
  (Submodule.mem_inf.1 hy).1

theorem yz_int {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ IntPol p (Fin N × Fin r) :=
  (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).2).2

theorem yz_mk {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (h1 : y ∈ Y p (r := r) LL J M) (h2 : y ∈ IntPol p (Fin N × Fin r)) :
    y ∈ YZ p (r := r) LL J M :=
  Submodule.mem_inf.2 ⟨h1, Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 h1).1, h2⟩⟩

omit [NeZero r] in
theorem biHom_span {r' : ℕ} {w e : Fin r' → BVar N r D.T.t} {a b : ℕ} {S : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])}
    (h : ∀ x ∈ S, BiHom w e a b x) : ∀ x ∈ Submodule.span ℤ_[p] S, BiHom w e a b x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hxS => exact h x hxS
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h' | h'
    · exact hx m h'
    · exact hy m h'
  | smul a x _ hx =>
    intro m hm
    exact hx m (MvPolynomial.support_smul hm)

theorem biHom_tie (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    ∀ x ∈ Lat p D (r := r) j jp, BiHom (wv D i) (ev D i) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i)))
      ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1))) x := by
  intro x hx
  refine biHom_span (S := {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}) ?_ x hx
  rintro _ ⟨y, hy, g, hg, rfl⟩ m hm
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := supp_gen (p := p) (D := D) (hm := hm)
  have hdeg : MultiDeg (D.lettersAt j jp) m1 :=
    ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 (yz_pol hy)) hm1
  have hxi := (xi_supp (p := p) (D := D) (hg := hg) (hm2 := hm2))
  constructor
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (wv D i c) = m1 (D.letterAt (D.T.pos i), c) := fun c => by
      rw [wv_chain (hB := hB), Finsupp.mapDomain_apply (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (wv D i c) = 0 := fun c => hxi.1 _ (fun d => wv_ne_xi hB i c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (ev D i c) = m1 (D.letterAt (D.T.pos i + 1), c) := fun c => by
      rw [ev_chain (hB := hB), Finsupp.mapDomain_apply (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (ev D i c) = 0 := fun c => hxi.1 _ (fun d => ev_ne_xi hB i c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _

theorem biHom_plus (j : Fin D.T.t → ℕ) (jp : ℕ) :
    ∀ x ∈ Lat p D (r := r) j jp, BiHom (wU D) (xiVar N r D.T.t) ((D.lettersAt j jp).deg D.uPos) (D.B - jp) x := by
  intro x hx
  refine biHom_span (S := {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}) ?_ x hx
  rintro _ ⟨y, hy, g, hg, rfl⟩ m hm
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := supp_gen (p := p) (D := D) (hm := hm)
  have hdeg : MultiDeg (D.lettersAt j jp) m1 :=
    ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 (yz_pol hy)) hm1
  have hxi := (xi_supp (p := p) (D := D) (hg := hg) (hm2 := hm2))
  constructor
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (wU D c) = m1 (D.uPos, c) := fun c => by
      show Finsupp.mapDomain (chainEmb N r D.T.t) m1 (chainEmb N r D.T.t (D.uPos, c)) = _
      rw [Finsupp.mapDomain_apply (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (wU D c) = 0 := fun c => hxi.1 _ (fun d => wU_ne_xi c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (xiVar N r D.T.t c) = 0 := fun c =>
      Finsupp.mapDomain_notin_range _ _ (xi_notin (D := D) c)
    simp only [e1, Finset.sum_const_zero, zero_add]
    exact hxi.2

end lat2

end Formalism.InvariantFactorPaths.KP.LL
