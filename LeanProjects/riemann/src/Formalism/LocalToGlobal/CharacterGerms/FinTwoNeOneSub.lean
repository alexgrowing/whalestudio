import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipNormOne

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

theorem pderiv_comm' {σ R : Type} [CommRing R] (i j : σ) (p : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    simp only [MvPolynomial.pderiv_monomial]
    by_cases hij : i = j
    · subst hij
      rfl
    · congr 1
      · rw [tsub_right_comm]
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_neg hij, if_neg (Ne.symm hij),
          tsub_zero]
        ring
  | add p q hp hq => simp only [map_add, hp, hq]

section One

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem no_conj_of_rowsOK {G : ∀ g, Cart V d (I g) (J g)} {alt : Prop} {N : ℕ} {P : MvPolynomial (Fin N × WV I) C}
    {kind : Fin N → Knd d} (h : RowsOK G alt P kind) {ρ : Fin N} {w w' : WV I} (hw : (ρ, w) ∈ P.vars)
    (hw' : (ρ, w') ∈ P.vars) (hg : w.1 ≠ w'.1) (ht : tyW G w = tyW G w') : False := by
  obtain ⟨h1, h2⟩ := h
  rw [MvPolynomial.mem_vars] at hw hw'
  obtain ⟨μ, hμ, hμw⟩ := hw
  obtain ⟨μ', hμ', hμw'⟩ := hw'
  rcases hk : kind ρ with _ | ⟨g, a, a'⟩
  · obtain ⟨g, hg'⟩ := h2 ρ hk
    have e1 := hg' μ hμ w (Finsupp.mem_support_iff.1 hμw)
    have e2 := hg' μ' hμ' w' (Finsupp.mem_support_iff.1 hμw')
    exact hg (e1.trans e2.symm)
  · obtain ⟨-, hodd, hleaf⟩ := h1 ρ g a a' hk
    have l1 := hleaf μ hμ w (Finsupp.mem_support_iff.1 hμw)
    have l2 := hleaf μ' hμ' w' (Finsupp.mem_support_iff.1 hμw')
    rcases l1 with ⟨e1, t1⟩ | ⟨e1, t1⟩ <;> rcases l2 with ⟨e2, t2⟩ | ⟨e2, t2⟩
    · exact hg (e1.trans e2.symm)
    · have he : a = a' := t1.symm.trans (ht.trans t2)
      rw [he, sub_self, ZMod.val_zero] at hodd
      exact absurd hodd (by decide)
    · have he : a' = a := t1.symm.trans (ht.trans t2)
      rw [he, sub_self, ZMod.val_zero] at hodd
      exact absurd hodd (by decide)
    · exact hg (e1.trans e2.symm)

variable (X : RowData C V d I J) (F : Flag X)

theorem exists_rowsOK (hdich : X.Alt ∨ ∀ a, X.big 0 a) (hj : X.j' < X.n) (b : GlobalTheory d)
    (hwt : ∀ g a k, b.wt X g a k ≠ 0 → k ≤ X.rkF g a) :
    ∃ kind : Fin (b.what₂ X.n) → Knd d, RowsOK X.G X.Alt (b.poly X F) kind := by
  cases b with
  | ch g a u =>
    refine ⟨(GlobalTheory.ch g a u).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩⟩
    · intro ρ g' a1 a2 hk
      exact absurd hk (by simp [GlobalTheory.kind])
    · intro ρ _
      exact ⟨g, fun w hw => (vars_letter X F (MvPolynomial.vars_pow _ _ hw)).1⟩
  | mon g e N =>
    refine ⟨(GlobalTheory.mon g e N).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩⟩
    · intro ρ g' a1 a2 hk
      exact absurd hk (by simp [GlobalTheory.kind])
    · intro ρ _
      refine ⟨g, fun w hw => ?_⟩
      obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hw)
      exact (vars_letter X F ha).1
  | bi g a i y =>
    by_cases hy : y = 0
    · subst hy
      have hp : (GlobalTheory.bi g a i 0).poly X F = 1 := by
        simp [GlobalTheory.poly]
        rfl
      refine ⟨fun _ => none, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩⟩
      · intro ρ g' a1 a2 hk
        exact absurd hk (by simp)
      · intro ρ _
        refine ⟨0, fun w hw => ?_⟩
        rw [hp] at hw
        simp at hw
    · have hl : 0 < V.l ^ i * y := Nat.mul_pos (pow_pos V.l_prime.pos i) (Nat.pos_of_ne_zero hy)
      have w1 : X.n ≤ X.rkF g a := by
        apply hwt g a X.n
        simp only [GlobalTheory.wt, and_self, if_true]
        omega
      have w2 : X.n ≤ X.rkF (1 - g) (a + (i : ZMod d)) := by
        apply hwt (1 - g) (a + (i : ZMod d)) X.n
        simp only [GlobalTheory.wt, and_self, if_true]
        omega
      have hao := alt_odd_of_big X hdich (big_of_le_rk X hj w1) (big_of_le_rk X hj w2)
      refine ⟨(GlobalTheory.bi g a i y).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩⟩
      · intro ρ g' a1 a2 hk
        have hk' : (g, a, a + (i : ZMod d)) = (g', a1, a2) := by simpa [GlobalTheory.kind] using hk
        obtain ⟨rfl, rfl, rfl⟩ : g = g' ∧ a = a1 ∧ a + (i : ZMod d) = a2 := by simpa using hk'
        refine ⟨hao.1, hao.2, fun w hw => ?_⟩
        rcases Finset.mem_union.1 (MvPolynomial.vars_mul _ _ hw) with h1 | h1
        · exact Or.inl (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
        · exact Or.inr (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
      · intro ρ hk
        exact absurd hk (by simp [GlobalTheory.kind])

end One

section Fam

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n}

theorem ConjugatePairPlaceSetting.rowsOK (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) :
    ∃ kind : Fin n → Knd d, RowsOK (X o).G (X o).Alt
      (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)) kind := by
  have h : ∀ i : Fin (L o).length, ∃ kind : Fin (rowsAt X L o i) → Knd d,
      RowsOK (X o).G (X o).Alt ((blkAt L o i).poly (X o) (F o)) kind := by
    intro i
    by_cases ho : o ∈ Z
    · refine exists_rowsOK (X o) (F o) (H.dich o ho) (H.hj o ho) _ fun g t k hk => (H.supp o ho g t k ?_).2
      rw [← H.wt o ho g t k]
      have h : (blkAt L o i).wt (X o) g t k ≤ ((L o).map fun q => q.1.wt (X o) g t k).sum :=
        le_sum_map (L o) (fun q => q.1.wt (X o) g t k) (List.get_mem (L o) i)
      omega
    · have h0 : (L o).length = 0 := by rw [H.off o ho]; rfl
      exact absurd i.2 (by omega)
  choose kind hk using h
  exact ⟨_, rowsOK_prodAll _ _ (plAt_inj n H.plinj o) _ kind hk⟩

theorem mem_vars_blkProd {b : Fin n} {o : Orb} {w : WV (IIof r tau o)}
    (hx : ((b, ⟨o, w⟩) : Fin n × WVO (IIof r tau)) ∈ (blkProd X F n L pl).vars) :
    (b, w) ∈ (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)).vars := by
  unfold blkProd at hx
  have h1 := MvPolynomial.vars_prod _ hx
  rw [Finset.mem_biUnion] at h1
  obtain ⟨o', -, h2⟩ := h1
  unfold toAll at h2
  have h3 := MvPolynomial.vars_rename _ _ h2
  rw [Finset.mem_image] at h3
  obtain ⟨y, hy, hyeq⟩ := h3
  simp only [Prod.mk.injEq] at hyeq
  obtain ⟨hy1, hy2⟩ := hyeq
  have ho : o' = o := congrArg Sigma.fst hy2
  subst ho
  have hw : y.2 = w := eq_of_heq (Sigma.mk.inj_iff.1 hy2).2
  rw [show (b, w) = y from Prod.ext hy1.symm hw.symm]
  exact hy

theorem fin_two_ne_one_sub (g : Fin 2) : g ≠ 1 - g := by
  fin_cases g <;> decide

theorem ConjugatePairPlaceSetting.no_conj (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (b : Fin n) (o : Orb) (g : Fin 2) (t : ZMod d)
    (i : Fin (r (tau o g t))) (i' : Fin (r (tau o (1 - g) t)))
    (hx : ((b, ⟨o, ⟨g, ⟨t, i⟩⟩⟩) : Fin n × WVO (IIof r tau)) ∈ (blkProd X F n L pl).vars)
    (hx' : ((b, ⟨o, ⟨1 - g, ⟨t, i'⟩⟩⟩) : Fin n × WVO (IIof r tau)) ∈ (blkProd X F n L pl).vars) : False := by
  obtain ⟨kind, hk⟩ := H.rowsOK o
  refine no_conj_of_rowsOK hk (mem_vars_blkProd hx) (mem_vars_blkProd hx') (fin_two_ne_one_sub g) ?_
  show ((X o).G g).ty (Sum.inl ⟨t, i⟩) = ((X o).G (1 - g)).ty (Sum.inl ⟨t, i'⟩)
  rw [H.hty o g, H.hty o (1 - g)]

theorem ConjugatePairPlaceSetting.no_conj_letter (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (τ : T) (a1 : Fin (r τ)) (a2 : Fin (r (cc τ)))
    (b : Fin n)
    (h1 : (⟨τ, a1, b⟩ : Letter T r n) ∈ (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).vars)
    (h2 : (⟨cc τ, a2, b⟩ : Letter T r n) ∈ (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).vars) : False := by
  obtain ⟨x, hx, ex⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ h1)
  obtain ⟨x', hx', ex'⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ h2)
  obtain ⟨ρ, o, g, t, i⟩ := x
  obtain ⟨ρ', o', g', t', i'⟩ := x'
  have e1 : tau o g t = τ := congrArg Sigma.fst ex
  have e1' : tau o' g' t' = cc τ := congrArg Sigma.fst ex'
  have eρ : ρ = b := congrArg (fun ℓ : Letter T r n => ℓ.2.2) ex
  have eρ' : ρ' = b := congrArg (fun ℓ : Letter T r n => ℓ.2.2) ex'
  have e2 : tau o' g' t' = tau o (1 - g) t := by
    rw [e1', ← e1]
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · exact H.conj o t
    · exact H.conj' o t
  have e3 := H.inj (a₁ := (o', g', t')) (a₂ := (o, 1 - g, t)) e2
  simp only [Prod.mk.injEq] at e3
  obtain ⟨rfl, rfl, rfl⟩ := e3
  rw [eρ] at hx
  rw [eρ'] at hx'
  exact H.no_conj b o' g t' i i' hx hx'

end Fam

theorem lap_one_apply {T : Type} (r : T → ℕ) (n : ℕ) (C : Type) [Field C] (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ'))
    (P : MvPolynomial (Letter T r n) C) :
    lap r n C 1 τ τ' a a' P = ∑ b, ∑ b', (1 : Matrix (Fin n) (Fin n) C) b b' •
      MvPolynomial.pderiv (⟨τ, a, b⟩ : Letter T r n) (MvPolynomial.pderiv (⟨τ', a', b'⟩ : Letter T r n) P) := by
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rfl

theorem harmonic_product_bound : NormOneHarmonic := by
  intro C _ V d _ T r cc a Orb _ tau J _ X F Z ga n L pl H isX
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ _ a1 a2
  rw [lap_one_apply]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  by_cases hb : b = b'
  · subst hb
    by_cases h : (⟨τ, a1, b⟩ : Letter T r n) ∈ (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).vars
    · have h' : (⟨cc τ, a2, b⟩ : Letter T r n) ∉ (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).vars :=
        fun h2 => H.no_conj_letter τ a1 a2 b h h2
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars h', map_zero, smul_zero]
    · rw [pderiv_comm', MvPolynomial.pderiv_eq_zero_of_notMem_vars h, map_zero, smul_zero]
  · rw [Matrix.one_apply_ne hb, zero_smul]

end Formalism.L2.FormalSeriesBounds.RF
