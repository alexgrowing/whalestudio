import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.ChainEmbInj

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem yjtZ_mono (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) {thr thr' : Fin q → WithTop ℤ} (h : ∀ k, thr k ≤ thr' k)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) LL J thr) : y ∈ YjtZ O (r := r) LL J thr' :=
  ⟨yjt_mono' _ _ h hy.1, hy.2⟩

theorem le_add_nat (x : WithTop ℤ) (b : ℕ) : x ≤ x + ((b : ℤ) : WithTop ℤ) :=
  le_add_of_nonneg_right (by exact_mod_cast Int.natCast_nonneg b)

theorem otherE_free {D : BlockData N} (hT : TieOK D) (j : Fin D.T.t → ℕ) (i : Fin D.T.t) {v : BVar N r D.T.t}
    (h : ∀ i', i' ≠ i → v ∉ (D.Ehat O (r := r) i').vars) : FreeV v (otherE O r D j i) := by
  classical
  unfold otherE
  exact freeV_of_vars (nv_prod _ fun i' hi' => nv_pow (h i' (Finset.ne_of_mem_erase hi')) _)

theorem cth_gen (D7 : Formalism.BasicNotions.D7) {D : BlockData N} (hT : TieOK D) {thr thr' : Fin D.T.q → WithTop ℤ} (n : ℕ)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k) (v : BVar N r D.T.t) (hv : OddV D v)
    {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J thr)
    {g : MvPolynomial (BVar N r D.T.t) (KK O)} (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    cth v n ((∏ i, D.Ehat O (r := r) i ^ j i) * tailP O r D jp y g) ∈ SSt O r D thr' := by
  classical
  have hXX : ∀ i c, IsMult O r D.LL.vec D.T.J (tieW hT i) (tieE hT i) (X (tieW hT i, c) * X (tieE hT i, c)) :=
    fun i c => isMult_XX D7 D.LL.vec D.T.J _ _ (tieW_ne_tieE hT i i) (hT.vecE i _) c c
  have hPP : ∀ i, IsMult O r D.LL.vec D.T.J (tieW hT i) (tieE hT i) (-(pairP O r hT i)) :=
    fun i => (IsMult.sum _ fun c _ => hXX i c).neg
  rcases v with ⟨a, c⟩ | ⟨l, s⟩
  ·
    obtain ⟨ha1, ha2⟩ := hv
    obtain ⟨a0, rfl⟩ : ∃ a0 : Fin N, a = Fin.castSucc a0 := ⟨a.castPred ha2, (Fin.castSucc_castPred a ha2).symm⟩
    have ha0 : a0 ≠ D.uPos := fun h => ha1 (by rw [h])
    have hv' : (Sum.inl (Fin.castSucc a0, c) : BVar N r D.T.t) = chainEmb N r D.T.t (a0, c) := rfl
    rw [hv']
    have Hc : ∀ b, b ≤ n → ∃ (cb : ℕ) (yb : MvPolynomial (Fin N × Fin r) (KK O)),
        yb ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J (fun k => thr k + ((b : ℤ) : WithTop ℤ)) ∧
        cth (chainEmb N r D.T.t (a0, c)) b (tailP O r D jp y g) = cb • tailP O r D jp yb g := fun b _ =>
      ⟨1, cth (a0, c) b y, yjtZ_cth D7 _ _ b (fun _ => le_rfl) _ hy, by rw [tail_chain D jp a0 ha0 c b y hg, one_smul]⟩
    have hZS : ∀ i', chainEmb N r D.T.t (a0, c) ≠ scalZ N r D.T.t (Fin.castSucc i') ∧
        chainEmb N r D.T.t (a0, c) ≠ scalS N r D.T.t (Fin.castSucc i') := fun i' => by
      constructor <;> simp [chainEmb, scalZ, scalS]
    have hemb : ∀ {x x' : Fin N × Fin r}, x ≠ x' → chainEmb N r D.T.t x ≠ chainEmb N r D.T.t x' :=
      fun h h' => h (chainEmb_inj N r D.T.t h')
    by_cases hW : ∃ i, a0 = tieW hT i
    · obtain ⟨i, rfl⟩ := hW
      refine tie_mem hT n hthr hL i _ (m' := X (chainEmb N r D.T.t (tieE hT i, c)))
        (E' := X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
          ∑ c' ∈ Finset.univ.erase c, X (chainEmb N r D.T.t (tieW hT i, c')) * X (chainEmb N r D.T.t (tieE hT i, c')))
        ?_ ?_ ?_ (hXX i c) false ?_ ?_ hg Hc
      · rw [Ehat_eq hT, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c)]
        ring
      · exact freeV_of_vars (nv_X (hemb fun h => tieW_ne_tieE hT i i (congrArg Prod.fst h)))
      · refine freeV_of_vars (nv_add (nv_mul (nv_X (hZS i).1) (nv_X (hZS i).2)) (nv_sum _ fun c' hc' =>
          nv_mul (nv_X (hemb fun h => Finset.ne_of_mem_erase hc' (congrArg Prod.snd h).symm))
            (nv_X (hemb fun h => tieW_ne_tieE hT i i (congrArg Prod.fst h)))))
      · simp only [Bool.false_eq_true, if_false, zero_add, map_mul, rename_X]
      · refine otherE_free hT j i fun i' hi' => nv_Ehat hT i' (hZS i').1 (hZS i').2
          (fun c' => hemb fun h => hi' (hT.inj _ _ (congrArg Fin.val (congrArg Prod.fst h)).symm))
          (fun c' => hemb fun h => tieW_ne_tieE hT i i' (congrArg Prod.fst h))
    · by_cases hE : ∃ i, a0 = tieE hT i
      · obtain ⟨i, rfl⟩ := hE
        refine tie_mem hT n hthr hL i _ (m' := X (chainEmb N r D.T.t (tieW hT i, c)))
          (E' := X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
            ∑ c' ∈ Finset.univ.erase c, X (chainEmb N r D.T.t (tieW hT i, c')) * X (chainEmb N r D.T.t (tieE hT i, c')))
          ?_ ?_ ?_ (hXX i c) false ?_ ?_ hg Hc
        · rw [Ehat_eq hT, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c)]
          ring
        · exact freeV_of_vars (nv_X (hemb fun h => tieW_ne_tieE hT i i (congrArg Prod.fst h).symm))
        · refine freeV_of_vars (nv_add (nv_mul (nv_X (hZS i).1) (nv_X (hZS i).2)) (nv_sum _ fun c' hc' =>
            nv_mul (nv_X (hemb fun h => tieW_ne_tieE hT i i (congrArg Prod.fst h).symm))
              (nv_X (hemb fun h => Finset.ne_of_mem_erase hc' (congrArg Prod.snd h).symm))))
        · simp only [Bool.false_eq_true, if_false, zero_add, map_mul, rename_X]
          ring
        · refine otherE_free hT j i fun i' hi' => nv_Ehat hT i' (hZS i').1 (hZS i').2
            (fun c' => hemb fun h => tieW_ne_tieE hT i' i (congrArg Prod.fst h).symm)
            (fun c' => hemb fun h => hi' (hT.inj _ _ (by
              have := congrArg Fin.val (congrArg Prod.fst h)
              simp only [tieE] at this
              omega)))
      ·
        push_neg at hW hE
        have hfree : FreeV (chainEmb N r D.T.t (a0, c)) (∏ i, D.Ehat O (r := r) i ^ j i) :=
          freeV_of_vars (nv_prod _ fun i' _ => nv_pow (nv_Ehat hT i' (hZS i').1 (hZS i').2
            (fun c' => hemb fun h => hW i' (congrArg Prod.fst h))
            (fun c' => hemb fun h => hE i' (congrArg Prod.fst h))) _)
        rw [cth_mul_free _ _ hfree, tail_chain D jp a0 ha0 c n y hg]
        exact gen_mem D thr' hL (yjtZ_cth D7 _ _ n hthr _ hy) hg
  ·
    have hl : l ≠ Fin.last D.T.t := hv
    obtain ⟨i, rfl⟩ : ∃ i : Fin D.T.t, l = Fin.castSucc i := ⟨l.castPred hl, (Fin.castSucc_castPred l hl).symm⟩
    have hch : ∀ x, chainEmb N r D.T.t x ≠ (Sum.inr (Fin.castSucc i, s) : BVar N r D.T.t) := fun x => by
      simp [chainEmb]
    have hoth : FreeV (Sum.inr (Fin.castSucc i, s) : BVar N r D.T.t) (otherE O r D j i) := by
      refine otherE_free hT j i fun i' hi' => nv_Ehat hT i' ?_ ?_ (fun c' => (hch _).symm) (fun c' => (hch _).symm)
      · simp only [scalZ, ne_eq, Sum.inr.injEq, Prod.mk.injEq, Fin.castSucc_inj, not_and]
        exact fun h => absurd h.symm hi'
      · simp only [scalS, ne_eq, Sum.inr.injEq, Prod.mk.injEq, Fin.castSucc_inj, not_and]
        exact fun h => absurd h.symm hi'
    have hrest : ∀ (F : MvPolynomial (BVar N r D.T.t) (KK O)),
        (Sum.inr (Fin.castSucc i, s) : BVar N r D.T.t) ∉ F.vars →
        (Sum.inr (Fin.castSucc i, s) : BVar N r D.T.t) ∉ (D.Eplus O (r := r) ^ jp * F *
          X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus * rename (chainEmb N r D.T.t) y * g).vars := by
      intro F hF
      refine nv_mul (nv_mul (nv_mul (nv_mul (nv_pow (nv_Eplus D ?_ ?_ ?_ ?_) _) hF) (nv_pow (nv_X ?_) _))
        (nv_rename _ hch y)) (nv_xi ?_ hg)
      · simp only [scalZ, ne_eq, Sum.inr.injEq, Prod.mk.injEq, not_and]
        exact fun h => absurd h (Fin.castSucc_lt_last i).ne
      · simp only [scalS, ne_eq, Sum.inr.injEq, Prod.mk.injEq, not_and]
        exact fun h => absurd h (Fin.castSucc_lt_last i).ne
      · intro c'; simp
      · intro c'; simp [xiVar]
      · simp only [scalZ, ne_eq, Sum.inr.injEq, Prod.mk.injEq, not_and]
        exact fun h => absurd h (Fin.castSucc_lt_last i).ne
      · intro c'; simp [xiVar]
    have hpair : (Sum.inr (Fin.castSucc i, s) : BVar N r D.T.t) ∉
        (rename (chainEmb N r D.T.t) (pairP O r hT i)).vars := nv_rename _ hch _
    cases s with
    | false =>
      refine tie_mem hT n hthr hL i _ (m' := X (scalS N r D.T.t (Fin.castSucc i)))
        (E' := rename (chainEmb N r D.T.t) (pairP O r hT i)) (Ehat_eq' hT i) ?_ (freeV_of_vars hpair) (hPP i) true ?_
        hoth hg ?_
      · exact freeV_of_vars (nv_X (by simp [scalS, scalZ]))
      · simp only [if_true]
        rw [Ehat_eq' hT i, map_neg]
        ring
      · intro b _
        refine ⟨(D.T.z i).choose b, y, yjtZ_mono _ _ (fun k => le_add_nat _ b) hy, ?_⟩
        have e : tailP O r D jp y g = (D.Eplus O (r := r) ^ jp *
            (∏ i' ∈ Finset.univ.erase i, X (scalZ N r D.T.t (Fin.castSucc i')) ^ D.T.z i') *
            X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus * rename (chainEmb N r D.T.t) y * g) *
            X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i := by
          unfold tailP
          rw [← Finset.mul_prod_erase Finset.univ (fun i' => (X (scalZ N r D.T.t (Fin.castSucc i')) :
            MvPolynomial (BVar N r D.T.t) (KK O)) ^ D.T.z i') (Finset.mem_univ i)]
          ring
        have hfr := freeV_of_vars (hrest (∏ i' ∈ Finset.univ.erase i, X (scalZ N r D.T.t (Fin.castSucc i')) ^ D.T.z i')
          (nv_prod _ fun i' hi' => nv_pow (nv_X (by
            simp only [scalZ, ne_eq, Sum.inr.injEq, Prod.mk.injEq, Fin.castSucc_inj, and_true]
            exact fun h => Finset.ne_of_mem_erase hi' h.symm)) _))
        have hfr' : FreeV (scalZ N r D.T.t (Fin.castSucc i)) _ := hfr
        rw [e, cth_mul_free _ _ hfr', cth_X_pow, mul_smul_comm]
    | true =>
      refine tie_mem hT n hthr hL i _ (m' := X (scalZ N r D.T.t (Fin.castSucc i)))
        (E' := rename (chainEmb N r D.T.t) (pairP O r hT i)) ?_ ?_ (freeV_of_vars hpair) (hPP i) true ?_
        hoth hg ?_
      · rw [Ehat_eq' hT i]
        unfold scalS
        ring
      · exact freeV_of_vars (nv_X (by simp [scalZ]))
      · simp only [if_true]
        rw [Ehat_eq' hT i, map_neg]
        unfold scalS
        ring
      · intro b _
        have hfr : FreeV (Sum.inr (Fin.castSucc i, true) : BVar N r D.T.t) (tailP O r D jp y g) := by
          unfold tailP
          exact freeV_of_vars (hrest _ (nv_prod _ fun i' _ => nv_pow (nv_X (by simp [scalZ])) _))
        by_cases hb : b = 0
        · subst hb
          exact ⟨1, y, yjtZ_mono _ _ (fun k => le_add_nat _ 0) hy, by rw [cth_zero, one_smul]⟩
        · exact ⟨0, y, yjtZ_mono _ _ (fun k => le_add_nat _ b) hy, by rw [cth_free _ hfr hb, zero_smul]⟩

theorem cth_SSt (D7 : Formalism.BasicNotions.D7) {D : BlockData N} (hT : TieOK D) {thr thr' : Fin D.T.q → WithTop ℤ} (n : ℕ)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k) (v : BVar N r D.T.t) (hv : OddV D v)
    {u : MvPolynomial (BVar N r D.T.t) (KK O)} (hu : u ∈ SSt O r D thr) : cth v n u ∈ SSt O r D thr' := by
  have hle : SSt O r D thr ≤ (SSt O r D thr').comap ((cthL v n).restrictScalars O) := by
    unfold SSt BlockData.SSZ
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, hL, y, hy, g, hg, rfl⟩ := hx
    have h := cth_gen D7 hT n hthr v hv hL hy hg
    unfold tailP at h
    simp only [← mul_assoc] at h
    exact h
  exact hle hu

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
