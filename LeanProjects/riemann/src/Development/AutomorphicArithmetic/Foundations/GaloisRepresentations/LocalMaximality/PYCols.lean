import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma pk_mem' {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  rw [pk, dif_pos h]
  exact Finset.min'_mem I h

private lemma pk_zero' {d : ℕ} : pk ({0} : Finset (Fin (d + 1))) = 0 := by
  simp [pk]

private lemma inSp_sub {S κ κ' : Type} [CommRing S] [Algebra ℂ S] [Fintype κ] [Fintype κ']
    (R : Subalgebra ℂ S) (r : κ → S) (f : κ' → κ) {g : S} (h : InSp R (fun a => r (f a)) g) : InSp R r g := by
  classical
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨fun l => ∑ b ∈ Finset.univ.filter (fun b => f b = l), a b, fun l => R.sum_mem fun b _ => ha b, ?_⟩
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := f) (f := fun b => a b * r (f b))]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b hb => ?_
  rw [(Finset.mem_filter.mp hb).2]

private lemma inSp_self {S κ : Type} [CommRing S] [Algebra ℂ S] [Fintype κ]
    (R : Subalgebra ℂ S) (r : κ → S) (l : κ) : InSp R r (r l) := by
  classical
  refine ⟨fun l' => if l' = l then 1 else 0, fun l' => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  · simp

private lemma col_of_kos (hRS : RS) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S) (I J : Finset (Fin (d + 1))) (m : ℤ)
    (h : (kos T.act (T.M I J) (T.r n z (pk I) (pk J))).Z m ≤ (kos T.act (T.M I J) (T.r n z (pk I) (pk J))).B m) :
    (T.colCx n z I J).Z m ≤ (T.colCx n z I J).B m := by
  intro c hc
  have H := hRS S E T.act κ (T.M I J) (T.u n (pk I) (pk J)) (T.r n z (pk I) (pk J)) z (fun l => rfl) m c
  exact H.2.2.1.2 (h (H.2.1.1 hc))

private lemma admissible_append {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ κ' : Type} [LinearOrder κ] [LinearOrder κ'] (n : κ → ℕ × ℕ) (z : κ → S)
    (n' : κ' → ℕ × ℕ) (z' : κ' → S) (h : T.admitted n z) (h' : T.admitted n' z') : T.admitted (app n n') (app z z') := by
  intro i j l
  rcases hl : ofLex l with a | a
  · have := h i j a
    simpa [Sys.r, Sys.u, app, hl] using this
  · have := h' i j a
    simpa [Sys.r, Sys.u, app, hl] using this

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private lemma gS_X (i : Fin (d + 1)) :
    Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K') ((sysZ K x 0).X i) = (sysY x j2 d).X i := by
  ext
  simp [sysZ, sysY, gS, ← IsScalarTower.algebraMap_apply]

private lemma gS_Y (i : Fin (d + 1)) :
    Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K') ((sysZ K x 0).Y i) = (sysY x j2 d).Y i := by
  ext
  simp [sysZ, sysY, gS]

private lemma gS_r {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) (i j : Fin (d + 1)) (k : κ) :
    gS j2 ((sysZ K x 0).r n z i j k) = (sysY x j2 d).r n (fun l => gS j2 (z l)) i j k := by
  simp only [Sys.r, Sys.u, map_mul]
  congr 1
  have := congrArg (fun v : K'ˣ => ((v⁻¹ : K'ˣ) : K'))
    (show Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K')
        ((sysZ K x 0).X i ^ (n k).1 * (sysZ K x 0).Y j ^ (n k).2) =
        (sysY x j2 d).X i ^ (n k).1 * (sysY x j2 d).Y j ^ (n k).2 by
      rw [map_mul, map_pow, map_pow, gS_X x j2, gS_Y x j2])
  simpa [Units.coe_map_inv] using this

private lemma rT (i j : Fin (d + 1)) (l : Fin d) (hi : i = 0) :
    (sysY x j2 d).r n10 (gT x j2) i j l = tt K' x l := by
  subst hi
  simp [Sys.r, Sys.u, n10, gT, sysY, tt, div_eq_mul_inv]

private lemma cols_gen (hKE : YKE) (hOk : SysOk) (hRS : RS) (h0 : Y0 x j2) (hG : (sysY x j2 d).Good)
    {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K') (ha : (sysY x j2 d).admitted n z)
    (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) :
    ((∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ, (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n z (pk I) (pk J) l) 0) →
        ∃ e0, Over x j2 e e0 ∧ ∀ l, InSp (loc (rB ℂ K' (xv x) {0}) e0.1) ((sysY x j2 d).r n z (pk I) (pk J)) (tt K' x l)) →
      KE ((sysY x j2 d).colCx n z I J) d) ∧
    ((∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ, ¬ ∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n z (pk I) (pk J) l) 0) →
      ∀ m, ((sysY x j2 d).colCx n z I J).Z m ≤ ((sysY x j2 d).colCx n z I J).B m) := by
  have hr : ∀ l, (sysY x j2 d).r n z (pk I) (pk J) l ∈ RY (xv x) j2 I J :=
    ((hOk d K' (DR ℂ K') (sysY x j2 d) κ n z hG ha).2.1 I J _ (pk_mem' hI) _ (pk_mem' hJ)).1
  have hk := hKE F K K' d x j2 h0 κ ((sysY x j2 d).r n z (pk I) (pk J)) I J hI hr
  exact ⟨fun h m hm => col_of_kos hRS _ n z I J m (hk.1 h m hm),
    fun h m => col_of_kos hRS _ n z I J m fun c hc => hk.2.1 m c hc fun e he => absurd he (h e)⟩

end

theorem UpperTheory.Gal.productCup_of_system.yCols_of :
    YKE → PtG → PtT → FixLoc → GMap → ThMuLat → SysOk → RS → RYBasic → YCols := by
  intro hKE hPtG hPtT hFix hGM hTh hOk hRS hRY F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY κ _ _ n z hZ
  have h0 : Y0 x j2 := hY.toY0
  have hG : (sysY x j2 d).Good := (hRY F K K' d x j2 h0).2.1 d
  have hA0 : (sysY x j2 d).admitted n11 (sysY x j2 d).mu := (hTh d K' (DR ℂ K') (sysY x j2 d) hG).1
  have hAz : (sysY x j2 d).admitted n (fun l => gS j2 (z l)) := fun i j k => by
    have h2 := (hGM F K K' d x j2 h0 0 (Nat.zero_le _)).2.2.1 {i} {j} _ (hZ.adm i j k)
    rw [gS_r] at h2
    exact h2
  have hA1 : (sysY x j2 d).admitted (app n11 n) (gG x j2 z) := admissible_append _ _ _ _ _ hA0 hAz
  have hA2 : (sysY x j2 d).admitted n10 (gT x j2) := fun i j l => by
    have := hG.memX {i} {j} (Finset.singleton_nonempty j) i (Finset.mem_singleton_self i) l.succ
    simpa [Sys.r, Sys.u, n10, gT] using this
  have hA3 : (sysY x j2 d).admitted (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) := admissible_append _ _ _ _ _ hA1 hA2
  refine ⟨hA1, hA2, hA3, fun I J hI hJ => ?_⟩
  have c1 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA1 I J hI hJ
  have c2 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA2 I J hI hJ
  have c3 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA3 I J hI hJ
  have hi := pk_mem' hI
  have hj := pk_mem' hJ
  have pG : ∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ,
      (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r (app n11 n) (gG x j2 z) (pk I) (pk J) l) 0) →
      J = {0} ∧ ∃ e0 ∈ Fx, Over x j2 e e0 :=
    fun e he => hPtG F K K' d x j2 Fx A hY κ n z hZ I J _ hi _ hj e he
  have pT : ∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ,
      (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n10 (gT x j2) (pk I) (pk J) l) 0) →
      ∃ e0, Over x j2 e e0 :=
    fun e he => hPtT F K K' d x j2 h0 I J _ hi _ hj e he
  refine ⟨c1.1 ?_, c2.1 ?_, c3.1 ?_, fun hne m => ⟨c1.2 ?_ m, c3.2 ?_ m⟩⟩
  · intro e he
    obtain ⟨hJ0, e0, he0, hO⟩ := pG e he
    refine ⟨e0, hO, fun l => ?_⟩
    rw [hO.1, hJ0, pk_zero']
    obtain ⟨N, -, -, -, hN⟩ := hFix F K K' d x j2 Fx A hY e0 he0
    exact inSp_sub _ ((sysY x j2 d).r (app n11 n) (gG x j2 z) 0 0) (fun a => toLex (Sum.inl (dj 0 a))) (hN l)
  · intro e he
    obtain ⟨e0, hO⟩ := pT e he
    refine ⟨e0, hO, fun l => ?_⟩
    rw [← rT x j2 (pk I) (pk J) l (by rw [hO.1, pk_zero'])]
    exact inSp_self _ _ l
  · intro e he
    obtain ⟨e0, hO⟩ := pT e fun l => he (toLex (Sum.inr l))
    refine ⟨e0, hO, fun l => ?_⟩
    rw [← rT x j2 (pk I) (pk J) l (by rw [hO.1, pk_zero'])]
    exact inSp_sub _ ((sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) (pk I) (pk J))
      (fun a => toLex (Sum.inr a)) (inSp_self _ ((sysY x j2 d).r n10 (gT x j2) (pk I) (pk J)) l)
  · intro e he
    obtain ⟨hJ0, e0, -, hO⟩ := pG e he
    exact hne.elim (fun h => h hO.1) (fun h => h hJ0)
  · intro e he
    obtain ⟨hJ0, e0, -, hO⟩ := pG e fun l => he (toLex (Sum.inl l))
    exact hne.elim (fun h => h hO.1) (fun h => h hJ0)
