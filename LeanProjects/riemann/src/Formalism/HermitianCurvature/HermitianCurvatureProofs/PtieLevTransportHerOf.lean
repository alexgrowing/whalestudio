import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelTransport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermMulVecMulVec

open Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB Formalism.FourierDecayAlt.P.PTieL

section closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem mem_of_gen {V' : Type} [AddCommGroup V'] [Module ℂ V'] {i : Fin (P.r + 1)}
    (U : RadSp P.k P.r z z' π π' →ₗ[ℂ] V') (K : Submodule ℂ V')
    (h : ∀ Φ, HerGenC S P z z' π π' L st l0 Bs i Φ → U Φ ∈ K) :
    ∀ Φ ∈ herKc S P z z' π π' L st l0 Bs i, U Φ ∈ K := by
  have hle : herKc S P z z' π π' L st l0 Bs i ≤ K.comap U := Submodule.span_le.mpr fun Φ hΦ => h Φ hΦ
  exact fun Φ hΦ => hle hΦ

theorem waveC_closed (l : Fin P.r) (hl : l.val = 0) {w : List (Wd.Letter ℂ S)} (hw : WordOK P z z' π π' st l0 w)
    {s : ℂ} {Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')} (hW : multiplicationOperator Wv (fun c' _ => fsv s (c' l)))
    (hW' : multiplicationOperator Wv' (fun c' _ => fsv (-s) (c' l))) (a b : Wd.Ix S) :
    ∀ Ψ ∈ herKc S P z z' π π' L st l0 Bs 0, (Wd.Vw (mkP Wv Wv') s w a b).1 Ψ ∈ herKc S P z z' π π' L st l0 Bs 0 := by
  have h0 : l.castSucc = 0 := Fin.ext (by simp [hl])
  refine mem_of_gen (Wd.Vw (mkP Wv Wv') s w a b).1 _ fun Φ hΦ => Submodule.subset_span ?_
  have := HerGenC.waveC l w s Wv Wv' a b Φ hw hW hW' (by rw [h0]; exact hΦ)
  rw [h0] at this
  exact this

theorem waveZ_closed (hr : P.r = 0) {w : List (Wd.Letter ℂ S)} (hw : WordOK P z z' π π' st l0 w)
    {s : ℂ} {Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')}
    (hW : multiplicationOperator Wv (fun _ g => fsv s (P5.zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (P5.zeta P.k P.r z z' g))) (a b : Wd.Ix S) :
    ∀ Ψ ∈ herKc S P z z' π π' L st l0 Bs 0, (Wd.Vw (mkP Wv Wv') s w a b).1 Ψ ∈ herKc S P z z' π π' L st l0 Bs 0 := by
  have h0 : Fin.last P.r = 0 := Fin.ext (by simp [hr])
  refine mem_of_gen (Wd.Vw (mkP Wv Wv') s w a b).1 _ fun Φ hΦ => Submodule.subset_span ?_
  have := HerGenC.waveZ w s Wv Wv' a b Φ hw hW hW' (by rw [h0]; exact hΦ)
  rw [h0] at this
  exact this

end closure

section wave

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem mrel_Uinv (x : ℂ) : MRel T (Formalism.YangianSpanCharacter.T.Uinv (A := Pr V) x) (Formalism.YangianSpanCharacter.T.Uinv (A := Pr V') x) := fun a b => by
  fin_cases a <;> fin_cases b <;> simp [Formalism.YangianSpanCharacter.T.Uinv] <;>
    first | exact rel_one | exact rel_zero | exact rel_algebraMap x

theorem arel_UUiw (s : ℂ) : ∀ w : List (Wd.Letter ℂ S), ARel T (Wd.UUiw (A := Pr V) s w) (Wd.UUiw (A := Pr V') s w)
  | [] => by unfold Wd.UUiw; exact arel_one
  | l :: w => by
    unfold Wd.UUiw
    exact arel_mul (arel_ins _ (brel_lift0 (mrel_Uinv _))) (arel_UUiw s w)

theorem arel_Vw {f : Pr V} {f' : Pr V'} (hf : Rel T f f') (s : ℂ) (w : List (Wd.Letter ℂ S)) :
    ARel T (Wd.Vw f s w) (Wd.Vw f' s w) := by
  unfold Wd.Vw
  exact arel_mul (arel_io hf) (arel_UUiw s w)

end wave

theorem glue_at {r : ℕ} (i : ℕ) (hi : i < r) (c : Fin r → ℂ) (c'' : Fin (r - i) → ℂ) (l : Fin r) (hl : l.val = i) :
    P5.glue (⟨i, by omega⟩ : Fin (r + 1)) c (PTie.shiftCf ⟨i, by omega⟩ c'') l = c'' ⟨0, by omega⟩ := by
  unfold P5.glue PTie.shiftCf
  rw [dif_pos (by simp [hl])]
  congr 1
  ext
  simp [hl]

theorem zeta_step {k n ρ : ℕ} (hn : n = 1 + ρ) {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn.symm (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn.symm (liftVec k 1 ρ zs')) (g : Mx k ρ) :
    P5.zeta k n z z' (D.castM hn.symm (ιLev k 1 ρ g)) = P5.zeta k ρ zs zs' g := by
  subst hn
  rw [P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  rw [P.JCTx5.castM_rfl]
  exact zeta_iota zs zs' g

theorem wordOK_tr {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
    {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {X : ActualOps P.k P.r z z' π π'} {μ : Measure (Mt P.k P.r)}
    {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 j : ℕ}
    {zj zj' : Fin (2 * (P.r - j) + P.k + 1) → ℂ} {πj : Mx P.k (P.r - j) → (Wp →L[ℂ] Wp)}
    {πj' : Mx P.k (P.r - j) → (Wq →L[ℂ] Wq)} {Xj : ActualOps (JC.parLev P j).k (JC.parLev P j).r zj zj' πj πj'}
    {μj : Measure (Mt P.k (P.r - j))} {Lj : R.LevelData (Pr (RadSp P.k (P.r - j) zj zj' πj πj')) (P.r - j)}
    {stj : Fr.Start (Pr (RadSp P.k (P.r - j) zj zj' πj πj'))}
    (hD : IsData P z z' π π' X μ L st l0) (hDj : IsData (JC.parLev P j) zj zj' πj πj' Xj μj Lj stj l0)
    {S : Type} [Fintype S] [DecidableEq S] {w : List (Wd.Letter ℂ S)} (hw : WordOK P z z' π π' st l0 w) :
    WordOK (JC.parLev P j) zj zj' πj πj' stj l0 w := by
  obtain ⟨⟨hA1, hA2, hA3, hA4⟩, hw2, hw3⟩ := hw
  have hq : stj.q = st.q := hDj.2.2.2.2.1.trans hD.2.2.2.2.1.symm
  have hinv : stj.inv = st.inv := hDj.2.2.2.2.2.1.trans hD.2.2.2.2.2.1.symm
  refine ⟨⟨hA1, hA2, fun l hl => ?_, hA4⟩, hw2, hw3⟩
  rw [hq, hinv]
  exact hA3 l hl

section mul

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r i : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {zs zs' : Fin (2 * (r - i) + k + 1) → ℂ} {πs : Mx k (r - i) → (Wp →L[ℂ] Wp)}
  {πs' : Mx k (r - i) → (Wq →L[ℂ] Wq)}

theorem mulC_tr (hi : i < r) (c : Fin r → ℂ) (U : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zs zs' πs πs')
    (hU : ∀ Φ c'' g, (U Φ : Fn k (r - i) (Wq →L[ℂ] Wp)) c'' g =
      (Φ : Fn k r (Wq →L[ℂ] Wp)) (P5.glue ⟨i, by omega⟩ c (PTie.shiftCf ⟨i, by omega⟩ c''))
        (D.castM (by omega) (ιLev k i (r - i) g)))
    (l : Fin r) (hl : l.val = i) (s : ℂ) {Wv : Module.End ℂ (RadSp k r z z' π π')}
    {Wl : Module.End ℂ (RadSp k (r - i) zs zs' πs πs')} (hW : multiplicationOperator Wv (fun c' _ => fsv s (c' l)))
    (hWl : multiplicationOperator Wl (fun c' _ => fsv s (c' ⟨0, by omega⟩))) (v : RadSp k r z z' π π') :
    Wl (U v) = U (Wv v) := by
  apply Subtype.ext
  funext c'' g
  have e1 := hWl (U v) c'' g
  have e2 := hU v c'' g
  have e3 := hU (Wv v) c'' g
  have e4 := hW v (P5.glue ⟨i, by omega⟩ c (PTie.shiftCf ⟨i, by omega⟩ c'')) (D.castM (by omega) (ιLev k i (r - i) g))
  dsimp only at e1 e4
  rw [glue_at i hi c c'' l hl] at e4
  show (Wl (U v) : Fn k (r - i) (Wq →L[ℂ] Wp)) c'' g = (U (Wv v) : Fn k (r - i) (Wq →L[ℂ] Wp)) c'' g
  rw [e1, e2, e3, e4]

theorem mulZ_tr (c : Fin r → ℂ) (U : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zs zs' πs πs') (hir : i ≤ r)
    (hU : ∀ Φ c'' g, (U Φ : Fn k (r - i) (Wq →L[ℂ] Wp)) c'' g =
      (Φ : Fn k r (Wq →L[ℂ] Wp)) (P5.glue ⟨i, by omega⟩ c (PTie.shiftCf ⟨i, by omega⟩ c''))
        (D.castM (by omega) (ιLev k i (r - i) g)))
    (hz : ∀ g, P5.zeta k r z z' (D.castM (by omega) (ιLev k i (r - i) g)) = P5.zeta k (r - i) zs zs' g)
    (s : ℂ) {Wv : Module.End ℂ (RadSp k r z z' π π')} {Wl : Module.End ℂ (RadSp k (r - i) zs zs' πs πs')}
    (hW : multiplicationOperator Wv (fun _ g => fsv s (P5.zeta k r z z' g)))
    (hWl : multiplicationOperator Wl (fun _ g => fsv s (P5.zeta k (r - i) zs zs' g))) (v : RadSp k r z z' π π') :
    Wl (U v) = U (Wv v) := by
  apply Subtype.ext
  funext c'' g
  have e1 := hWl (U v) c'' g
  have e2 := hU v c'' g
  have e3 := hU (Wv v) c'' g
  have e4 := hW v (P5.glue ⟨i, by omega⟩ c (PTie.shiftCf ⟨i, by omega⟩ c'')) (D.castM (by omega) (ιLev k i (r - i) g))
  dsimp only at e1 e4
  rw [hz g] at e4
  show (Wl (U v) : Fn k (r - i) (Wq →L[ℂ] Wp)) c'' g = (U (Wv v) : Fn k (r - i) (Wq →L[ℂ] Wp)) c'' g
  rw [e1, e2, e3, e4]

end mul

theorem resG_smul {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (i : Fin (r + 1)) (κ : ℂ)
    (J : Mx k r → E) (c : Fin r → ℂ) (g : Mx k r) : resG k r i (κ • J) c g = κ • resG k r i J c g := by
  unfold resG
  rw [Pi.smul_apply, smul_comm]

set_option maxHeartbeats 4000000 in
theorem lev_ind_her {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (hT : D.TowerNormalised T) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (X : ActualOps P.k P.r T.base.z T.base.z' T.base.π T.base.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π'))) (l0 : ℕ)
    (hD : P5.IsData P T.base.z T.base.z' T.base.π T.base.π' X μ L st l0) (hl1 : 1 ≤ l0) (hl2 : l0 ≤ P.k)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (κ0 : ℂ) (hκ0 : ∀ F, B.JF Bs F = κ0 • B.JF T.base F)
    (hS : PTie.SliceStepHer) (c : Fin P.r → ℂ) :
    ∀ (j : ℕ) (hj : j ≤ P.r), (∀ l : Fin P.r, l.val < j → c l ≠ 0) →
    ∃ (Xj : ActualOps (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
      (μj : Measure (Mt P.k (P.r - j)))
      (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
      (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')))
      (Tj : RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π' →ₗ[ℂ]
        RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      P5.IsData (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj μj Lj stj l0 ∧
      KB.ZetaNorm (T.bs j) μj ∧
      (∀ Φ c'' g, (Tj Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c'' g =
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (P5.glue ⟨j, by omega⟩ c (PTie.shiftCf ⟨j, by omega⟩ c''))
          (D.castM (by omega) (ιLev P.k j (P.r - j) g))) ∧
      (∃ κ : ℝ, 0 < κ ∧ ∀ Φ Ψ c'', P5.pairAt μj (Tj Φ) (Tj Ψ) c'' =
        (κ : ℂ) * P5.pairAt μ Φ Ψ (P5.glue ⟨j, by omega⟩ c (PTie.shiftCf ⟨j, by omega⟩ c''))) ∧
      (∀ l : Fin (P.r - j), Rel Tj (L.p ⟨l.val + j, by omega⟩) (Lj.p l) ∧
        Rel Tj (L.c ⟨l.val + j, by omega⟩) (Lj.c l) ∧ Rel Tj (L.ci ⟨l.val + j, by omega⟩) (Lj.ci l)) ∧
      (∀ (n : ℕ) (hn : n + j ≤ P.r) (Y : ℂ),
        MRel Tj (P5.QQi L st ⟨n + j, by omega⟩ Y) (P5.QQi Lj stj ⟨n, by omega⟩ Y)) ∧
      (∀ g, P5.zeta P.k P.r T.base.z T.base.z' (D.castM (by omega) (ιLev P.k j (P.r - j) g)) =
        P5.zeta P.k (P.r - j) (T.bs j).z (T.bs j).z' g) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S],
        ∀ Φ ∈ herKc S P T.base.z T.base.z' T.base.π T.base.π' L st l0 Bs ⟨j, by omega⟩,
          Tj Φ ∈ herKc S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) 0
  | 0, _, _ => by
    obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - 0) Wp Wq (T.bs 0)
    have h1 : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
    obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, μ = a • μ0 := by
      have hU := Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed P.k P.r
      have h1' := h1
      have h0 : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ0 := hμ0.1
      rw [glev_last_eq] at h1' h0
      exact Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar P.k P.r _ μ0 μ hU h0 h1'.conc h1'.left h1'.finite_compact
    have ha0 : (a : ℝ) ≠ 0 := by
      intro h
      apply h1.ne_zero
      rw [ha, show a = 0 from by exact_mod_cast h, zero_smul]
    have hD0 : P5.IsData (JC.parLev P 0) (T.bs 0).z (T.bs 0).z' (T.bs 0).π (T.bs 0).π' X μ0 L st l0 :=
      ⟨JCTx5.isPlace_lev P T ⟨0, by omega⟩ hP, hμ0.1, hD.2.2⟩
    refine ⟨X, μ0, L, st, LinearMap.id, hD0, hμ0,
      fun Φ c'' g => ?_, ⟨(a : ℝ)⁻¹, inv_pos.2 (lt_of_le_of_ne a.2 (Ne.symm ha0)), fun Φ Ψ c'' => ?_⟩,
      fun l => ⟨rel_id _, rel_id _, rel_id _⟩, fun n hn Y => mrel_id _, fun g => ?_, fun S _ _ => ?_⟩
    · rw [glue_zero', castM_iota0]; rfl
    · rw [glue_zero', ha, pairAt_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ha0, Complex.ofReal_one,
        one_mul]
      rfl
    · rw [castM_iota0]
      try rfl
    · refine mem_of_gen (S := S) LinearMap.id
        (herKc S (JC.parLev P 0) (T.bs 0).z (T.bs 0).z' (T.bs 0).π (T.bs 0).π' L st l0 (T.bs 0) 0) fun Φ hΦ => ?_
      suffices H : ∀ (i : Fin (P.r + 1)) (Φ : RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π'),
          HerGenC S P T.base.z T.base.z' T.base.π T.base.π' L st l0 Bs i Φ → i.val = 0 →
          Φ ∈ herKc S (JC.parLev P 0) (T.bs 0).z (T.bs 0).z' (T.bs 0).π (T.bs 0).π' L st l0 (T.bs 0) 0 from
        H _ Φ hΦ rfl
      intro i Φ h
      induction h with
      | jf F Φ hF hΦ =>
        intro _
        by_cases hκ : κ0 = 0
        · have e : Φ = 0 := by
            apply Subtype.ext
            funext c' g
            by_cases hx : (c', g) ∈ DomR P.k P.r T.base.z T.base.z'
            · have h2 := hΦ (c', g) hx
              simp only at h2
              rw [h2, hκ0 F, resG_smul, hκ, zero_smul]
              try rfl
            · exact Φ.2.1 (c', g) hx
          rw [e]
          exact Submodule.zero_mem _
        · obtain ⟨Φ', hΦ'e⟩ : ∃ Φ' : RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π', Φ' = κ0⁻¹ • Φ := ⟨_, rfl⟩
          have hΦ' : IsRadJF (JC.parLev P 0) (T.bs 0).z (T.bs 0).z' (T.bs 0).π (T.bs 0).π' (T.bs 0) F Φ' := by
            intro x hx
            rw [hΦ'e]
            show κ0⁻¹ • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
            rw [hΦ x hx, hκ0 F, resG_smul, smul_smul, inv_mul_cancel₀ hκ, one_smul]
            try rfl
          have e : Φ = κ0 • Φ' := by rw [hΦ'e, smul_smul, mul_inv_cancel₀ hκ, one_smul]
          have hg := Submodule.subset_span (R := ℂ) (HerGenC.jf (S := S) (P := JC.parLev P 0) (z := (T.bs 0).z)
            (z' := (T.bs 0).z') (π := (T.bs 0).π) (π' := (T.bs 0).π') (L := L) (st := st) (l0 := l0) (D := T.bs 0)
            F Φ' hF hΦ')
          rw [e]
          exact Submodule.smul_mem _ κ0 hg
      | slice l w a b Φ hw hΦ ih =>
        intro he
        simp at he
      | waveC l w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
        intro he
        exact waveC_closed l (by simpa using he) (wordOK_tr hD hD0 hw) hW hW' a b Φ (ih he)
      | waveZ w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
        intro he
        exact waveZ_closed (by simpa [JC.parLev] using he) (wordOK_tr hD hD0 hw) hW hW' a b Φ (ih he)
  | j + 1, hj, hc => by
    obtain ⟨Xj, μj, Lj, stj, Tj, hDj, hZj, hform, ⟨κ, hκ, hpair⟩, hsite, hqq, hzeta, hher⟩ :=
      lev_ind_her P T hT hP X μ L st l0 hD hl1 hl2 Bs κ0 hκ0 hS c j (by omega) (fun l hl => hc l (by omega))
    have hj' : j + 1 ≤ P.r := hj
    have hPl := JCTx5.isPlace_lev P T ⟨j + 1, by omega⟩ hP
    obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
    obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs l0
    obtain ⟨μs, hμs⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - (j + 1)) Wp Wq (T.bs (j + 1))
    have hDs : P5.IsData (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
        (T.bs (j + 1)).π' Xs μs Ls sts l0 := ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩
    have hn : P.r - j = 1 + (P.r - (j + 1)) := by omega
    have hcj : c ⟨j, by omega⟩ ≠ 0 := hc ⟨j, by omega⟩ (by simp)
    obtain ⟨T', hf', hs', hq', hp'⟩ := step_cast (k := P.k) (n := P.r - j) (ρ := P.r - (j + 1)) hn
      (levTower_bs_z_eq_castV_liftVec T j hj') (levTower_bs_z'_eq_castV_liftVec T j hj') (T.bs (j + 1)).z_mem (T.bs (j + 1)).z'_mem (tower_π T j hj')
      (tower_π' T j hj') Xj Xs Lj stj Ls sts (M.sgn (JC.parLev P j) l0) μj μs hDj.2.2.1 hDs.2.2.1
      hDj.2.2.2.1 hDs.2.2.2.1 hZj.1 hμs.1 hZj.2 hμs.2 (c ⟨j, by omega⟩) hcj
    have hform1 : ∀ Φ c'' g, ((T' ∘ₗ Tj) Φ : Fn P.k (P.r - (j + 1)) (Wq →L[ℂ] Wp)) c'' g =
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (P5.glue ⟨j + 1, by omega⟩ c (PTie.shiftCf ⟨j + 1, by omega⟩ c''))
          (D.castM (by omega) (ιLev P.k (j + 1) (P.r - (j + 1)) g)) := by
      intro Φ c'' g
      rw [LinearMap.comp_apply, hf', hform, glue_step j hj' c c'' hn,
        lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r hn.symm (by omega) (by omega)]
    have hzeta1 : ∀ g, P5.zeta P.k P.r T.base.z T.base.z' (D.castM (by omega) (ιLev P.k (j + 1) (P.r - (j + 1)) g)) =
        P5.zeta P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' g := by
      intro g
      rw [← lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r hn.symm (by omega) (by omega), hzeta,
        zeta_step hn (levTower_bs_z_eq_castV_liftVec T j hj') (levTower_bs_z'_eq_castV_liftVec T j hj') g]
    refine ⟨Xs, μs, Ls, sts, T' ∘ₗ Tj, hDs, hμs, hform1, ⟨κ, hκ, fun Φ Ψ c'' => ?_⟩,
      fun l => ?_, fun n hn' Y => ?_, hzeta1, fun S _ _ => ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hp', hpair, glue_step j hj' c c'' hn]
    · have e : (⟨l.val + 1 + j, by omega⟩ : Fin P.r) = ⟨l.val + (j + 1), by omega⟩ :=
        Fin.ext (show l.val + 1 + j = l.val + (j + 1) by omega)
      obtain ⟨a1, a2, a3⟩ := hsite ⟨l.val + 1, by omega⟩
      obtain ⟨b1, b2, b3⟩ := hs' l
      rw [← e]
      exact ⟨rel_comp a1 b1, rel_comp a2 b2, rel_comp a3 b3⟩
    · have e : (⟨n + 1 + j, by omega⟩ : Fin (P.r + 1)) = ⟨n + (j + 1), by omega⟩ :=
        Fin.ext (show n + 1 + j = n + (j + 1) by omega)
      have a := hqq (n + 1) (by omega) Y
      have b := hq' n (by omega) Y
      rw [← e]
      exact mrel_comp a b
    · refine mem_of_gen (S := S) (T' ∘ₗ Tj) (herKc S (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z'
        (T.bs (j + 1)).π (T.bs (j + 1)).π' Ls sts l0 (T.bs (j + 1)) 0) fun Φ hΦ => ?_
      suffices H : ∀ (i : Fin (P.r + 1)) (Φ : RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π'),
          HerGenC S P T.base.z T.base.z' T.base.π T.base.π' L st l0 Bs i Φ → i.val = j + 1 →
          (T' ∘ₗ Tj) Φ ∈ herKc S (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
            (T.bs (j + 1)).π' Ls sts l0 (T.bs (j + 1)) 0 from H _ Φ hΦ rfl
      intro i Φ h
      induction h with
      | jf F Φ hF hΦ =>
        intro he
        simp at he
      | slice l w a b Φ hw hΦ ih =>
        intro he
        have hl : l.val = j := by simp at he; omega
        have hmem : Φ ∈ herKc S P T.base.z T.base.z' T.base.π T.base.π' L st l0 Bs ⟨j, by omega⟩ := by
          have e : l.castSucc = ⟨j, by omega⟩ := Fin.ext (by simp [hl])
          exact Submodule.subset_span (by rw [← e]; exact hΦ)
        have hTΦ := hher S Φ hmem
        have hl' : l = ⟨0 + j, by omega⟩ := Fin.ext (by simp [hl])
        obtain ⟨a1, a2, a3⟩ := hsite ⟨0, by omega⟩
        have hrel := arel_bT (σ := P5.site L ⟨0 + j, by omega⟩) (σ' := P5.site Lj ⟨0, by omega⟩) a1 a2 a3 w a b
        have e2 : Tj ((P5.bTl L ⟨0 + j, by omega⟩ w a b).1 Φ) =
            (P5.bTl Lj (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w a b).1 (Tj Φ) :=
          (LinearMap.congr_fun hrel.1 Φ).symm
        rw [LinearMap.comp_apply, hl', e2]
        exact hS Wp Wq P T hP hT j hj' l0 hl1 hl2 Xj μj Lj stj Xs μs Ls sts hDj hDs T' (c ⟨j, by omega⟩) hcj hf' S w a b
          (wordOK_tr hD hDj hw) (Tj Φ) hTΦ
      | waveC l w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
        intro he
        have hl : l.val = j + 1 := by simpa using he
        obtain ⟨Wl, hWl⟩ := Formalism.FourierDecayAlt.P5.waveCExists Wp Wq P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z'
          (T.bs (j + 1)).π (T.bs (j + 1)).π' ⟨0, by omega⟩ s
        obtain ⟨Wl', hWl'⟩ := Formalism.FourierDecayAlt.P5.waveCExists Wp Wq P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z'
          (T.bs (j + 1)).π (T.bs (j + 1)).π' ⟨0, by omega⟩ (-s)
        have hrel : Rel (T' ∘ₗ Tj) (mkP Wv Wv') (mkP Wl Wl') :=
          rel_mk (fun v => mulC_tr (i := j + 1) (by omega) c (T' ∘ₗ Tj) hform1 l hl s hW hWl v)
            (fun v => mulC_tr (i := j + 1) (by omega) c (T' ∘ₗ Tj) hform1 l hl (-s) hW' hWl' v)
        have hV := arel_Vw hrel s w
        have e : (T' ∘ₗ Tj) ((Wd.Vw (mkP Wv Wv') s w a b).1 Φ) = (Wd.Vw (mkP Wl Wl') s w a b).1 ((T' ∘ₗ Tj) Φ) :=
          (LinearMap.congr_fun (hV a b).1 Φ).symm
        rw [e]
        exact waveC_closed (⟨0, by have := l.isLt; change 0 < P.r - (j + 1); omega⟩ : Fin (JC.parLev P (j + 1)).r) rfl (wordOK_tr hD hDs hw) hWl hWl' a b _ (ih he)
      | waveZ w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
        intro he
        have hr : P.r = j + 1 := by simpa using he
        obtain ⟨Wl, hWl⟩ := Formalism.FourierDecayAlt.P5.waveZExists Wp Wq P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z'
          (T.bs (j + 1)).π (T.bs (j + 1)).π' s
        obtain ⟨Wl', hWl'⟩ := Formalism.FourierDecayAlt.P5.waveZExists Wp Wq P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z'
          (T.bs (j + 1)).π (T.bs (j + 1)).π' (-s)
        have hrel : Rel (T' ∘ₗ Tj) (mkP Wv Wv') (mkP Wl Wl') :=
          rel_mk (fun v => mulZ_tr (i := j + 1) c (T' ∘ₗ Tj) hj' hform1 hzeta1 s hW hWl v)
            (fun v => mulZ_tr (i := j + 1) c (T' ∘ₗ Tj) hj' hform1 hzeta1 (-s) hW' hWl' v)
        have hV := arel_Vw hrel s w
        have e : (T' ∘ₗ Tj) ((Wd.Vw (mkP Wv Wv') s w a b).1 Φ) = (Wd.Vw (mkP Wl Wl') s w a b).1 ((T' ∘ₗ Tj) Φ) :=
          (LinearMap.congr_fun (hV a b).1 Φ).symm
        rw [e]
        exact waveZ_closed (by simp [JC.parLev]; omega) (wordOK_tr hD hDs hw) hWl hWl' a b _ (ih he)

theorem levTransportHer_of (hJ : PTie.JFScale) (hS : PTie.SliceStepHer) : PTie.LevTransportHer := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 Bs hD hl1 hl2 hz hz' hπ hπ' i c hc
  obtain ⟨T, h1, h2, h3, h4, hN⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq Bs
  obtain ⟨κ0, hκ0⟩ := hJ P.k P.r Wp Wq Bs T.base h1.symm h2.symm h3.symm h4.symm
  have e1 : T.base.z = z := h1.trans hz
  have e2 : T.base.z' = z' := h2.trans hz'
  have e3 : T.base.π = π := h3.trans hπ
  have e4 : T.base.π' = π' := h4.trans hπ'
  subst e1 e2 e3 e4
  obtain ⟨Xi, μi, Li, sti, Ti, hDi, -, hform, hpair, hsite, hqq, -, hher⟩ :=
    lev_ind_her P T hN hD.1 X μ L st l0 hD hl1 hl2 Bs κ0 hκ0 hS c i.val (by omega) hc
  refine ⟨T.bs i, Xi, μi, Li, sti, Ti, hDi, ⟨hform, hpair, fun n hn Y => hqq n hn Y,
    fun S _ _ w => ⟨fun l => ?_, fun n hn => ?_, fun hw => wordOK_tr hD hDi hw⟩⟩, fun S _ _ => hher S⟩
  · obtain ⟨a1, a2, a3⟩ := hsite l
    exact arel_bT (σ := P5.site L ⟨l.val + i, by omega⟩) (σ' := P5.site Li l) a1 a2 a3 w
  · exact arel_RRw (fun Y => hqq n hn Y) w

end Formalism.FourierDecayAlt.P.PTieH

namespace Formalism.FourierDecayAlt.P

theorem ptie_levTransportHer_of : Formalism.FourierDecayAlt.P.PTie.JFScale → Formalism.FourierDecayAlt.P.PTie.SliceStepHer →
    Formalism.FourierDecayAlt.P.PTie.LevTransportHer := PTieH.levTransportHer_of

end Formalism.FourierDecayAlt.P
