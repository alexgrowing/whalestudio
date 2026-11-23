import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCMain
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlace
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAdjointIntegralEndOfLadicLimit
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfLadicActionLimitStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLadicSeparatingSequenceEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DiagonalSplitStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralSeriesFrameEqProdRowsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEndomorphismPairW0Statement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeBiadditiveSymmAdjointIntegralEndStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivationsConstantInLogCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffDerivationPolynomialEqJetAt0Statement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdSubstDisjointVariablesStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdmissibleRowsValueEqRowGaugeStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermEqGaugedFormalGroupLawExpIntegralStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlaceStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquarStatement

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ValSelf

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) {d : ℕ} [NeZero d] {Orb : Type} {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

theorem exists_sep (p : ∀ o, SelfData Y d (I0 o)) (hs : SelfSep Y p) (o : Orb) :
    ∃ E E' : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C, IsEnd (Y.rawSelf (p o)) V E E' ∧
      (∀ g c, E.mulVec ((Y.rawSelf (p o)).u g c) = (Y.rawSelf (p o)).u g c) ∧
      ∀ o', o' ≠ o → ∀ g c, E.mulVec ((Y.rawSelf (p o')).u g c) = 0 ∧ E'.mulVec ((Y.rawSelf (p o')).u g c) = 0 := by
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.T.exists_ladic_separating_sequence_embeddings C V O d (p o).em (p o).em_int (p o).em_frob (p o).em_unr
  let X : RawChart C d (fun _ => I0 o) (Fin dd) :=
    { lg := fun i => un1 (Y.lg i), ex := fun i => un1 (Y.ex i), h := Y.h, k := 0, u := fun _ => (p o).e,
      ty := fun _ => (p o).ty0, n := 0, j := 0, j' := 0, big := fun _ _ => True }
  obtain ⟨M, M', h1, -, h3, h4⟩ := GlobalTheory.T.exists_integralEnd_of_ladic_action_limit C V O dd Y d _ X rfl rfl rfl s hs1
  have hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (un1 (Y.lg i)) = 0
    rw [constantCoeff_uncurry, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.lg_lin i 0 (by simp)]
    simp
  have hex : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (un1 (Y.ex i)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const i
  have hh : MvPowerSeries.constantCoeff X.h = 0 := by
    have := coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl (by
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' _ _ hg']
      rfl) Y.gauge.ax0 0 (by simp)
    simpa using this
  have e1 := teichSelf_double C V dd d d _ _ X (Y.rawSelf (p o)) hlg hex hh rfl rfl rfl M M' h1
  have m1 : ∀ c i, M.mulVec ((p o).e c) i = 1 * (p o).e c i := fun c =>
    teichSelf_eig _ _ ((p o).e_int c) _ _ (hs2 ((p o).ty0 c)) fun K i => by
      simpa only [(p o).e_eig, Pi.smul_apply, smul_eq_mul] using h3 K ((p o).e c) i
  have hk : ∀ o', o' ≠ o → ∀ a K, ∃ n0, ∀ n ≥ n0, V.Ge (K : ℕ) (0 - (p o').em a (s n)) := fun o' ho a =>
    hs3 _ ((p o').em_int a) fun b => hs (o, b) (o', a) fun h => ho (congrArg Prod.fst h).symm
  have m2 : ∀ o', o' ≠ o → ∀ c i, M.mulVec ((p o').e c) i = 0 * (p o').e c i := fun o' ho c =>
    teichSelf_eig _ _ ((p o').e_int c) _ _ (hk o' ho ((p o').ty0 c)) fun K i => by
      simpa only [(p o').e_eig, Pi.smul_apply, smul_eq_mul] using h3 K ((p o').e c) i
  have m3 : ∀ o', o' ≠ o → ∀ c i, M'.mulVec ((p o').e c) i = 0 * (p o').e c i := fun o' ho c =>
    teichSelf_eig _ _ ((p o').e_int c) _ _ (hk o' ho ((p o').ty0 c + (p o').hd)) fun K i => by
      simpa only [(p o').e_eig, Pi.smul_apply, smul_eq_mul, (p o').em_conj] using h4 K ((p o').e c) i
  refine ⟨_, _, e1, fun g c => ?_, fun o' ho g c => ⟨?_, ?_⟩⟩
  · exact (teichSelf_mulVec M (fun r => (p o).gm ((p o).ty0 c) r g) ((p o).e c) _ (m1 c)).trans (one_smul _ _)
  · exact (teichSelf_mulVec M (fun r => (p o').gm ((p o').ty0 c) r g) ((p o').e c) _ (m2 o' ho c)).trans
      (zero_smul _ _)
  · exact (teichSelf_mulVec M' (fun r => (p o').gm ((p o').ty0 c) r g) ((p o').e c) _ (m3 o' ho c)).trans
      (zero_smul _ _)

omit [CharZero C] in
theorem mul_eq_zero_of_range {κ α : Type} [Fintype κ] [Fintype α] {A B : Matrix κ κ C} {u : α → κ → C}
    (hB : ∀ v, ∃ b : α → C, B.mulVec v = ∑ c, b c • u c) (hA : ∀ c, A.mulVec (u c) = 0) : A * B = 0 := by
  classical
  refine Matrix.ext_of_mulVec_single fun j => ?_
  obtain ⟨b, hb⟩ := hB (Pi.single j 1)
  rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_sum, Matrix.zero_mulVec]
  exact Finset.sum_eq_zero fun c _ => by rw [Matrix.mulVec_smul, hA, smul_zero]

omit [CharZero C] in
theorem mul_eq_self_of_range {κ α : Type} [Fintype κ] [Fintype α] {A B : Matrix κ κ C} {u : α → κ → C}
    (hB : ∀ v, ∃ b : α → C, B.mulVec v = ∑ c, b c • u c) (hA : ∀ c, A.mulVec (u c) = u c) : A * B = B := by
  classical
  have := mul_eq_zero_of_range (A := A - 1) hB fun c => by rw [Matrix.sub_mulVec, hA, Matrix.one_mulVec, sub_self]
  rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this

theorem exists_plane [Fintype Orb] (p : ∀ o, SelfData Y d (I0 o)) (hs : SelfSep Y p) (o₀ : Orb)
    (gr : ∀ o, MvPowerSeries (WV fun _ => I0 o) C) (hg : ∀ o, gr o ∈ ExpInt (Y.rawSelf (p o)) V) :
    ∃ F : MvPowerSeries (Fin 2 × Fin dd) C, IntS V F ∧
      MvPowerSeries.subst (fun x : Fin 2 × Fin dd => MvPowerSeries.subst
        (fun i : Fin 2 × Fin dd => ∑ w : WVO fun o (_ : Fin 2) => I0 o, (Y.rawSelf (p w.1)).u w.2.1 w.2.2 i •
          (MvPowerSeries.X w : MvPowerSeries (WVO fun o (_ : Fin 2) => I0 o) C)) (inCol x.1 (un1 (Y.ex x.2))))
        (F * mvExp ((Y.k : C) • ∑ col : Fin 2, inCol col (un1 (Y.B.hL C Y.h Y.w0)))) =
      ∏ o, MvPowerSeries.subst (fun w : WV fun _ => I0 o =>
        (MvPowerSeries.X (⟨o, w⟩ : WVO fun o (_ : Fin 2) => I0 o) : MvPowerSeries (WVO fun o (_ : Fin 2) => I0 o) C))
        (gr o * mvExp (Y.rawSelf (p o)).hRow) := by
  classical
  have hL := GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d _ (p o₀)
  obtain ⟨W, W', hW, hWW, hWv, hWh⟩ := GlobalTheory.T.exists_endomorphism_pair_w0 C V O dd Y d _ (p o₀)
  choose P hP01 hP10 hPid hPk hPr using fun o => GlobalTheory.T.hasGaugeAdjointLieProjectors_selfConjugatePlace C V O dd Y d _ (p o)
  choose E E' hE hEid hEk using exists_sep Y p hs
  obtain ⟨-, -, cmul, czero, -, -, cadj⟩ := GlobalTheory.T.gauge_biadditive_symm_adjoint_integralEnd C V d _ _ (Y.rawSelf (p o₀)) hL
  have hPg : ∀ o g, IsEnd (Y.rawSelf (p o₀)) V (P o g) (P o (1 - g)) := by
    intro o g
    fin_cases g
    · exact hP01 o
    · exact hP10 o
  have hE0 : ∀ o, IsEnd (Y.rawSelf (p o₀)) V (E o) (E' o) := hE
  have hπ : ∀ o g, IntEnd (Y.rawSelf (p o₀)) V (P o g * E o) := fun o g => cmul _ _ (hPg o g).1 (hE0 o).1
  have hr : ∀ o g v, ∃ b : I0 o → C, (P o g * E o).mulVec v = ∑ c, b c • (Y.rawSelf (p o)).u g c := fun o g v => by
    rw [← Matrix.mulVec_mulVec]; exact hPr o g _
  have hWu : ∀ o g c, W.mulVec ((Y.rawSelf (p o)).u g c) =
      (p o).em ((p o).ty0 c) Y.w0 • (Y.rawSelf (p o)).u g c := by
    intro o g c
    funext x
    rw [hWv]
    have h1 := congrFun ((p o).e_eig c Y.w0) x.2
    simp only [linAct, FBChart.rawSelf, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_left_comm, ← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hcore := GlobalTheory.T.sum_hEnd_sub_hEnd_mem_logInt C V d _ _ (Y.rawSelf (p o₀)) hL Orb (fun o g => P o g * E o) W W' hπ hW hWW (by
    intro o g o' g' hne
    have hWπ := cmul _ _ hW.1 (hπ o' g')
    by_cases ho : o' = o
    · subst ho
      have hgg : g' = g := by
        by_contra h
        exact hne ⟨rfl, fin_two_eq_one_sub_of_ne' _ _ h⟩
      subst hgg
      have h1 := cadj _ _ _ _ (hPg o' g') (hπ o' g') hWπ
      rw [mul_eq_self_of_range (hr o' g') (hPid o' g'), ← Matrix.mul_assoc (P o' (1 - g')) W,
        mul_eq_zero_of_range (A := P o' (1 - g') * W) (hr o' g'), (czero _).1, sub_zero] at h1
      · exact h1
      · intro c
        have h2 := hPk o' (1 - g') c
        rw [sub_sub_cancel] at h2
        rw [← Matrix.mulVec_mulVec, hWu, Matrix.mulVec_smul, h2, smul_zero]
    · have h1 := cadj _ _ _ _ (hE0 o) (hπ o g) hWπ
      rw [mul_eq_self_of_range (hr o g) (hEid o g), ← Matrix.mul_assoc (E' o) W,
        mul_eq_zero_of_range (A := E' o * W) (hr o' g'), (czero _).1, sub_zero] at h1
      · exact h1
      · intro c
        rw [← Matrix.mulVec_mulVec, hWu, Matrix.mulVec_smul, (hEk o o' ho g' c).2, smul_zero])
  rw [hWh]
  refine GlobalTheory.T.exists_integralSeries_frame_eq_prod_rows C V d Orb _ _ (fun o => Y.rawSelf (p o)) d _ (Y.rawSelf (p o₀)) hL (fun _ => ⟨rfl, rfl, rfl⟩)
    (fun o g => P o g * E o) W hπ ?_ ?_ hcore gr hg
  · intro o g c
    rw [← Matrix.mulVec_mulVec, hEid, hPid]
  · intro o g o' g' c hne
    rw [← Matrix.mulVec_mulVec]
    by_cases ho : o' = o
    · subst ho
      have hgg : g' = 1 - g := fin_two_eq_one_sub_of_ne' _ _ fun h => hne (by rw [h])
      subst hgg
      rw [hEid, hPk]
    · rw [(hEk o o' ho g' c).1, Matrix.mulVec_zero]

section Glue

open MvPowerSeries

variable {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) {ω : Type} [Fintype ω] (u : ω → Fin 2 × Fin dd → C)

noncomputable def linCol (s : Fin n × Fin dd) : MvPowerSeries (Fin N × ω) C :=
  ∑ x : Fin N × ω, (∑ col : Fin 2, if pl (x.1, col) = s.1 then u x.2 (col, s.2) else 0) • X x

omit [CharZero C] in
theorem cc_linCol (s : Fin n × Fin dd) : constantCoeff (linCol pl u s) = 0 := by
  simp [linCol]

omit [CharZero C] in
theorem linCol_pl (ρ : Fin N) (col : Fin 2) (j : Fin dd) :
    linCol pl u (pl (ρ, col), j) = ∑ w, u w (col, j) • X (ρ, w) := by
  unfold linCol
  rw [Fintype.sum_prod_type, Finset.sum_eq_single ρ]
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp
  · intro ρ' _ h
    simp [h]
  · simp

omit [CharZero C] in
theorem linCol_out (b : Fin n) (hb : ∀ y, pl y ≠ b) (j : Fin dd) : linCol pl u (b, j) = 0 := by
  simp [linCol, hb]

omit [CharZero C] in
theorem subst_zero_of_cc {σ τ : Type} [Finite σ] {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) :
    subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = 0 := by
  ext ν
  have h0 : Van (∅ : Set τ) (subst (fun _ : σ => (0 : MvPowerSeries τ C)) f) :=
    Van.subst Set.univ (fun _ => map_zero _) (fun _ _ ν _ => by simp) (van_univ hf)
  exact h0 ν (by simp)

theorem glue (ex : Pt C 1 dd) (hex : ∀ i, constantCoeff (ex i) = 0) (hl : PS C 1 dd) (hhl : constantCoeff hl = 0)
    (k : C) (F : Fin N → MvPowerSeries (Fin 2 × Fin dd) C) :
    subst (fun s : Fin n × Fin dd => subst (fun j : Fin dd => linCol pl u (s.1, j)) (un1 (ex s.2)))
      ((∏ ρ, subst (fun x : Fin 2 × Fin dd => (X (pl (ρ, x.1), x.2) : PS C n dd)) (F ρ)) *
        FB.expS C (k • ∑ b : Fin n, ev (n := n) ![pt C dd b] hl)) =
    ∏ ρ, subst (fun w : ω => (X (ρ, w) : MvPowerSeries (Fin N × ω) C))
      (subst (fun x : Fin 2 × Fin dd => subst (fun i : Fin 2 × Fin dd => ∑ w, u w i • (X w : MvPowerSeries ω C))
        (inCol x.1 (un1 (ex x.2)))) (F ρ * mvExp (k • ∑ col : Fin 2, inCol col (un1 hl)))) := by
  classical
  set E : Fin n × Fin dd → MvPowerSeries (Fin N × ω) C :=
    fun s => subst (fun j : Fin dd => linCol pl u (s.1, j)) (un1 (ex s.2)) with hE
  set e : Fin 2 × Fin dd → MvPowerSeries ω C := fun x =>
    subst (fun i : Fin 2 × Fin dd => ∑ w, u w i • (X w : MvPowerSeries ω C)) (inCol x.1 (un1 (ex x.2))) with he
  have hex' : ∀ i, constantCoeff (un1 (ex i)) = 0 := fun i => by rw [constantCoeff_uncurry, hex]
  have hl' : constantCoeff (un1 hl) = 0 := by rw [constantCoeff_uncurry, hhl]
  have hL0 : ∀ i : Fin 2 × Fin dd, constantCoeff (∑ w, u w i • (X w : MvPowerSeries ω C)) = 0 := fun i => by simp
  have he1 : ∀ x, e x = subst (fun j => ∑ w, u w (x.1, j) • (X w : MvPowerSeries ω C)) (un1 (ex x.2)) := fun x =>
    teichSelf_subst_inCol _ hL0 _ _
  have he0 : ∀ x, constantCoeff (e x) = 0 := fun x => by
    rw [he1]; exact constantCoeff_subst_zero (fun j => hL0 _) (hex' _)
  have hE0 : ∀ s, constantCoeff (E s) = 0 := fun s =>
    constantCoeff_subst_zero (fun j => cc_linCol pl u _) (hex' _)
  have hES := hasSubst_of_constantCoeff_zero hE0
  have heS := hasSubst_of_constantCoeff_zero he0
  have hRS : ∀ ρ : Fin N, HasSubst (fun w : ω => (X (ρ, w) : MvPowerSeries (Fin N × ω) C)) := fun ρ =>
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hE1 : ∀ ρ (x : Fin 2 × Fin dd), subst (fun w : ω => (X (ρ, w) : MvPowerSeries (Fin N × ω) C)) (e x) =
      E (pl (ρ, x.1), x.2) := by
    intro ρ x
    rw [he1, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun j => hL0 _) (hRS ρ)]
    show _ = subst (fun j : Fin dd => linCol pl u (pl (ρ, x.1), j)) (un1 (ex x.2))
    congr 1
    funext j
    rw [linCol_pl, ← coe_substAlgHom (hRS ρ), map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_smul, coe_substAlgHom, subst_X (hRS ρ)]
  have hcb : ∀ b : Fin n, ev (n := n) ![pt C dd b] hl = subst (fun j => (X (b, j) : PS C n dd)) (un1 hl) := by
    intro b
    rw [ActionLimit.subst_singlePointUncurry _ (fun _ => constantCoeff_X _)]
    unfold ev
    congr 1
    funext q
    rw [Subsingleton.elim q.1 0]
    rfl
  have hc1 : constantCoeff (k • ∑ b : Fin n, ev (n := n) ![pt C dd b] hl) = 0 := by
    rw [constantCoeff_smul, map_sum, Finset.sum_eq_zero, smul_zero]
    intro b _
    rw [hcb]
    exact constantCoeff_subst_zero (fun _ => constantCoeff_X _) hl'
  have hc2 : constantCoeff (k • ∑ col : Fin 2, inCol col (un1 hl)) = 0 := by
    rw [constantCoeff_smul, map_sum, Finset.sum_eq_zero, smul_zero]
    intro b _
    exact constantCoeff_subst_zero (fun _ => constantCoeff_X _) hl'
  have hG0 : ∀ ρ (x : Fin 2 × Fin dd), constantCoeff (E (pl (ρ, x.1), x.2)) = 0 := fun ρ x => hE0 _
  have hR : ∀ ρ, subst (fun w : ω => (X (ρ, w) : MvPowerSeries (Fin N × ω) C))
      (subst e (F ρ * mvExp (k • ∑ col : Fin 2, inCol col (un1 hl)))) =
      subst (fun x : Fin 2 × Fin dd => E (pl (ρ, x.1), x.2)) (F ρ) *
        mvExp (k • ∑ col : Fin 2, subst (fun j => E (pl (ρ, col), j)) (un1 hl)) := by
    intro ρ
    have hS := hasSubst_of_constantCoeff_zero (hG0 ρ)
    rw [subst_comp_subst_apply heS (hRS ρ)]
    simp only [hE1]
    rw [subst_mul hS, subst_mvExp (hG0 ρ) hc2, ← coe_substAlgHom hS, map_smul, map_sum]
    simp only [coe_substAlgHom, teichSelf_subst_inCol _ (hG0 ρ)]
  simp only [hR]
  rw [Finset.prod_mul_distrib, subst_mul hES]
  congr 1
  · rw [← coe_substAlgHom hES, map_prod]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [coe_substAlgHom, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hES]
    simp only [subst_X hES]
  · unfold FB.expS
    rw [← mvExp_eq_subst hc1, subst_mvExp hE0 hc1, ← mvExp_sum]
    · congr 1
      rw [← Finset.smul_sum, ← coe_substAlgHom hES, map_smul, map_sum]
      congr 1
      have h1 : ∀ b : Fin n, substAlgHom hES (ev (n := n) ![pt C dd b] hl) = subst (fun j => E (b, j)) (un1 hl) := by
        intro b
        rw [coe_substAlgHom, hcb,
          subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hES]
        simp only [subst_X hES]
      simp only [h1]
      rw [← Fintype.sum_prod_type' (f := fun ρ col => subst (fun j => E (pl (ρ, col), j)) (un1 hl))]
      symm
      refine Fintype.sum_of_injective pl pl.injective _ _ ?_ fun _ => rfl
      intro b hb
      have hb' : ∀ y, pl y ≠ b := fun y h => hb ⟨y, h⟩
      have h2 : (fun j => E (b, j)) = fun _ => 0 := by
        funext j
        show subst (fun i : Fin dd => linCol pl u (b, i)) (un1 (ex j)) = 0
        simp only [linCol_out pl u b hb']
        exact subst_zero_of_cc (hex' j)
      rw [h2]
      exact subst_zero_of_cc hl'
    · intro ρ
      rw [constantCoeff_smul, map_sum, Finset.sum_eq_zero, smul_zero]
      intro b _
      exact constantCoeff_subst_zero (fun _ => hE0 _) hl'

end Glue

theorem valEqSelf : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) [Fintype Orb] (I0 : Orb → Type) [∀ o, Fintype (I0 o)] (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ), ValEqSelfSt Y p H Ls n := by
  intro C _ _ V O _ _ dd Y d _ Orb _ I0 _ p H Ls n hs N pl P _ Po hQ kind hk S t ht gr hg
  classical
  obtain ⟨co, hco, hQ⟩ := hQ
  have hl0 : MvPowerSeries.constantCoeff (Y.B.hL C Y.h Y.w0) = 0 :=
    ReciprocityTheory.ChartRestriction.G.TB.SCPf.cc_hL Y.B Y.h Y.gauge Y.w0
  set u : (WVO fun o (_ : Fin 2) => I0 o) → Fin 2 × Fin dd → C :=
    fun w => (Y.rawSelf (p w.1)).u w.2.1 w.2.2 with hu
  have hE0 : ∀ s : Fin n × Fin dd, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun j : Fin dd => linCol pl u (s.1, j)) (un1 (Y.ex s.2))) = 0 := fun s =>
    constantCoeff_subst_zero (fun j => cc_linCol pl u _) (by rw [constantCoeff_uncurry, Y.ex_const])
  have hjet := GlobalTheory.T.constantCoeff_derivationPolynomial_eq_jetAt0 C dd n (Y.B.FK C) _ (Ls.cp n) (Ls.uv n) _ _ hE0 co P (by
    intro ℓ hℓ
    refine GlobalTheory.T.invariantDerivations_constant_in_logCoordinates C V O dd Y n _ (linCol pl u) (cc_linCol pl u) _ _ _ ?_
    intro b j
    obtain ⟨ρ, col, hpl, h0, h1⟩ := hco ℓ hℓ
    have h2 : ∀ x, MvPowerSeries.pderiv C x (linCol pl u (b, j)) =
        MvPowerSeries.C (∑ col : Fin 2, if pl (x.1, col) = b then u x.2 (col, j) else 0) := by
      intro x
      unfold linCol
      rw [map_sum, Finset.sum_eq_single x]
      · rw [Derivation.map_smul, MvPowerSeries.pderiv_X_self, MvPowerSeries.smul_eq_C_mul, mul_one]
      · intro y _ hy
        rw [Derivation.map_smul, MvPowerSeries.pderiv_X_of_ne hy, smul_zero]
      · simp
    have h3 : ∀ col', ∑ w, co ℓ (ρ, w) * u w (col', j) = if col' = col then Ls.uv n ℓ j else 0 := by
      intro col'
      have := congrFun h1 (col', j)
      simpa [Finset.sum_apply, hu] using this.symm
    simp only [h2, MvPowerSeries.smul_eq_C_mul, ← map_mul]
    rw [← map_sum, Fintype.sum_prod_type, Finset.sum_eq_single ρ]
    · simp only [Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, h3, ← hpl]
      rw [Finset.sum_eq_single col]
      · by_cases hb : b = pl (ρ, col)
        · simp [hb]
        · simp [hb, Ne.symm hb]
      · intro c _ hc
        simp [hc]
      · simp
    · intro ρ' _ hρ
      simp [h0 ρ' _ hρ]
    · simp)
  rcases isEmpty_or_nonempty Orb with hO | ⟨⟨o₀⟩⟩
  · refine ⟨1, intS_one, ?_⟩
    unfold FBChart.nab nabValN
    rw [hjet, ← hQ, Fintype.prod_empty, Fintype.prod_empty, RF.jetAt0_one, cc_subst hE0, one_mul]
    refine ReciprocityTheory.ChartRestriction.G.TB.SCPf.cc_expS _ ?_
    rw [MvPowerSeries.constantCoeff_smul, map_sum, Finset.sum_eq_zero, smul_zero]
    intro b _
    refine constantCoeff_subst_zero (fun q => ?_) hl0
    rw [Subsingleton.elim q.1 0]
    exact MvPowerSeries.constantCoeff_X _
  have hg' : ∀ o ρ, gr o ρ ∈ ExpInt (Y.rawSelf (p o)) V := fun o ρ => by
    rw [← GlobalTheory.T.integralGerm_eq_gaugedFormalGroupLaw_expIntegral C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d _ (p o)) (H o).cartH (S o) (t o) (ht o)]
    exact hg o ρ
  choose F hF hFe using fun ρ => exists_plane Y p hs o₀ (fun o => gr o ρ) fun o => hg' o ρ
  refine ⟨∏ ρ, MvPowerSeries.subst
    (fun x : Fin 2 × Fin dd => (MvPowerSeries.X (pl (ρ, x.1), x.2) : PS C n dd)) (F ρ),
    intS_prod _ fun ρ => intS_subst (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X _) (hF ρ), ?_⟩
  unfold FBChart.nab nabValN
  rw [hjet, ← hQ, glue pl u Y.ex Y.ex_const _ hl0]
  simp only [hu, hFe, GlobalTheory.T.admissibleRows_value_eq_rowGauge C V d _ _ _ (H _) N _ _ (hk _)]
  rw [← GlobalTheory.T.jetAt0_prod_subst_disjoint_variables C Orb (fun o => Fin N × WV fun _ => I0 o) (Fin N × WVO fun o (_ : Fin 2) => I0 o)
    (fun o x => (x.1, ⟨o, x.2⟩)) (by
      rintro ⟨o, ρ, w⟩ ⟨o', ρ', w'⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      rfl)]
  congr 1
  have hR : ∀ ρ : Fin N, MvPowerSeries.HasSubst (fun w : WVO fun o (_ : Fin 2) => I0 o =>
      (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WVO fun o (_ : Fin 2) => I0 o) C)) := fun ρ =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  have hT : ∀ o, MvPowerSeries.HasSubst (fun x : Fin N × WV fun _ => I0 o =>
      (MvPowerSeries.X (x.1, ⟨o, x.2⟩) : MvPowerSeries (Fin N × WVO fun o (_ : Fin 2) => I0 o) C)) := fun o =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  have hrow : ∀ o ρ, rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.rawSelf (p o)).hRow) =
      rowCopy ρ (gr o ρ * mvExp (Y.rawSelf (p o)).hRow) := by
    intro o ρ
    have h0 : MvPowerSeries.constantCoeff (Y.rawSelf (p o)).hRow = 0 := (H o).axes 0 (Or.inl (by simp))
    unfold rowCopy
    rw [MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _),
      subst_mvExp (fun _ => MvPowerSeries.constantCoeff_X _) h0]
  simp only [hrow]
  simp only [← MvPowerSeries.coe_substAlgHom (hR _), ← MvPowerSeries.coe_substAlgHom (hT _), map_prod]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun o _ => Finset.prod_congr rfl fun ρ _ => ?_
  unfold rowCopy
  rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (hR ρ),
    MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (hT o)]
  simp only [MvPowerSeries.subst_X (hR ρ), MvPowerSeries.subst_X (hT o)]

end GlobalTheory.ValSelf
