import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSemilinearRankNullityModMaxIdealStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainStepKernelRankLeModMaxIdealStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IndependentModFirstCoeffChainLastStepStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PairingKernelLeOfSaturatedSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsUnimodularMulEqNegOfIndependentModMaximalStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffLeafGaugeSubMainTermEqZeroOnFirstAxisStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LeafCoordinateWeightNonnegOfAdaptedChainDataStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ZetaSeriesLeafMainTermCurveSystemStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightGaugeSubMainTermLeafStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeSubMainTermIntegralLowBidegreeStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataAdaptedChainDataStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

open Formalism.BaseCaseIdentities (Data Kn s0)

noncomputable section

namespace GlobalTheory.MainTerm

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem mm_neg_iff {x : C} : V.MM (-x) ↔ V.MM x := by
  unfold VF.MM
  rw [V.v.map_neg]

theorem chain_rank (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (hb : X.big g a)
    (i : ℕ) (S : Sys (X.G g)) {Z : Type} (D : Data C Z (I g)) (h : Adapted S D a i)
    (N : ℕ) (em : Fin N ↪ I g) (hem : ∀ δ, D.lev (em δ) = 0) (s : ℕ) (hs : s < Kn i) :
    ∃ (m : ℕ) (cc : Fin m ↪ Fin N), N ≤ m + s * X.j' ∧
      IndepMod V (fun δ c => if D.lev c = s then chainMat D s c (em (cc δ)) else 0) := by
  haveI := X.algClosed
  induction s with
  | zero =>
    refine ⟨N, Function.Embedding.refl _, by omega, fun co _ hco ν => ?_⟩
    have := hco (em ν)
    simpa [hem, chainMat_zero] using this
  | succ s ih =>
    obtain ⟨m, cc, hm, hI⟩ := ih (by omega)
    have hsK : s < Kn D.i := by rw [h.2.2.1]; omega
    obtain ⟨m', cc', hm', hI'⟩ := GlobalTheory.T.powerSemilinear_rank_nullity_mod_maxIdeal C V (I g) m X.j' (V.l ^ 2)
      (Nat.one_le_pow _ _ V.l_prime.pos)
      (fun δ c => if D.lev c = s + 1 then chainMat D (s + 1) c (em (cc δ)) else 0)
      (by
        intro δ c
        split_ifs
        · exact h.chainMat_int _ _ _
        · exact VF.Ge.zero 0)
      (by
        intro N' x hx hxI hxM
        refine GlobalTheory.T.chainStep_kernel_rank_le_mod_maxIdeal C V d I J X hA g a hb i S Z D h s hs m
          (fun δ c => chainMat D s c (em (cc δ))) (fun δ c => h.chainMat_int _ _ _) hI N' x hx hxI ?_
        intro ν e he
        have := hxM ν e
        simpa [he, chainMat_succ, hsK, h.2.1] using this)
    exact ⟨m', cc'.trans cc, by rw [Nat.succ_mul]; omega, hI'⟩

theorem mainVec_rank (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (hb : X.big g a)
    (i : ℕ) (S : Sys (X.G g)) {Z : Type} (D : Data C Z (I g)) (h : Adapted S D a i)
    (N : ℕ) (em : Fin N ↪ I g) (hem : ∀ δ, D.lev (em δ) = 0) :
    ∃ (m : ℕ) (cc : Fin m ↪ Fin N), N ≤ m + s0 i * X.j' ∧
      IndepMod V (fun δ => mainVec S D (em (cc δ))) := by
  have hi : Odd i := h.2.2.1 ▸ D.i_odd
  obtain ⟨m, cc, hm, hI⟩ := chain_rank X hA g a hb i S D h N em hem (s0 i) (chainStartIndex_lt_chainLength_of_odd hi)
  refine ⟨m, cc, hm, fun co hco hM => ?_⟩
  refine GlobalTheory.T.independentMod_firstCoeff_chainLastStep C V d I J X hA g a hb i S Z D h (s0 i) (chainStartIndex_lt_chainLength_of_odd hi) m
    (fun δ c => chainMat D (s0 i) c (em (cc δ))) (fun δ c => h.chainMat_int _ _ _) hI co hco ?_
  intro κ
  have h1 := hM κ
  simp only [mainVec, h.2.2.1, h.2.1, chainStartIndex_lt_chainLength_of_odd hi, and_true] at h1
  rcases neg_one_pow_eq_or C (s0 i + 1) with h2 | h2
  · simpa [h2] using h1
  · rw [← mm_neg_iff]
    simpa [h2] using h1

theorem not_big_add_odd (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d)
    (hb : X.big g a) {i : ℕ} (hi : Odd i) : ¬ X.big g (a + (i : ZMod d)) := by
  have hpar : Even (a + (i : ZMod d)).val ↔ ¬ Even a.val := by
    obtain ⟨e, he⟩ := hA.1
    have h2 : 2 ∣ d := ⟨e, by omega⟩
    have h3 : (a + (i : ZMod d)).val % 2 = (a.val + i) % 2 := by
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ h2, Nat.add_mod,
        Nat.mod_mod_of_dvd _ h2, ← Nat.add_mod]
    obtain ⟨k, rfl⟩ := hi
    simp only [Nat.even_iff]
    omega
  have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
  have hg : g = 0 ∨ g = 1 := by omega
  rcases hg with rfl | rfl
  · rw [hA.2, hpar, not_not]; exact (hA.2 a).1 hb
  · rw [h1, not_not, hA.2, hpar, ← hA.2]; exact (h1 a).1 hb

theorem both (X : RowData C V d I J) (hA : X.Alt) (h5 : 5 ≤ V.l) (g : Fin 2) (a : ZMod d)
    (hb : X.big g a) (i : ℕ) (hi : Odd i) (hid : i < d) (U : Fin X.n → I g → C)
    (U' : Fin X.n → I (1 - g) → C) (hU : X.SatIn g a U)
    (hU' : X.SatIn (1 - g) (a + (i : ZMod d)) U') :
    ∃ (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
      X.MConcl g a i U U' n0 e v' Φ ∧ X.CurveSystemVanishing g a i n0 e v' Φ ∧
        (i = 1 → X.MPlusConcl g a n0 e v' Φ) := by
  haveI := X.algClosed
  haveI := X.charZero
  obtain ⟨S, N1, D, hv, hl, hDi, hal, hty, hN1, A, hAint, hAeq⟩ :=
    GlobalTheory.T.rowData_adaptedChainData C V d I J X hA g a hb i hi hid U hU
  have h : Adapted S D a i := ⟨hv, hl, hDi, hal, hty⟩
  obtain ⟨m, c1, hm, hI1⟩ := mainVec_rank X hA g a hb i S D h N1 ⟨D.ι, D.ι_inj⟩ D.ι_lev
  have hΨint : ∀ c0 (u : I (1 - g) → C), (∀ k, V.Ge 0 (u k)) →
      V.Ge 0 (∑ κ : J g, ∑ k : I (1 - g), mainVec S D c0 κ * X.pair g κ k * u k) :=
    fun c0 u hu => VF.Ge.sum fun κ _ => VF.Ge.sum fun k _ =>
      ((h.mainVec_int c0 κ).mul_int (X.pair_int g κ k)).mul_int (hu k)
  obtain ⟨n0, c2, hn0, hI2⟩ := GlobalTheory.T.powerSemilinear_rank_nullity_mod_maxIdeal C V (Fin X.n) m X.j 1 le_rfl
    (fun δ b => ∑ κ : J g, ∑ k : I (1 - g), mainVec S D (D.ι (c1 δ)) κ * X.pair g κ k * U' b k)
    (fun δ b => hΨint _ _ (hU'.1.1 b))
    (by
      intro N x hx hxI hxM
      refine GlobalTheory.T.pairing_kernel_le_of_saturated_submodule C V d I J X g _ (not_big_add_odd X hA g a hb hi) U' hU' N
        (fun ν κ => ∑ δ, x ν δ * mainVec S D (D.ι (c1 δ)) κ)
        (fun ν κ => VF.Ge.sum fun δ _ => (hx ν δ).mul_int (h.mainVec_int _ _)) ?_ ?_ ?_
      · intro ν κ hκ
        simp [h.mainVec_pure _ κ hκ]
      · intro co hco hM
        refine hxI co hco (hI1 (fun δ => ∑ ν, co ν * x ν δ)
          (fun δ => VF.Ge.sum fun ν _ => (hco ν).mul_int (hx ν δ)) fun κ => ?_)
        convert hM κ using 1
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      · intro ν b
        convert hxM ν b using 1
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc, pow_one]
        rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
        refine Finset.sum_congr rfl fun κ _ => Finset.sum_comm)
  let em : Fin n0 ↪ I g := (c2.trans c1).trans ⟨D.ι, D.ι_inj⟩
  have hem : ∀ δ, D.lev (em δ) = 0 := fun δ => D.ι_lev _
  have hK : 0 < Kn i := by rw [Kn_eq hi]; omega
  have hemty : ∀ δ, (X.G g).ty (Sum.inl (em δ)) = a := fun δ => by
    rw [hty _ (by rw [hem]; exact hK), hem]; simp
  have hemal : ∀ δ x, S.al (em δ) 1 x = 0 := fun δ x =>
    h.al_one (D.pure_good _ (by rw [hem, hDi]; exact hK)) x
  obtain ⟨hn0n, Y, hYint, hYdet, hYΦ⟩ := GlobalTheory.T.exists_unimodular_mul_eq_neg_of_independent_mod_maximal C V X.n n0
    (fun b c => ∑ κ : J g, ∑ k : I (1 - g), mainVec S D (em c) κ * X.pair g κ k * U' b k)
    (fun b c => hΨint _ _ (hU'.1.1 b)) hI2
  let v' : Fin X.n → I (1 - g) → C := fun b x => ∑ b', Y b b' * U' b' x
  have hv'int : ∀ b k, V.Ge 0 (v' b k) := fun b k =>
    VF.Ge.sum fun b' _ => (hYint b b').mul_int (hU'.1.1 b' k)
  have hv'ty : ∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0 :=
    fun b k hk => by simp [v', hU'.2 _ k hk]
  have hety : ∀ c x, (X.G g).ty (Sum.inl x) ≠ a → S.tan (em c) x = 0 := fun c x hx =>
    tan_pure S _ x (by rw [hemty]; exact hx)
  have hS0 : ∀ g', Nonempty (Sys (X.G g')) := fun g' => by
    obtain ⟨S', -⟩ := sysExists (X.G g') (fun c x => if c = x then 1 else 0)
      (by intro c x; split_ifs; exacts [VF.Ge.one, VF.Ge.zero 0])
      (by
        intro c x hx
        rw [if_neg]
        rintro rfl
        exact hx rfl)
      (by
        have : (Matrix.of fun c x : I g' => if c = x then (1 : C) else 0) = 1 := by
          ext c x; simp [Matrix.one_apply]
        rw [this, Matrix.det_one, V.v.map_one])
    exact ⟨S'⟩
  obtain ⟨SS, rfl⟩ : ∃ SS : ∀ g', Sys (X.G g'), SS g = S :=
    ⟨Function.update (fun g' => (hS0 g').some) g S, by simp⟩
  choose t ht using fun g' => (tExistsUnique (X.G g') (SS g')).exists
  have hζ := GlobalTheory.T.zetaSeries_leaf_mainTerm_curveSystem C V d (I g) (J g) (X.G g) (SS g) _ D a i h hid (t g) (ht g) n0 em hem
  refine ⟨n0, fun δ => (SS g).tan (em δ), v',
    fun b c => ∑ κ : J g, ∑ k : I (1 - g), mainVec (SS g) D (em c) κ * X.pair g κ k * v' b k,
    ⟨⟨?_, hn0n⟩, isSat_tan _ em, ⟨fun c => A (c1 (c2 c)), fun c b => hAint _ b, fun c x => ?_⟩,
      ⟨Y, hYint, hYdet, fun b x => rfl⟩, fun b c => hΨint _ _ (hv'int b), fun b c hb => ?_, ?_,
      fun μ hμ => GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis C V d I J X g a i _ _ _ _ _ μ hμ⟩,
    ⟨SS g, t g, em, fun c => mainVec (SS g) D (em c), ht g, fun c => rfl, hemal,
      fun c κ => h.mainVec_int _ _, fun b c => rfl, hζ⟩, ?_⟩
  · have h1 := two_mul_chainStartIndex_add_one_of_odd hi
    rw [Kn_eq hi] at hN1
    have h2 : (i + 1) * X.j' = (s0 i + 1 + 1) * X.j' + s0 i * X.j' := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  · exact ((SS g).cur_zero_inl _ x).symm.trans (hAeq _ x)
  · rw [← hYΦ b c hb]
    simp only [v', Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ (α := Fin X.n))]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · exact GlobalTheory.T.weight_gauge_sub_mainTerm_leaf C V d I J X hA h5 g a i hi hid SS t ht n0 X.n _ v'
      (fun c => mainVec (SS g) D (em c)) hety hv'int hv'ty
      (GlobalTheory.T.leafCoordinate_weight_nonneg_of_adaptedChainData C V d (I g) (J g) (X.G g) (SS g) _ D a i h (t g) (ht g) n0 em hem) hζ
  · rintro rfl
    simp only [fun c => funext (h.mainVec_level_one (hem c))]
    exact GlobalTheory.T.gauge_sub_mainTerm_integral_lowBidegree C V d I J X hA hid g a SS t ht n0 em v' hemty hemal hv'int hv'ty

theorem main : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.LemmaM ∧ X.LemmaMPlus := by
  intro C _ V d _ I J _ _ X
  constructor
  · intro hA h5 g a hb i hi hid U U' hU hU'
    obtain ⟨n0, e, v', Φ, h1, h2, -⟩ := both X hA h5 g a hb i hi hid U U' hU hU'
    exact ⟨n0, e, v', Φ, h1, h2⟩
  · intro hA h5 hd g a hb U U' hU hU'
    obtain ⟨n0, e, v', Φ, h1, h2, h3⟩ := both X hA h5 g a hb 1 odd_one hd U U' hU hU'
    exact ⟨n0, e, v', Φ, h1, h2, h3 rfl⟩

end GlobalTheory.MainTerm
