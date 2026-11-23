import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

theorem subst_comb_expPt {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d n : ℕ} {σ κ : Type} [Fintype κ]
    (G : LogFGL v d) (w : κ → Fin d → MvPowerSeries σ C) (hw : ∀ b i, constantCoeff (w b i) = 0)
    (F : MvPowerSeries (Fin n × Fin d) C) (M : κ → Fin n → Matrix (Fin d) (Fin d) C) :
    (subst (fun q : Fin n × Fin d => ∑ i : κ × Fin d, M i.1 q.1 q.2 i.2 • w i.1 i.2)
      (subst (fun q : Fin n × Fin d => expPt G (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2) F :
        MvPowerSeries (Fin n × Fin d) C) : MvPowerSeries σ C) =
      subst (fun q : Fin n × Fin d => expPt G (∑ b, mv (M b q.1) (w b)) q.2) F := by
  have ht : HasSubst (fun q : Fin n × Fin d => ∑ i : κ × Fin d, M i.1 q.1 q.2 i.2 • w i.1 i.2) :=
    hasSubst_of_constantCoeff_zero (by intro q; simp [hw])
  have hs : HasSubst (fun q : Fin n × Fin d =>
      expPt G (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2) :=
    hasSubst_of_constantCoeff_zero (fun q => cc_expPt G (by simp) q.2)
  refine (subst_comp_subst_apply hs ht F).trans ?_
  congr 1
  funext q
  refine (subst_expPt G ht (by simp) q.2).trans ?_
  congr 1
  funext e
  refine (subst_X ht _).trans ?_
  simp [mv, Fintype.sum_prod_type, Finset.sum_apply]

theorem le_v_pow_mul_int {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {p : ℕ} (hp : v (p : C) = 1)
    (N : ℕ) (z : ℤ) : ((N : ℝ) : WithTop ℝ) ≤ v ((((p : ℤ) ^ N * z : ℤ)) : C) := by
  have hz : 0 ≤ v (z : C) := intCast_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v) z
  push_cast
  rw [v.map_mul, v.map_pow, hp]
  calc ((N : ℕ) : WithTop ℝ) = N • (1 : WithTop ℝ) := by simp
    _ ≤ _ := le_add_of_nonneg_right hz

theorem limFrame : AddSt → ActSt → UnitSt → BiaddSt → FrameSt → FinSt → ContSt → LimFrameSt := by
  classical
  intro _ hAct hUnit hBi hFr hFin hCont C _ _ v p hp d R _ _ O _ _ _ B hB h hh σ _ κ _ w hw w0 n A a hA hiso α
  have hw0 : ∀ b i, constantCoeff (w b i) = 0 := fun b => (hw b).1
  have mono : ∀ {M N : ℕ} {x : WithTop ℝ}, M ≤ N → ((N : ℝ) : WithTop ℝ) ≤ x → ((M : ℝ) : WithTop ℝ) ≤ x :=
    fun hMN hx => le_trans (WithTop.coe_le_coe.2 (Nat.cast_le.2 hMN)) hx
  have zle : ∀ {N : ℕ} {x : C}, ((N : ℝ) : WithTop ℝ) ≤ v x → IsIntV v x := fun hx => by
    have := mono (Nat.zero_le _) hx
    simpa [IsIntV] using this
  have hD : ∀ (x : O) i j, IsIntV v (dAct C B x i j) := fun x i j => hB.2.1 x i _
  have hAi : ∀ b j e e', IsIntV v (A b j e e') := fun b j e e' => by
    have := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem (zle (hA 0 b j e e')) (hD (a 0 b j) e e')
    rw [sub_add_cancel] at this
    exact this
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := ℤ) (M := O)
  let g : κ × κ × Fin m → MvPowerSeries σ C := fun i =>
    pairSer (fglOf hB) h (w i.1) (mv (dAct C B (e i.2.2)) (w i.2.1))
  have hg0 : ∀ i, constantCoeff (g i) = 0 := fun i =>
    (hBi C v d R O B hB h hh σ (w i.1) (w i.1) _ (hw _) (hw _)
      ((hAct C v d R O B hB σ (e i.2.2)).2 _ (hw i.2.1))).1
  obtain ⟨N₀, hN₀⟩ := hCont C v (Fin n × Fin d) σ (κ × Fin d)
    (subst (fun q : Fin n × Fin d => expPt (fglOf hB) (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2)
      (frameSer B h w0 n)) (fun i => w i.1 i.2) (fun i => hw0 _ _) α
  choose N₁ hN₁ using fun γ => hCont C v Unit σ (κ × κ × Fin m) (PowerSeries.exp C) g hg0 γ
  obtain ⟨N, hN0, hN1⟩ : ∃ N : ℕ, N₀ ≤ N ∧ ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α, N₁ x.2 ≤ N :=
    ⟨max N₀ ((Finset.HasAntidiagonal.antidiagonal α).sup fun x => N₁ x.2), le_max_left _ _,
      fun x hx => le_trans (Finset.le_sup (f := fun x => N₁ x.2) hx) (le_max_right _ _)⟩
  have hdec : ∀ b b', ∃ nn : Fin m → ℤ,
      (∑ j, star (a N b j) * a N b' j) * w0 = ∑ i, ((p : ℤ) ^ N * nn i) • e i := fun b b' => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hiso N b b')
    obtain ⟨nn, hnn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ (v := e) (x := c * w0)).1
      (by rw [he]; exact Submodule.mem_top)
    refine ⟨nn, ?_⟩
    rw [hc, mul_assoc, ← hnn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zsmul_eq_mul, mul_assoc]
  choose nn hnn using hdec
  have hU := hFin C v d R O B hB h hh σ κ w hw w0 n (a N) (Fin m) e (fun b b' i => (p : ℤ) ^ N * nn b b' i) hnn
  have hF := (hFr C v d R O B hB h hh w0 n).2.2 σ (fun j => ∑ b, mv (dAct C B (a N b j)) (w b))
    (fun j i => by simp [Finset.sum_apply, mv, hw0])
  let s : κ × κ × Fin m → C := fun i => (((p : ℤ) ^ N * nn i.1 i.2.1 i.2.2 : ℤ) : C)
  have hT : ∑ b, ∑ b', ∑ i, (((p : ℤ) ^ N * nn b b' i : ℤ) : C) •
      pairSer (fglOf hB) h (w b) (mv (dAct C B (e i)) (w b')) = ∑ i, s i • g i := by
    simp only [Fintype.sum_prod_type, s, g]
  rw [hT] at hU
  have hT0 : constantCoeff (∑ i, s i • g i) = 0 := by simp [hg0]
  obtain ⟨hz, -, -, hmul, -⟩ := hUnit C v σ
  have hprod := hmul _ _ hU.1 hT0
  rw [sub_add_cancel, ← hF] at hprod
  have h1 := hN₀ (fun q i => A i.1 q.1 q.2 i.2) (fun q i => dAct C B (a N i.1 q.1) q.2 i.2)
    (fun q i => hAi _ _ _ _) (fun q i => hD _ _ _) (fun q i => mono hN0 (hA N _ _ _ _))
  rw [subst_comb_expPt (fglOf hB) w hw0 _ A,
    subst_comb_expPt (fglOf hB) w hw0 _ (fun b j => dAct C B (a N b j)), hprod] at h1
  have h2 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α,
      IsIntV v (coeff x.2 (PowerSeries.subst (∑ i, s i • g i) (PowerSeries.exp C))) := fun x hx => by
    have h3 := hN₁ x.2 (fun _ => s) (fun _ _ => 0) (fun _ i => zle (le_v_pow_mul_int hp N _))
      (fun _ _ => by simp [IsIntV]) (fun _ i => by
        rw [sub_zero]; exact mono (hN1 x hx) (le_v_pow_mul_int hp N _))
    simp only [zero_smul, Finset.sum_const_zero] at h3
    have h4 := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem h3 (hz.2 x.2)
    have h5 : ∀ y z : C, y - z + z ∈ ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v → IsIntV v y := fun y z hyz => by
      rw [sub_add_cancel] at hyz
      exact hyz
    exact h5 _ _ h4
  rw [coeff_mul] at h1
  have h6 := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem h1
    ((ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).sum_mem fun x hx =>
      (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).mul_mem (hU.2 x.1) (h2 x hx))
  rw [sub_add_cancel] at h6
  exact h6

end GlobalTheory.IsoTriv
