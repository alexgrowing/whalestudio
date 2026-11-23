import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.HermRead

open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

section Lin

variable {C : Type} [Field C] {d : ℕ} {σ : Type}

theorem mv_sum (A : Matrix (Fin d) (Fin d) C) {β : Type} (s : Finset β) (x : β → Fin d → MvPowerSeries σ C) :
    mv A (∑ b ∈ s, x b) = ∑ b ∈ s, mv A (x b) := by
  funext e
  simp only [mv, Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_comm

theorem mv_mv (A A' : Matrix (Fin d) (Fin d) C) (w : Fin d → MvPowerSeries σ C) :
    mv A (mv A' w) = mv (A * A') w := by
  funext e
  simp only [mv, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem add_mv (A A' : Matrix (Fin d) (Fin d) C) (w : Fin d → MvPowerSeries σ C) :
    mv (A + A') w = mv A w + mv A' w := by
  funext e
  simp only [mv, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]

end Lin

theorem map_sum_of_additive {M Q : Type} [AddCommMonoid M] [AddCommGroup Q] (p : M → Prop) (h0 : p 0)
    (hp : ∀ x y, p x → p y → p (x + y)) (f : M → Q) (hf : ∀ x y, p x → p y → f (x + y) = f x + f y)
    {β : Type} (s : Finset β) (x : β → M) (hx : ∀ b, p (x b)) :
    p (∑ b ∈ s, x b) ∧ f (∑ b ∈ s, x b) = ∑ b ∈ s, f (x b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using h0, ?_⟩
    have := hf 0 0 h0 h0
    rw [add_zero] at this
    simpa using this
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact ⟨hp _ _ (hx b) ih.1, by rw [hf _ _ (hx b) ih.1, ih.2]⟩

theorem finSt_of (hAdd : AddSt) (hAct : ActSt) (hUnit : UnitSt) (hBi : BiaddSt) : FinSt := by
  intro C _ _ v d R _ _ O _ _ B hB h hg σ _ κ _ w hw w0 n a ι _ e t ht
  obtain ⟨hU0, hUadd, hUneg, -⟩ := hUnit C v σ
  obtain ⟨hI0, -, hIadd⟩ := hAdd C v d (fglOf hB) σ
  have hIact := fun c => (hAct C v d R O B hB σ c).2
  have hbi := hBi C v d R O B hB h hg σ
  let U : AddSubgroup (MvPowerSeries σ C) :=
    { carrier := {s | LogUnit v s}
      add_mem' := fun {s t} hs ht => hUadd s t hs ht
      zero_mem' := hU0
      neg_mem' := fun {s} hs => hUneg s hs }
  let π := QuotientAddGroup.mk' U
  have key : ∀ s, π s = 0 ↔ LogUnit v s := fun s => QuotientAddGroup.eq_zero_iff s
  have h1 : ∀ z, IntLog (fglOf hB) z → ∀ x y, IntLog (fglOf hB) x → IntLog (fglOf hB) y →
      π (pairSer (fglOf hB) h (x + y) z) = π (pairSer (fglOf hB) h x z) + π (pairSer (fglOf hB) h y z) := by
    intro z hz x y hx hy
    have := (key _).2 (hbi x y z hx hy hz).2.1
    rw [map_sub, map_add, sub_eq_zero] at this
    exact this.symm
  have h2 : ∀ z, IntLog (fglOf hB) z → ∀ x y, IntLog (fglOf hB) x → IntLog (fglOf hB) y →
      π (pairSer (fglOf hB) h z (x + y)) = π (pairSer (fglOf hB) h z x) + π (pairSer (fglOf hB) h z y) := by
    intro z hz x y hx hy
    have := (key _).2 (hbi x y z hx hy hz).2.2.1
    rw [map_sub, map_add, sub_eq_zero] at this
    exact this.symm
  have h3 : ∀ (c : O) x z, IntLog (fglOf hB) x → IntLog (fglOf hB) z →
      π (pairSer (fglOf hB) h (mv (dAct C B c) x) z) =
        π (pairSer (fglOf hB) h x (mv (dAct C B (star c)) z)) := by
    intro c x z hx hz
    have := (key _).2 ((hbi x x z hx hx hz).2.2.2 c)
    rwa [map_sub, sub_eq_zero] at this
  let F : κ → κ → O →+ MvPowerSeries σ C ⧸ U := fun b b' =>
    AddMonoidHom.mk' (fun c => π (pairSer (fglOf hB) h (w b) (mv (dAct C B c) (w b')))) fun c c' => by
      rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add, add_mv]
      exact h2 _ (hw b) _ _ (hIact _ _ (hw b')) (hIact _ _ (hw b'))
  have hF : ∀ b b' c, F b b' c = π (pairSer (fglOf hB) h (w b) (mv (dAct C B c) (w b'))) := fun _ _ _ => rfl
  have hj : ∀ j, π (pairSer (fglOf hB) h (∑ b, mv (dAct C B (a b j)) (w b))
      (mv (dAct C B w0) (∑ b, mv (dAct C B (a b j)) (w b)))) =
        ∑ b, ∑ b', F b b' (star (a b j) * a b' j * w0) := by
    intro j
    have hy : IntLog (fglOf hB) (∑ b, mv (dAct C B (a b j)) (w b)) :=
      (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun _ => (0 : ℤ)) (by simp) Finset.univ _
        fun b => hIact _ _ (hw b)).1
    have hz := hIact w0 _ hy
    generalize hzz : mv (dAct C B w0) (∑ b, mv (dAct C B (a b j)) (w b)) = z at hz
    refine (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun x => π (pairSer (fglOf hB) h x z)) (h1 _ hz)
      Finset.univ _ fun b => hIact (a b j) _ (hw b)).2.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [h3 _ _ _ (hw b) hz, ← hzz, mv_mv, mv_sum, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul]
    refine (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun x => π (pairSer (fglOf hB) h (w b) x))
      (h2 _ (hw b)) Finset.univ _ fun b' => hIact _ _ (hIact _ _ (hw b'))).2.trans
      (Finset.sum_congr rfl fun b' _ => ?_)
    rw [hF, mv_mv, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul, mul_right_comm]
  rw [← key, map_sub, sub_eq_zero, map_sum, Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [← map_sum, ← Finset.sum_mul, ht, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul, map_zsmul, hF]

end GlobalTheory.IsoTriv.HermRead
