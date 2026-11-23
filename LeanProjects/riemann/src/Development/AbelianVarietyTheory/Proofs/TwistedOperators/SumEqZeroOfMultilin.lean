import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteReproducingOfSubmodule
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConnectionLinear
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {M : Vol G} {t : T}

theorem conAt_zero (hM : M.Is t) (Φ : SchDown G t) (h : Pts G) (j : ℕ) (hj : Even j) (hm : ¬ (Even D.R.m ∧ j + 2 ≤ D.R.m)) :
    conAt W hM Φ h j = 0 := by
  unfold conAt
  split_ifs with h1 h2
  · exfalso; apply hm; refine ⟨?_, by omega⟩; rw [← h1]; simpa [Nat.even_add] using hj
  · exfalso; apply hm; refine ⟨?_, by omega⟩; rw [← h2]; obtain ⟨r, hr⟩ := hj; exact ⟨r + ((D.R.m - 4 - j) / 2 + 1) + 1, by omega⟩
  · exact dif_neg h2

theorem conAt_local (hM : M.Is t) (Φ Φ' : SchDown G t) (h : Pts G) (j : ℕ)
    (hΦ : ∀ a : Fin D.R.m, ((a : ℕ) = j ∨ (a : ℕ) = j + 1) → Φ a = Φ' a) : conAt W hM Φ h j = conAt W hM Φ' h j := by
  have key : ∀ (a : ℕ) (ha : a < D.R.m), (a = j ∨ a = j + 1) → Φ ⟨a, ha⟩ = Φ' ⟨a, ha⟩ := fun a ha e => hΦ ⟨a, ha⟩ e
  unfold conAt
  simp (disch := simp) only [key]

theorem sum_eq_zero_of_multilin {ι I : Type} [Fintype ι] [dI : DecidableEq ι] {Y : ι → Type} (V : ∀ j, Submodule ℂ (Y j → ℂ))
    (E : (∀ j, Y j → ℂ) → ℂ)
    (hE : ∀ Φ : ∀ j, Y j → ℂ, (∀ j, Φ j ∈ V j) → ∀ a (φ φ' : Y a → ℂ) (c : ℂ), φ ∈ V a → φ' ∈ V a →
      E (Function.update Φ a (c • φ + φ')) = c * E (Function.update Φ a φ) + E (Function.update Φ a φ'))
    (S : Finset I) (x : I → ℂ) (Φ : I → ∀ j, Y j → ℂ) (hΦ : ∀ i ∈ S, ∀ j, Φ i j ∈ V j)
    (h0 : ∀ v : ∀ j, Y j, ∑ i ∈ S, x i * ∏ j, Φ i j (v j) = 0) : ∑ i ∈ S, x i * E (Φ i) = 0 := by
  have coe_upd : ∀ (m : ∀ j, V j) (a : ι) (p : V a),
      (fun j => ((Function.update m a p j : V j) : Y j → ℂ)) = Function.update (fun j => (m j : Y j → ℂ)) a (p : Y a → ℂ) :=
    fun m a p => funext fun j => Function.apply_update (fun j (z : V j) => (z : Y j → ℂ)) m a p j
  let Mm : MultilinearMap ℂ (fun j => V j) ℂ :=
    { toFun := fun m => E fun j => (m j : Y j → ℂ)
      map_update_add' := by
        intro inst m a p q
        obtain rfl : inst = dI := Subsingleton.elim _ _
        simp only [coe_upd, Submodule.coe_add]
        have := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a p q 1 p.2 q.2
        rw [one_smul, one_mul] at this
        exact this
      map_update_smul' := by
        intro inst m a c p
        obtain rfl : inst = dI := Subsingleton.elim _ _
        simp only [coe_upd, Submodule.coe_smul, smul_eq_mul]
        have := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a p 0 c p.2 (V a).zero_mem
        rw [add_zero] at this
        rw [this]
        have h00 := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a 0 0 1 (V a).zero_mem (V a).zero_mem
        simp only [smul_zero, add_zero, one_mul] at h00
        have hz : E (Function.update (fun j => (m j : Y j → ℂ)) a 0) = 0 := by linear_combination -h00
        rw [hz, add_zero] }
  classical
  let φ : I → ∀ j, V j := fun i j => if hi : i ∈ S then ⟨Φ i j, hΦ i hi j⟩ else 0
  let τ : I →₀ ℂ := Finsupp.onFinset S (fun i => if i ∈ S then x i else 0) (fun i hi => by by_contra h; simp [h] at hi)
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq V Mm τ 0 φ φ (fun z => by
    rw [Finsupp.sum_zero_index, Finsupp.onFinset_sum _ (fun _ => zero_mul _)]
    rw [← h0 z]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [φ, hi])
  rw [Finsupp.sum_zero_index] at key
  dsimp only [τ] at key
  rw [Finsupp.onFinset_sum _ (g := fun a c => c • Mm (φ a)) (fun _ => zero_smul _ _)] at key
  rw [← key]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [φ, hi, Mm]
end GlobalTheory.ConnectionLinear

namespace GlobalTheory.ConnectionLinear

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def PositionLinAt (j off : ℕ) : Prop :=
  ∀ t (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (Φ : SchDown ch.G t) (a : Fin D.R.m), (a : ℕ) = j + off →
    ∀ (φ φ' : Sch ch.G (.down t D.R.m a)) (c : ℂ), (∀ b, IsThetaFunO ch.W.ψ _ _ (Φ b)) → IsThetaFunO ch.W.ψ _ _ φ →
      IsThetaFunO ch.W.ψ _ _ φ' → ∀ u v,
      conAt ch.W hM (fockD ch.W t (Function.update Φ a (c • φ + φ')) P) h j u v =
        c * conAt ch.W hM (fockD ch.W t (Function.update Φ a φ) P) h j u v +
          conAt ch.W hM (fockD ch.W t (Function.update Φ a φ') P) h j u v

def ContrLin (off : ℕ) : Prop := ∀ j, Even j → j + 2 < D.R.m → Even D.R.m → PositionLinAt ch j off

def LastLin (off : ℕ) : Prop := ∀ j, Even j → j + 2 = D.R.m → PositionLinAt ch j off

theorem conLin_of_positions (hC0 : ContrLin ch 0) (hC1 : ContrLin ch 1) (hL0 : LastLin ch 0) (hL1 : LastLin ch 1) :
    ConLin ch := by
  intro t M hM P h I S x f Φ hΦ h0 u y
  have intersection_update_fsHerm_neg_one : ∀ j off, Even j → off ≤ 1 → PositionLinAt ch j off := by
    intro j off hj ho
    by_cases hm : Even D.R.m ∧ j + 2 ≤ D.R.m
    · rcases Nat.lt_or_eq_of_le hm.2 with hlt | heq
      · interval_cases off
        · exact hC0 j hj hlt hm.1
        · exact hC1 j hj hlt hm.1
      · interval_cases off
        · exact hL0 j hj heq
        · exact hL1 j hj heq
    · intro t M hM P h Φ a _ φ φ' c _ _ _ u v
      simp only [conAt_zero ch.W hM _ h j hj hm, Pi.zero_apply, mul_zero, add_zero]
  let E : SchDown ch.G t → ℂ := fun Ψ => ∏ k ∈ Finset.range (D.R.m / 2),
    conAt ch.W hM (fockD ch.W t Ψ P) h (2 * k) (u (2 * k)) (u (2 * k + 1))
  have hev : ∀ i, evT (conAt ch.W hM (fockD ch.W t (Φ i) P) h) (f i) u y = (∏ n, f i n (y n)) * E (Φ i) := fun i => by
    simp only [evT, E]; ring
  simp only [hev, ← mul_assoc]
  refine sum_eq_zero_of_multilin (fun j : Fin D.R.m => GlobalTheory.LastVertexInv.thSub ch.W (.mu t D.R.m (j : ℕ))) E ?_ S
    (fun i => x i * ∏ n, f i n (y n)) Φ (fun i hi j => hΦ i hi j) (fun v => ?_)
  · intro Ψ hΨ a φ φ' c hφ hφ'
    by_cases hm : Even D.R.m
    · have hk : (a : ℕ) / 2 ∈ Finset.range (D.R.m / 2) := by
        obtain ⟨r, hr⟩ := hm; have := a.2; rw [Finset.mem_range]; omega
      have hrest : ∀ ψ : Sch ch.G (.down t D.R.m a), ∏ k ∈ Finset.range (D.R.m / 2) \ {(a : ℕ) / 2},
          conAt ch.W hM (fockD ch.W t (Function.update Ψ a ψ) P) h (2 * k) (u (2 * k)) (u (2 * k + 1)) =
          ∏ k ∈ Finset.range (D.R.m / 2) \ {(a : ℕ) / 2},
          conAt ch.W hM (fockD ch.W t Ψ P) h (2 * k) (u (2 * k)) (u (2 * k + 1)) := by
        intro ψ
        refine Finset.prod_congr rfl fun k hk' => ?_
        have hk2 : k ≠ (a : ℕ) / 2 := by simpa using (Finset.mem_sdiff.1 hk').2
        rw [conAt_local ch.W hM (fockD ch.W t (Function.update Ψ a ψ) P) (fockD ch.W t Ψ P) h (2 * k) (fun b hb => ?_)]
        have hne : b ≠ a := fun e => by subst e; omega
        simp only [fockD, Function.update_of_ne hne]
      simp only [E]
      have hsplit := fun (g : ℕ → ℂ) => Finset.prod_eq_mul_prod_diff_singleton (s := Finset.range (D.R.m / 2)) ((a : ℕ) / 2) g (fun h' => absurd hk h')
      rw [hsplit, hsplit, hsplit, hrest, hrest, hrest]
      rw [intersection_update_fsHerm_neg_one (2 * ((a : ℕ) / 2)) ((a : ℕ) - 2 * ((a : ℕ) / 2)) (even_two_mul _) (by omega) t M hM P h Ψ a (by omega)
        φ φ' c hΨ hφ hφ']
      ring
    · have h0m : 0 ∈ Finset.range (D.R.m / 2) := by have := D.R.two_le_m; rw [Finset.mem_range]; omega
      have hz : ∀ Ψ' : SchDown ch.G t, E Ψ' = 0 := fun Ψ' => Finset.prod_eq_zero h0m (by
        rw [conAt_zero ch.W hM _ h (2 * 0) (even_two_mul 0) (fun e => hm e.1)]
        rfl)
      simp only [hz, mul_zero, add_zero]
  · rw [← h0 y v]
    exact Finset.sum_congr rfl fun i _ => by ring
end
end GlobalTheory.ConnectionLinear
