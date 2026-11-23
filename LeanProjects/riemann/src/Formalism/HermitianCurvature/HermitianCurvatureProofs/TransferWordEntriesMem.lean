import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvMemOfKappa

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Pres

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def presAlg (U : Submodule ℂ V) : StarSubalgebra ℂ (Pr V) where
  carrier := {a | (∀ Φ ∈ U, a.1 Φ ∈ U) ∧ ∀ Φ ∈ U, a.2.unop Φ ∈ U}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun Φ hΦ => ha1 _ (hb1 Φ hΦ), fun Φ hΦ => hb2 _ (ha2 Φ hΦ)⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun Φ hΦ => U.add_mem (ha1 Φ hΦ) (hb1 Φ hΦ), fun Φ hΦ => U.add_mem (ha2 Φ hΦ) (hb2 Φ hΦ)⟩
  algebraMap_mem' := by
    intro a
    refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
    · show (algebraMap ℂ (Module.End ℂ V) a) Φ ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem a hΦ
    · show (algebraMap ℂ (Module.End ℂ V) (conj a)) Φ ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem _ hΦ
  star_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨ha2, ha1⟩

end Pres

section Words

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem entries_mem_transpose {M : M2 (SlopeTestRemainingChoices S A)} (h : E2 𝒜 M) : E2 𝒜 Mᵀ := fun i j => h j i

theorem transfer_word_entries_mem (QQ : ℂ → M2 A) (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, QQ Y a b ∈ 𝒜) (w : List (Letter ℂ S)) (Y : ℂ)
    (hY : star Y = Y) : E2 𝒜 (TTw QQ w Y) := by
  induction w with
  | nil =>
    intro a b
    show io (QQ Y a b) ∈ entSub 𝒜
    exact io_mem (hQ Y hY a b)
  | cons l w ih =>
    by_cases hp : l.plus
    · rw [TTw, if_pos hp]; exact entries_mem_mul ih (reflection_entries_mem _ _)
    · rw [TTw, if_neg hp]; exact entries_mem_mul (reflection_transpose_entries_mem _ _) ih

theorem rrw_mem (QQ : ℂ → M2 A) (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, QQ Y a b ∈ 𝒜) (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, star l.pt = l.pt) : RRw QQ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [RRw]
    refine (entSub 𝒜).mul_mem (ih fun l' hl' => hw l' (by simp [hl'])) (ins_mem _ ?_)
    have hT := transfer_word_entries_mem QQ hQ w l.pt (hw l (by simp))
    split_ifs
    · exact hT
    · exact entries_mem_transpose hT

end Words

section Levels

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem matrix_two_entries_mem {𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))} {a b c d : Pr (RadSp k r z z' π π')}
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜) (hd : d ∈ 𝒜) : ∀ i j, (!![a, b; c, d] : M2 _) i j ∈ 𝒜 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem tprod_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π')))
    (Y : ℂ) (i : ℕ) (hS : ∀ l : Fin r, i ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) (a b : Fin 2) :
    tprod L Y i a b ∈ 𝒜 := by
  suffices H : ∀ n i, r - i = n → (∀ l : Fin r, i ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) →
      ∀ a b, tprod L Y i a b ∈ 𝒜 from H _ i rfl hS a b
  intro n
  induction n with
  | zero =>
    intro i hi _ a b
    unfold tprod
    rw [dif_neg (by omega), Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ n ih =>
    intro i hi hS a b
    unfold tprod
    rw [dif_pos (by omega), Matrix.mul_apply]
    refine sum_mem fun e _ => mul_mem (ih (i + 1) (by omega) (fun l hl => hS l (by omega)) a e) ?_
    obtain ⟨hp, hc, hci⟩ := hS ⟨i, by omega⟩ le_rfl
    have h00 : algebraMap ℂ _ Y + L.p ⟨i, by omega⟩ ∈ 𝒜 := add_mem (𝒜.algebraMap_mem Y) hp
    fin_cases e <;> fin_cases b <;> simp [Ts, Formalism.YangianSpanCharacter.T.Tm, site, h00, hc, hci]

theorem QQi_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))) (i : Fin (r + 1))
    (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, st.QQ Y a b ∈ 𝒜)
    (hS : ∀ l : Fin r, i.val ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) :
    ∀ Y : ℂ, star Y = Y → ∀ a b, QQi L st i Y a b ∈ 𝒜 := by
  intro Y hY a b
  unfold QQi
  rw [Matrix.mul_apply]
  refine sum_mem fun e _ => mul_mem ?_ (tprod_mem L 𝒜 Y i.val hS e b)
  rw [Matrix.mul_apply]
  refine sum_mem fun f _ => mul_mem ?_ (hQ Y hY f e)
  rw [Matrix.conjTranspose_apply]
  exact star_mem (tprod_mem L 𝒜 (star Y) i.val hS f a)

def IntLevOn (μ : Measure (Mt k r)) (i : Fin (r + 1)) (U : Submodule ℂ (RadSp k r z z' π π')) : Prop :=
  ∀ c ∈ OmX r, ∀ Φ ∈ U, ∀ Ψ ∈ U,
    (∀ c' : Cf r i, Integrable (fun g : Mt k r =>
      B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ) ∧
    Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * pairAt μ Φ Ψ (glue i c c'))

end Levels

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formInt_of_cls (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (U : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (hK : ∀ i, K i ≤ U i)
    (hI : ∀ i, IntLevOn μ i (U i))
    (hQ : ∀ i, ∀ Y : ℂ, star Y = Y → ∀ a b, st.QQ Y a b ∈ presAlg (U i))
    (hS : ∀ (i : Fin (P.r + 1)) (l : Fin P.r), i.val ≤ l.val →
      L.p l ∈ presAlg (U i) ∧ L.c l ∈ presAlg (U i) ∧ L.ci l ∈ presAlg (U i)) :
    FormInt S P z z' π π' μ L st l0 K := by
  intro w hw i c hc x y hx hy
  have hRR : RRi L st i w ∈ entSub (presAlg (U i)) :=
    rrw_mem (QQi L st i) (QQi_mem L st _ i (hQ i) (hS i)) w hw.1.2.1
  have hu : ∀ a, act (RRi L st i w) x a ∈ U i := fun a =>
    (U i).sum_mem fun b _ => (hRR a b).1 _ (hK i (hx b))
  have hv : ∀ a, y a ∈ U i := fun a => hK i (hy a)
  refine ⟨fun c' a => ((hI i) c hc _ (hu a) _ (hv a)).1 c', ?_⟩
  simp only [Finset.mul_sum]
  exact integrable_finsetSum _ fun a _ => ((hI i) c hc _ (hu a) _ (hv a)).2

end Top

end Formalism.FourierDecayAlt.P5.HerA
