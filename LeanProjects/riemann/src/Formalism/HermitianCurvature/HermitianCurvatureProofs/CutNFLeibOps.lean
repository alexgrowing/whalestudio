import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nfLeibOps_hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

theorem nfLeibOps_hsInner_smul_left (c : ℂ) (A B' : Wq →L[ℂ] Wp) : B.hsInner (c • A) B' = c * B.hsInner A B' := by
  unfold B.hsInner
  rw [nfLeibOps_hsVec_smul, inner_smul_right]

theorem nfLeibOps_hsInner_smul_right (c : ℂ) (A B' : Wq →L[ℂ] Wp) :
    B.hsInner A (c • B') = conj c * B.hsInner A B' := by
  unfold B.hsInner
  rw [nfLeibOps_hsVec_smul, inner_smul_left]

def nfLeibOps_sc (Bs : B.RealPlaceData k r Wp Wq) (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) (g : B.Mat k r) : ℂ :=
  t.2.1 g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1

open Classical in

def nfLeibOps_mk (Bs : B.RealPlaceData k r Wp Wq) (T : B.DTerm k r Wp Wq)
    (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) : B.DTerm k r Wp Wq where
  coef g := nfLeibOps_sc Bs t g • T.coef g
  coefAdj g := conj (nfLeibOps_sc Bs t g) • T.coefAdj g
  word := if ∀ X ∈ t.2.2.2, B.inLie k r X then t.2.2.2 else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id x A B' := by
    simp only [ContinuousLinearMap.smul_apply]
    rw [nfLeibOps_hsInner_smul_left, nfLeibOps_hsInner_smul_right, T.adj_id, Complex.conj_conj]

theorem nfLeibOps_ckOn_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (B.Mat k r)}
    {c : B.Mat k r → ℂ} {f : B.Mat k r → E} (hc : B.CkOn ⊤ UU c) (hf : B.CkOn ⊤ UU f) :
    B.CkOn ⊤ UU (fun g => c g • f g) := by
  unfold B.CkOn at hc hf ⊢
  intro g₀ hg₀
  obtain ⟨U₁, c', hU₁, hg₁, hc', ec⟩ := hc g₀ hg₀
  obtain ⟨U₂, f', hU₂, hg₂, hf', ef⟩ := hf g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => c' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right), ?_⟩
  intro g hg hgG
  show c g • f g = c' g • f' g
  rw [ec g hg.1 hgG, ef g hg.2 hgG]

theorem nfLeibOps_ckOn_conj {UU : Set (B.Mat k r)} {c : B.Mat k r → ℂ} (hc : B.CkOn ⊤ UU c) :
    B.CkOn ⊤ UU (fun g => conj (c g)) := by
  unfold B.CkOn at hc ⊢
  intro g₀ hg₀
  obtain ⟨U, c', hU, hg, hc', ec⟩ := hc g₀ hg₀
  refine ⟨U, fun g => conj (c' g), hU, hg, ?_, ?_⟩
  · refine (Complex.conjCLE.contDiff.comp_contDiffOn hc').congr (fun g _ => ?_)
    simp
  · intro g hgU hgG
    show conj (c g) = conj (c' g)
    rw [ec g hgU hgG]

theorem nfLeibOps_ckOn_sc (Bs : B.RealPlaceData k r Wp Wq) (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) (D : ℕ)
    (hP : ListSumSplittings.PolyClass D t.2.1) : B.CkOn ⊤ (C6.domL Bs ∅) (nfLeibOps_sc Bs t) := by
  intro g₀ hg₀
  obtain ⟨U1, c1, hU1, hg1, hc1, he1⟩ := hP.1 g₀ hg₀.1
  have hGc : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z')
  have hO : IsOpen {g : B.Mat k r | 0 < Gf k r Bs.z Bs.z' g} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
  refine ⟨U1 ∩ {g | 0 < Gf k r Bs.z Bs.z' g},
    fun g => c1 g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1, hU1.inter hO, ⟨hg1, hg₀.2.1⟩, ?_, ?_⟩
  · refine (hc1.mono Set.inter_subset_left).mul ?_
    refine ContDiffOn.pow ?_ _
    refine (hGc.contDiffOn.inv fun g hg => ?_).mono Set.inter_subset_right
    · exact_mod_cast (ne_of_gt hg)
  · intro g hg hgG
    simp only [nfLeibOps_sc, he1 g hg.1 hgG]

end ops

theorem nfLeibOps_sum_key {E : Type*} [AddCommGroup E] [Module ℂ E] {α : Type*} (Q : ℕ) (key : α → ℕ)
    (f : ℕ → ℂ) (a : α → E) : ∀ l : List α, (∀ t ∈ l, key t ≤ Q) →
    (l.map fun t => f (key t) • a t).sum =
      ∑ q : Fin (Q + 1), f q • ((l.filter fun t => key t = (q : ℕ)).map a).sum := by
  intro l hl
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun t' ht' => hl t' (by simp [ht']))]
    have hq : key t < Q + 1 := Nat.lt_succ_of_le (hl t (by simp))
    have hsplit : ∀ q : Fin (Q + 1), f q • (((t :: l).filter fun t' => key t' = (q : ℕ)).map a).sum =
        (if key t = (q : ℕ) then f q • a t else 0) +
          f q • ((l.filter fun t' => key t' = (q : ℕ)).map a).sum := by
      intro q
      by_cases h : key t = (q : ℕ)
      · simp [List.filter_cons, h, smul_add]
      · simp [List.filter_cons, h]
    rw [Finset.sum_congr rfl (fun q _ => hsplit q), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨key t, hq⟩]
    · simp
    · intro b _ hb
      have hne : key t ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [hne]
    · simp

theorem nfLeibOps_of (hE : NFLeibExp) : NFLeibOps := by
  intro k r Wp Wq _ _ _ _ _ Bs Dop hsm
  classical
  let terms : B.DTerm k r Wp Wq → List (ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) :=
    fun T => (hE k r Wp Wq Bs T.word T.word_lie).choose
  have hspec := fun T : B.DTerm k r Wp Wq => (hE k r Wp Wq Bs T.word T.word_lie).choose_spec
  set Q : ℕ := (Dop.map fun T => T.word.length).sum with hQ
  have hQle : ∀ T ∈ Dop, T.word.length ≤ Q := fun T hT =>
    List.le_sum_of_mem (List.mem_map.2 ⟨T, hT, rfl⟩)
  let LT : B.DTerm k r Wp Wq → Fin (Q + 1) → B.DiffOp k r Wp Wq :=
    fun T q => ((terms T).filter fun t => t.1 = (q : ℕ)).map (nfLeibOps_mk Bs T)
  refine ⟨Q, fun q => Dop.flatMap fun T => LT T q, ?_, ?_, ?_⟩
  ·
    intro q T' hT'
    obtain ⟨T, hT, hT'T⟩ := List.mem_flatMap.1 hT'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT'T
    have htm : t ∈ terms T := (List.mem_filter.1 ht).1
    have hP := ((hspec T).1 t htm).2.1
    exact ⟨nfLeibOps_ckOn_smul (nfLeibOps_ckOn_sc Bs t _ hP) (hsm T hT).1,
      nfLeibOps_ckOn_smul (nfLeibOps_ckOn_conj (nfLeibOps_ckOn_sc Bs t _ hP)) (hsm T hT).2⟩
  ·
    intro q T' hT'
    obtain ⟨T, hT, hT'T⟩ := List.mem_flatMap.1 hT'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT'T
    have htm : t ∈ terms T := (List.mem_filter.1 ht).1
    obtain ⟨-, hP, hsub⟩ := (hspec T).1 t htm
    refine ⟨T, hT, t.2.1, t.2.2.1, hP, ?_, fun g _ => rfl⟩
    have hlie : ∀ X ∈ t.2.2.2, B.inLie k r X := fun X hX => T.word_lie X (hsub.subset hX)
    simp only [nfLeibOps_mk]
    rw [if_pos hlie]
    exact hsub
  ·
    intro Ψ hΨ F hF x hx
    have hT1 : ∀ T ∈ Dop, T.coef x (B.Rw T.word (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x) =
        ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (LT T q) F x := by
      intro T hT
      rw [(hspec T).2 Ψ hΨ F hF x hx, map_list_sum, List.map_map]
      have e1 : ((terms T).map ((T.coef x) ∘ fun t => ((((Ψ t.1 (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) * t.2.1 x *
            ((Gf k r Bs.z Bs.z' x : ℝ) : ℂ)⁻¹ ^ t.2.2.1) • B.Rw t.2.2.2 F x))) =
          (terms T).map fun t => (fun n : ℕ => ((Ψ n (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ)) t.1 •
            (fun t => nfLeibOps_sc Bs t x • T.coef x (B.Rw t.2.2.2 F x)) t := by
        refine List.map_congr_left fun t _ => ?_
        simp only [Function.comp_apply, map_smul, nfLeibOps_sc, smul_smul, mul_assoc]
      rw [e1]
      refine (nfLeibOps_sum_key Q (fun t => t.1) (fun n : ℕ => ((Ψ n (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ))
        (fun t => nfLeibOps_sc Bs t x • T.coef x (B.Rw t.2.2.2 F x)) (terms T)
        (fun t ht => ((hspec T).1 t ht).1.trans (hQle T hT))).trans ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      unfold B.opApply
      rw [List.map_map]
      refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
      have htm : t ∈ terms T := (List.mem_filter.1 ht).1
      have hlie : ∀ X ∈ t.2.2.2, B.inLie k r X := fun X hX => T.word_lie X (((hspec T).1 t htm).2.2.subset hX)
      simp only [Function.comp_apply, nfLeibOps_mk, if_pos hlie, ContinuousLinearMap.smul_apply]
    have hall : ∀ D' : B.DiffOp k r Wp Wq, (∀ T ∈ D', T ∈ Dop) →
        B.opApply D' (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
          ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (D'.flatMap fun T => LT T q) F x := by
      intro D'
      induction D' with
      | nil => intro _; simp [B.opApply]
      | cons T D' ih =>
        intro hsub
        have eA : ∀ (D'' : B.DiffOp k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)),
            B.opApply (T :: D'') G x = T.coef x (B.Rw T.word G x) + B.opApply D'' G x := by
          intro D'' G; simp [B.opApply]
        have eB : ∀ (l1 l2 : B.DiffOp k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)),
            B.opApply (l1 ++ l2) G x = B.opApply l1 G x + B.opApply l2 G x := by
          intro l1 l2 G; simp [B.opApply]
        rw [eA, hT1 T (hsub T List.mem_cons_self), ih fun T' hT' => hsub T' (List.mem_cons_of_mem _ hT'),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [List.flatMap_cons, eB, smul_add]
    exact hall Dop fun T hT => hT

end

end Formalism.FourierDecayAlt.P.CutBP
