import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormSmulL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameThresholdBoundHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWave

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem onOld_id {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {w : List C.Letter} :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
      KB.onOld (⇑(LinearMap.id : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] _)) ys x = x
  | [], x => rfl
  | y :: ys, x => by
    funext e
    simp only [KB.onOld]
    rw [onOld_id ys]
    exact congrArg x (Fin.cons_self_tail e)

theorem mix_push {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) {K d : ℕ}
    (grid : Fin K → Fin (d + 1) → ℝ) (mk : List ℝ → List C.Letter) (p q : C.LPt) :
    KB.mix S v ε i (PBD.pushU grid mk) (PBD.pushTh grid mk) p q =
      ∑ n : Fin K → Fin (d + 1), (F7.thGrid grid n : ℂ) *
        KB.gN S v ε i (mk (List.ofFn fun b => grid b (n b))) p q := by
  unfold KB.mix PBD.pushTh
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hmem : mk (List.ofFn fun b => grid b (n b)) ∈ PBD.pushU grid mk :=
    Finset.mem_image_of_mem _ (Finset.mem_univ n)
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    simp

section sizes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem sizeAt_plusW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ys : List ℝ) (a : List C.Letter) :
    S.sizeAt v (KB.plusW ys a) = (ys.map fun y => |S.P v y|).prod * S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  rw [PBD.plusW_eq, List.map_append, List.prod_append, List.map_map]
  rfl

theorem sizeAt_minusW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ys : List ℝ) (a : List C.Letter) :
    S.sizeAt v (KB.minusW ys a) = (ys.map fun y => |S.P v (y + 1)|).prod * S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  rw [PBD.minusW_eq, List.map_append, List.prod_append, List.map_map]
  rfl

theorem sizeAt_pos (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) (a : List C.Letter)
    (ha : D.AdmAt S v a) : 0 < S.sizeAt v a := by
  obtain ⟨w, hw⟩ := ha
  have hA := (PBD.admissible_list_of_word S w v).1
  rw [hw] at hA
  unfold C.HidaSetting.sizeAt
  refine List.prod_pos fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have hnode := hA j hj
  have hgrid : (∃ a', PBD.nodeOf a[j] ∈ S.grid v a') ∨ PBD.nodeOf a[j] ∈ S.grid1 v := by
    rcases Finset.mem_union.1 hnode with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr h
  obtain ⟨-, -, hP, hP1⟩ := (hG v).2.2.2.2.2 _ hgrid
  refine abs_pos.2 ?_
  unfold PBD.nodeOf at hP hP1
  split_ifs at hP hP1 with hs
  · exact hP
  · simpa using hP1

end sizes

section nodes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

def NodeOK (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (one : Bool) (y : ℝ) : Prop :=
  (one = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ y ∈ S.grid v a') ∨
    (one = true ∧ y ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, y) x)

theorem nodes_level (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (a : List C.Letter) (ha : D.AdmAt S v a)
    (K : ℕ) (hK : a.length + K ≤ S.Ntop) (j : ℕ) (hj : j ≤ S.G.r) :
    ∃ grid : Fin K → Fin (2 * j + 1) → ℝ,
      (∀ b, Function.Injective (grid b)) ∧
      (∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * j)) ∧
      (∀ n : Fin K → Fin (2 * j + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        (List.ofFn fun b => grid b (n b)).Pairwise (fun y y' => 2 < |y - y'|) ∧
        ∀ y ∈ (List.ofFn fun b => grid b (n b)), NodeOK S v a (decide (j = 0)) y) ∧
      KB.LocProb S v (a.length + K) (PBD.pushU grid fun ys => KB.plusW ys a)
        (PBD.pushTh grid fun ys => KB.plusW ys a) ∧
      KB.LocProb S v (a.length + K) (PBD.pushU grid fun ys => KB.minusW ys a)
        (PBD.pushTh grid fun ys => KB.minusW ys a) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGr, -⟩ := hB'
  have hCI := PBCut.cutInside_of_built hB
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  ·
    obtain ⟨ys, hlen, -, hg1, hp, hm, hcp, hcm, hpw⟩ :=
      Formalism.FourierDecayAlt.P.new_letters_admissible_level_one E Wp Wq S hGo hGr hCI v a K ha hK
    set grid : Fin K → Fin (2 * 0 + 1) → ℝ := fun b _ => ys.get ⟨b, by rw [hlen]; exact b.2⟩ with hgrid
    have hys : ∀ n : Fin K → Fin (2 * 0 + 1), (List.ofFn fun b => grid b (n b)) = ys := by
      intro n
      apply List.ext_get
      · simp [hlen]
      · intro i h1 h2
        simp [hgrid]
    have hsep : ∀ y ∈ ys, ∀ x ∈ a, PBD.Sep (true, y) x := by
      obtain ⟨w, hw⟩ := hp
      have hA := (PBD.admissible_list_of_word S w v).2
      rw [hw, PBD.plusW_eq] at hA
      intro y hy x hx
      exact (List.pairwise_append.1 hA).2.2 _ (List.mem_map.2 ⟨y, hy, rfl⟩) _ hx
    have hmk : ∀ mk : List ℝ → List C.Letter, (mk ys = KB.plusW ys a ∨ mk ys = KB.minusW ys a) →
        ∀ n : Fin K → Fin (2 * 0 + 1), D.AdmAt S v (mk (List.ofFn fun b => grid b (n b))) ∧
          (mk (List.ofFn fun b => grid b (n b))).length ≤ a.length + K := by
      intro mk hmk n
      rw [hys n]
      rcases hmk with h | h <;> rw [h]
      · exact ⟨hp, by rw [PBD.plusW_eq]; simp [hlen]; omega⟩
      · exact ⟨hm, by rw [PBD.minusW_eq]; simp [hlen]; omega⟩
    refine ⟨grid, fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega), fun b => ?_, fun n => ?_, ?_, ?_⟩
    · simp [F7.lagCo]
    · rw [hys n]
      refine ⟨hp, hm, hcp, hcm, hpw.imp fun h => by linarith, fun y hy => Or.inr ⟨rfl, hg1 y hy, hsep y hy⟩⟩
    · exact PBD.locProb_push S v _ grid (fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega)) _
        (hmk (fun ys => KB.plusW ys a) (Or.inl rfl))
    · exact PBD.locProb_push S v _ grid (fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega)) _
        (hmk (fun ys => KB.minusW ys a) (Or.inr rfl))
  ·
    obtain ⟨-, grid, hinj, hl1, hmem, hall, hlp, hlm⟩ :=
      Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a K (2 * j) ha hK (by omega)
    refine ⟨grid, hinj, hl1, fun n => ?_, hlp, hlm⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hall n
    refine ⟨h1, h2, h3, h4, h5.imp fun h => by linarith, fun y hy => Or.inl ⟨by simp; omega, ?_⟩⟩
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨a.length + K - b, by omega, by omega, hmem b (n b)⟩

end nodes

end

end Formalism.FourierDecayAlt.P.PBL
