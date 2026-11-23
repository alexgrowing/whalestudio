import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.TypeDecomp

theorem lintegral_biUnion_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (A : ι → Set α) (f : α → ENNReal) :
    ∫⁻ x in ⋃ i ∈ s, A i, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in A i, f x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hb]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

theorem hasType_cast (I : AutInst) (x : I.GA) {a a' : ℕ} (h : a' = a) (j : Fin a → ℕ) (τ : Fin a → ℝ)
    (H : HasType I x j τ) : ∃ τ', HasType I x (fun i : Fin a' => j (Fin.cast h i)) τ' := by
  subst h
  exact ⟨τ, H⟩

theorem sum_diff (a : ℕ) (r : Fin (a + 1) → ℕ) (j : Fin a → ℕ)
    (h : ∀ i, r i.succ = r i.castSucc + j i) : r (Fin.last a) = r 0 + ∑ i, j i := by
  induction a with
  | zero => simp
  | succ a ih =>
    have key := ih (fun i => r i.castSucc) (fun i => j i.castSucc) (fun i => by
      have := h i.castSucc
      rwa [Fin.succ_castSucc] at this)
    have hl := h (Fin.last a)
    rw [Fin.succ_last] at hl
    simp only [Fin.castSucc_zero] at key
    rw [Fin.sum_univ_castSucc, hl, key]
    ring

theorem exists_type (B : RowsAut) (p q : ℕ) (hs : SigIs B p q) (hn : 1 ≤ B.I.n) (x : B.I.GA)
    (hx : least B.I x < 1 / 2) :
    ∃ J ∈ Finset.Icc 1 q, ∃ c : Composition J, ∃ τ, HasType B.I x c.blocksFun τ := by
  obtain ⟨⟨a, S, τ, hF⟩, -, hprop⟩ := GlobalTheory.PointFlag.flag_spec B.I x
  obtain ⟨hsteps, hlast⟩ := hprop a S τ hF
  have hlt : ∀ i : Fin a, Formalism.HN.rkK (S i.castSucc) < Formalism.HN.rkK (S i.succ) := fun i => (hsteps i).2.1
  set j : Fin a → ℕ := fun i => Formalism.HN.rkK (S i.succ) - Formalism.HN.rkK (S i.castSucc) with hj
  have hstep : ∀ i, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i := fun i => by
    have := hlt i
    simp only [hj]
    omega
  have hjpos : ∀ i, 0 < j i := fun i => by
    have := hlt i
    simp only [hj]
    omega
  have hT : HasType B.I x j τ := ⟨S, hF, hstep⟩
  have hsum : Formalism.HN.rkK (S (Fin.last a)) = Formalism.HN.rkK (S 0) + ∑ i, j i :=
    GlobalTheory.TypeDecomp.sum_diff a (fun i => Formalism.HN.rkK (S i)) j hstep
  have ha : a ≠ 0 := by
    intro h0
    have := (hlast hn).1.mp h0
    linarith
  obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
  have hiso : Formalism.HN.rkK (stepLt B.I x (1 / 2)) ≤ rkR (B.I.ε v) := (GlobalTheory.FlagIso.flag_isotropic B.I x).2.1 v
  have hq : rkR (B.I.ε v) ≤ q := (min_le_right _ _).trans (hs v).2.le
  have hSl : S (Fin.last a) = stepLt B.I x (1 / 2) := hF.2.2.1
  have h1 : 1 ≤ ∑ i, j i := by
    have := Finset.single_le_sum (f := j) (fun i _ => Nat.zero_le _) (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero ha⟩)
    have := hjpos ⟨0, Nat.pos_of_ne_zero ha⟩
    omega
  have h2 : ∑ i, j i ≤ q := by
    rw [hSl] at hsum
    omega
  let c : Composition (∑ i, j i) :=
    ⟨List.ofFn j, fun {b} hb => by
      simp only [List.mem_ofFn, Set.mem_range] at hb
      obtain ⟨k, rfl⟩ := hb
      exact hjpos k, by simp [List.sum_ofFn]⟩
  have hlen : c.length = a := by simp [c, Composition.length]
  have hc : c.blocksFun = fun i => j (Fin.cast hlen i) := by
    funext i
    show (List.ofFn j).get i = j (Fin.cast hlen i)
    first
      | rw [List.get_ofFn]
      | simp [List.get_eq_getElem, Fin.cast]
  obtain ⟨τ', h'⟩ := GlobalTheory.TypeDecomp.hasType_cast B.I x hlen j τ hT
  refine ⟨∑ i, j i, Finset.mem_Icc.mpr ⟨h1, h2⟩, c, τ', ?_⟩
  rw [hc]
  exact h'

theorem lintegral_le_sum_types : ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → 1 ≤ B.I.n → ∀ Φ : B.I.GA → ENNReal, (∀ x, 1 / 2 ≤ least B.I x → Φ x = 0) → ∫⁻ x in B.fund, Φ x ∂(B.I.muA B.μf) ≤ ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J, ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) := by
  intro B p q hs hn Φ hΦ
  have hT : ∀ (J : ℕ) (c : Composition J),
      MeasurableSet {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} := fun J c => by
    obtain ⟨s, -, h, -⟩ := GlobalTheory.FlagMeas.type_measurable B.I c.length c.blocksFun
    exact h
  set P : Set B.I.GA := ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
    {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} with hP
  set U : Set B.I.GA := ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
    {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund with hU
  have hPm : MeasurableSet P :=
    Finset.measurableSet_biUnion _ fun J _ => Finset.measurableSet_biUnion _ fun c _ => hT J c
  have hcover : B.fund ⊆ U ∪ Pᶜ := by
    intro x hx
    by_cases hxP : x ∈ P
    · left
      simp only [hP, hU, Set.mem_iUnion, Set.mem_inter_iff] at hxP ⊢
      obtain ⟨J, hJ, c, hc, hxc⟩ := hxP
      exact ⟨J, hJ, c, hc, hxc, hx⟩
    · exact Or.inr hxP
  have hzero : ∫⁻ x in Pᶜ, Φ x ∂(B.I.muA B.μf) = 0 := by
    have hae : ∀ᵐ x ∂((B.I.muA B.μf).restrict Pᶜ), Φ x = 0 := by
      rw [ae_restrict_iff' hPm.compl]
      refine ae_of_all _ fun x hx => hΦ x ?_
      by_contra hlt
      push_neg at hlt
      obtain ⟨J, hJ, c, τ, hτ⟩ := GlobalTheory.TypeDecomp.exists_type B p q hs hn x hlt
      apply hx
      simp only [hP, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨J, hJ, c, Finset.mem_univ c, τ, hτ⟩
    rw [lintegral_congr_ae hae, lintegral_zero]
  calc ∫⁻ x in B.fund, Φ x ∂(B.I.muA B.μf)
      ≤ ∫⁻ x in U ∪ Pᶜ, Φ x ∂(B.I.muA B.μf) := lintegral_mono_set hcover
    _ ≤ ∫⁻ x in U, Φ x ∂(B.I.muA B.μf) + ∫⁻ x in Pᶜ, Φ x ∂(B.I.muA B.μf) := lintegral_union_le _ _ _
    _ = ∫⁻ x in U, Φ x ∂(B.I.muA B.μf) := by rw [hzero, add_zero]
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∫⁻ x in ⋃ c ∈ (Finset.univ : Finset (Composition J)),
          {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) :=
        GlobalTheory.TypeDecomp.lintegral_biUnion_le _ _ _ _
    _ ≤ _ := Finset.sum_le_sum fun J _ => GlobalTheory.TypeDecomp.lintegral_biUnion_le _ _ _ _

end GlobalTheory.TypeDecomp
