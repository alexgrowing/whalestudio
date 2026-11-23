import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenSetOfLeRank
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyConstantExtensionByZero

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences

theorem comp_mem_SB_of_isInducing {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsInducing i) (Φ : SB X) {C : Set X} (hC : IsClosed C) (hiC : ∀ y, i y ∈ C)
    (hs : ∀ x ∈ C, Φ.1 x ≠ 0 → x ∈ Set.range i) : (fun y => Φ.1 (i y)) ∈ SB Y := by
  refine ⟨Φ.2.1.comp_continuous hi.continuous, ?_⟩
  have h0 : IsClosed (Function.support Φ.1) := (Φ.2.1.isOpen_fiber 0).isClosed_compl
  have h1 : IsCompact (Function.support Φ.1) := Φ.2.2.of_isClosed_subset h0 subset_closure
  have h2 : IsCompact (i ⁻¹' (Function.support Φ.1 ∩ C)) :=
    hi.isCompact_preimage' (h1.inter_right hC) fun x hx => hs x hx.2 hx.1
  refine HasCompactSupport.intro' h2 ((h0.inter hC).preimage hi.continuous) fun y hy => ?_
  by_contra h
  exact hy ⟨h, hiC y⟩

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [DecidableEq a] [DecidableEq b] in

theorem isOpen_le_rank (κ : ℕ) : IsOpen {x : Matrix b a k | κ ≤ x.rank} := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  exact GlobalTheory.isOpen_setOf_le_rank k b a κ

omit [DecidableEq a] [DecidableEq b] in

theorem isClosed_rank_lt (κ : ℕ) : IsClosed {x : Matrix b a k | x.rank < κ} := by
  have := (isOpen_le_rank (k := k) (a := a) (b := b) κ).isClosed_compl
  simpa only [Set.compl_ofPred, not_le] using this

omit [DecidableEq a] [DecidableEq b] in

theorem exists_extend_rankIn {s : Set ℕ} {κ n : ℕ} (hs : ∀ r ∈ s, κ ≤ r ∧ r < n) (f : SB (RankIn k a b s)) :
    ∃ F : SB (RankIn k a b (Set.Iio n)), (∀ x : RankIn k a b (Set.Iio n), x.1.rank < κ → F.1 x = 0) ∧
      ∀ x : RankIn k a b s, F.1 ⟨x.1, (hs _ x.2).2⟩ = f.1 x := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩,
      SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix b a k) :=
    inferInstanceAs (TotallyDisconnectedSpace (b → a → k))
  have : LocallyCompactSpace (Matrix b a k) := inferInstanceAs (LocallyCompactSpace (b → a → k))
  obtain ⟨G, hG, hG0⟩ := GlobalTheory.SBExtend.exists_extension (Matrix b a k) {x | κ ≤ x.rank} {x | x.rank ∈ s} (isOpen_le_rank κ)
    (fun x hx => (hs _ hx).1) f
  refine ⟨⟨fun y => G.1 y.1, comp_mem_SB_of_isInducing IsInducing.subtypeVal G (isClosed_rank_lt n)
    (fun y => y.2) fun x hx _ => ⟨⟨x, hx⟩, rfl⟩⟩, fun x hx => hG0 _ (not_le.2 hx), fun x => hG x⟩

def resFilt (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n) (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m) :
    (filt a b μ (Set.Iio n) κ).toRepresentation.IntertwiningMap (omegaOn a b μ s) where
  toFun Φ := ⟨fun x => Φ.1.1 ⟨x.1, ((hs _).1 x.2).2.trans_le hmn⟩,
    comp_mem_SB_of_isInducing
      (i := fun x : RankIn k a b s => (⟨x.1, ((hs _).1 x.2).2.trans_le hmn⟩ : RankIn k a b (Set.Iio n)))
      (IsInducing.subtypeVal.of_comp_iff.1 IsInducing.subtypeVal) Φ.1
      ((isClosed_rank_lt m).preimage continuous_subtype_val) (fun y => ((hs _).1 y.2).2)
      fun x hx h0 => ⟨⟨x.1, (hs _).2 ⟨not_lt.1 fun h => h0 (Φ.2 x h), hx⟩⟩, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl

theorem resFilt_apply (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n) (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m)
    (Φ : (filt a b μ (Set.Iio n) κ).toSubmodule) (x : RankIn k a b s) :
    (resFilt μ hmn hs Φ).1 x = Φ.1.1 ⟨x.1, ((hs _).1 x.2).2.trans_le hmn⟩ := rfl

theorem resFilt_surjective (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n)
    (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m) : Function.Surjective (resFilt (a := a) (b := b) μ hmn hs) := by
  intro f
  obtain ⟨F, h0, hF⟩ := exists_extend_rankIn (κ := κ) (n := n)
    (fun r hr => ⟨((hs r).1 hr).1, ((hs r).1 hr).2.trans_le hmn⟩) f
  exact ⟨⟨F, h0⟩, Subtype.ext (funext hF)⟩

theorem ker_resFilt (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n)
    (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m) (Φ : (filt a b μ (Set.Iio n) κ).toSubmodule) :
    resFilt μ hmn hs Φ = 0 ↔ Φ.1 ∈ (filt a b μ (Set.Iio n) m).toSubmodule := by
  constructor
  · intro h x hx
    by_cases hκ : x.1.rank < κ
    · exact Φ.2 x hκ
    · exact congrFun (congrArg Subtype.val h) ⟨x.1, (hs _).2 ⟨not_lt.1 hκ, hx⟩⟩
  · intro h
    exact Subtype.ext (funext fun x => h _ ((hs _).1 x.2).2)

end

theorem rankFiltration (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a t : ℕ) (μ : kˣ →* ℂˣ) : RankFiltration a t μ := by
  refine ⟨eq_top_iff.2 fun _ _ _ hx => absurd hx (Nat.not_lt_zero _),
    Subrepresentation.toSubmodule_injective <|
      eq_bot_iff.2 fun _ hΦ => Subtype.ext (funext fun x => hΦ x x.2), fun κ hκ => ⟨?_, ?_, ?_⟩⟩
  · exact fun Φ hΦ x hx => hΦ x (Nat.lt_succ_of_lt hx)
  · have hs : ∀ r, r ∈ Set.Ico κ a ↔ κ ≤ r ∧ r < a := fun _ => Iff.rfl
    have hinj : Function.Injective (resFilt (a := Fin a) (b := Fin (a + t)) μ le_rfl hs) := by
      refine (injective_iff_map_eq_zero _).2 fun Φ hΦ => ?_
      exact Subtype.ext (Subtype.ext (funext fun x => (ker_resFilt μ le_rfl hs Φ).1 hΦ x x.2))
    let e := Representation.Equiv.mk
      (LinearEquiv.ofBijective (resFilt (a := Fin a) (b := Fin (a + t)) μ le_rfl hs).toLinearMap
        ⟨hinj, resFilt_surjective μ le_rfl hs⟩) (resFilt μ le_rfl hs).isIntertwining'
    refine ⟨e.symm, fun Φ x => ?_⟩
    split_ifs with h
    · have h1 : e (e.symm Φ) = Φ := e.toLinearEquiv.apply_symm_apply Φ
      exact congrFun (congrArg Subtype.val h1) ⟨x.1, h, x.2⟩
    · exact (e.symm Φ).2 x (not_le.1 h)
  · have hs : ∀ r, r ∈ ({κ} : Set ℕ) ↔ κ ≤ r ∧ r < κ + 1 := fun r => by
      rw [Set.mem_singleton_iff]; omega
    let ρ := resFilt (a := Fin a) (b := Fin (a + t)) μ (Nat.succ_le_of_lt hκ) hs
    have hker : Submodule.comap (filt (Fin a) (Fin (a + t)) μ (Set.Iio a) κ).toSubmodule.subtype
        (filt (Fin a) (Fin (a + t)) μ (Set.Iio a) (κ + 1)).toSubmodule = LinearMap.ker ρ.toLinearMap :=
      Submodule.ext fun Φ => (ker_resFilt μ _ hs Φ).symm
    refine ⟨Representation.Equiv.mk ((Submodule.quotEquivOfEq _ _ hker).trans
      (LinearMap.quotKerEquivOfSurjective ρ.toLinearMap (resFilt_surjective μ _ hs))) fun g => ?_,
      fun Φ x => rfl⟩
    exact Submodule.linearMap_qext _ rfl

end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
