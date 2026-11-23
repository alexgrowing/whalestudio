import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralLinearAndCongrStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedInvariantIntegralDoubleCosetCellSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralVanishOfInnerVanishStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CellVanishing

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]

def extPt (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) : ∀ i, H i :=
  fun i => if hp : p i then g ⟨i, hp⟩ else h₀ i

lemma extPt_update (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) (j : Subtype p)
    (x : H j.1) : extPt p h₀ (Function.update g j x) = Function.update (extPt p h₀ g) j.1 x := by
  funext i
  by_cases hi : i = j.1
  · subst hi
    simp [extPt, j.2]
  · have hne : ∀ hp : p i, (⟨i, hp⟩ : Subtype p) ≠ j := fun hp h => hi (by rw [← h])
    rw [Function.update_of_ne hi]
    unfold extPt
    split_ifs with hp
    · rw [Function.update_of_ne (hne hp)]
    · rfl

lemma extPt_at (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) (j : Subtype p) :
    extPt p h₀ g j.1 = g j := by
  simp [extPt, j.2]

lemma niter_sub (p : ι → Prop) [DecidablePred p] {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i))
    (μ : ∀ i, Measure (H i)) (f : (∀ i, H i) → ℂ) (h₀ : ∀ i, H i) :
    ∀ (l : List (Subtype p)) (g : ∀ j : Subtype p, H j.1) (z : ℂ),
      NIter (R := fun j : Subtype p => R j.1) (fun j => ρ j.1) (fun j => μ j.1) (fun g => f (extPt p h₀ g)) l g z →
      NIter ρ μ f (l.map Subtype.val) (extPt p h₀ g) z
  | [], g, z, hz => by simpa [NIter] using hz
  | j :: l, g, z, hz => by
    obtain ⟨F, hF, hF'⟩ := hz
    refine ⟨F, hF, fun x => ?_⟩
    rw [← extPt_update]
    exact niter_sub p ρ μ f h₀ l _ _ (hF' x)

end GlobalTheory.CellVanishing

namespace GlobalTheory.RowVal

open GlobalTheory.CellVanishing in

theorem cellVan_holds : CellVan := by
  intro ι _ H _ _ _ _ _ _ _ _ A B R K l hl hS ρ μ ρ' μ' hM X S b w q z α hw hdist hinv hsupp hz hrel
  haveI := Classical.decEq (∀ i, H i)
  have hQ := (GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr ι H R ρ μ l 1).1 (Fin 2) Finset.univ α z q (fun n _ => hz n)
  refine GlobalTheory.T.isIteratedInvariantIntegral_vanish_of_inner_vanish ι H A B R K l hl hS ρ μ ρ' μ' hM
    ((S 0).image (b 0) ∪ (S 1).image (b 1)) (fun g => ∑ n ∈ Finset.univ, α n * q n g) _ ?_ ?_ ?_ hQ ?_
  · intro c hc i
    rcases Finset.mem_union.1 hc with hc | hc <;>
    · obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hc
      obtain ⟨_, hb, _⟩ := hw _ β hβ
      exact hb i
  · intro i hi h
    constructor
    · intro r hr
      exact Finset.sum_congr rfl fun n _ => by rw [(hinv n i hi h).1 r hr]
    · intro k hk
      exact Finset.sum_congr rfl fun n _ => by rw [(hinv n i hi h).2 k hk]
  · intro h h1 hne
    obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨β, hβ, hc⟩ := hsupp n h h1 (right_ne_zero_of_mul hn)
    refine ⟨b n β, ?_, hc⟩
    fin_cases n
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hβ)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hβ)
  · intro a ha ha1
    let p : ι → Prop := fun i => i ∈ l
    haveI : ∀ j : Subtype p, LocallyCompactSpace (B j.1) := fun j =>
      (hS j.1 j.2).clB.isClosedEmbedding_subtypeVal.locallyCompactSpace

    haveI : ∀ n (β : X n) i, Decidable (b n β i ∈ B i) := fun _ _ _ => Classical.dec _
    let bb : ∀ n, X n → ∀ i, B i := fun n β i => if h : b n β i ∈ B i then ⟨b n β i, h⟩ else 1
    have hbb : ∀ n β (hβ : β ∈ S n), bb n β = fun i => ⟨b n β i, (hw n β hβ).2.1 i⟩ := by
      intro n β hβ
      funext i
      exact dif_pos _
    let qn : Fin 2 → (∀ j : Subtype p, B j.1) → ℂ := fun n g => q n fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1
    have hg1 : ∀ (g : ∀ j : Subtype p, B j.1) i, i ∉ l → a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1 = 1 := by
      intro g i hi
      simp [extPt, p, hi, ha1 i hi]
    have hmeas : ∀ j ∈ l.attach, IsClosed (((R j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧
        IsCompact (((K j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧
        IsOpen (((K j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧ (ρ' j.1).IsHaarMeasure ∧
        (ρ' j.1).IsInvInvariant ∧ (μ' j.1).IsHaarMeasure ∧ (μ' j.1).IsMulRightInvariant := by
      intro j _
      have hs := hS j.1 j.2
      obtain ⟨-, -, h3, h4⟩ := hM j.1 j.2
      exact ⟨hs.clR.preimage continuous_subtype_val, hs.clB.isClosedEmbedding_subtypeVal.isCompact_preimage hs.cpt,
        hs.opn, h3, hs.uniRB _ h3, h4, hs.uniB _ h4⟩
    have hcell : ∀ n, NIter (R := fun j : Subtype p => (R j.1).subgroupOf (B j.1)) (fun j => ρ' j.1) (fun j => μ' j.1)
        (qn n) l.attach 1 (∑ β ∈ S n, w n β * q n (a * b n β)) := by
      intro n
      have hv : ∀ β (hβ : β ∈ S n) i, ((bb n β i : B i) : H i) = b n β i := fun β hβ i => by rw [hbb n β hβ]
      have key := GlobalTheory.T.iteratedInvariantIntegral_doubleCoset_cellSum (Subtype p) (fun j => B j.1) (fun j => (R j.1).subgroupOf (B j.1))
        (fun j => (K j.1).subgroupOf (B j.1)) l.attach (List.nodup_attach.2 hl) (fun j => ρ' j.1) (fun j => μ' j.1) hmeas
        (X n) (S n) (fun β j => bb n β j.1) (qn n) (fun β _ j hj => absurd (List.mem_attach l j) hj) ?_ ?_ ?_
      · convert key using 1
        refine Finset.sum_congr rfl fun β hβ => ?_
        obtain ⟨h1, hb, hwβ⟩ := hw n β hβ
        rw [hwβ, hbb n β hβ]
        congr 1
        · exact congrArg List.prod (List.attach_map_val (f := fun i => cellWt (ρ' i) (μ' i) ((K i).subgroupOf (B i)) ⟨b n β i, hb i⟩)).symm
        · show q n (a * b n β) = q n fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 (fun j => (⟨b n β j.1, hb j.1⟩ : B j.1)) i).1
          congr 1
          funext i
          by_cases hi : i ∈ l
          · simp [extPt, p, hi]
          · simp [extPt, p, hi, ha1 i hi, h1 i hi]
      · intro β hβ β' hβ' hc
        apply hdist n β hβ β' hβ'
        intro i hi
        obtain ⟨r, hr, a0, ha0, k, hk, e⟩ := hc ⟨i, hi⟩ (List.mem_attach _ _)
        rw [Subgroup.mem_bot] at ha0
        subst ha0
        refine ⟨r.1, Subgroup.mem_subgroupOf.1 hr, 1, (A i).one_mem, k.1, Subgroup.mem_subgroupOf.1 hk, ?_⟩
        have e' := congrArg Subtype.val e
        dsimp only at e'
        simp only [Subgroup.coe_mul, OneMemClass.coe_one, mul_one] at e'
        rw [hv β' hβ', hv β hβ] at e'
        rw [mul_one]
        exact e'
      · intro j _ g
        have hgj : ∀ x : B j.1, (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 (Function.update g j x) i).1) =
            Function.update (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1) j.1 (a j.1 * x.1) := by
          intro x
          rw [extPt_update]
          funext i
          by_cases hi : i = j.1
          · subst hi; simp
          · simp [Function.update_of_ne hi]
        have hj1 : (extPt (H := fun i => ↥(B i)) p 1 g j.1) = g j := extPt_at _ _ _ _
        constructor
        · intro r hr
          have := (hinv n j.1 j.2 (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1)).1 r.1
            (Subgroup.mem_subgroupOf.1 hr)
          show q n _ = q n _
          rw [hgj]
          have hx : a j.1 * (r * g j).1 = r.1 * (a j.1 * (extPt (H := fun i => ↥(B i)) p 1 g j.1).1) := by
            rw [hj1, Subgroup.coe_mul, ← mul_assoc, ← mul_assoc, (hS j.1 j.2).comm _ (ha j.1) _ r.2]
          rw [hx]
          exact this
        · intro k hk
          have := (hinv n j.1 j.2 (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1)).2 k.1
            (Subgroup.mem_subgroupOf.1 hk)
          show q n _ = q n _
          rw [hgj]
          have hx : a j.1 * (g j * k).1 = (a j.1 * (extPt (H := fun i => ↥(B i)) p 1 g j.1).1) * k.1 := by
            rw [hj1, Subgroup.coe_mul, mul_assoc]
          rw [hx]
          exact this
      · intro g _ hne
        obtain ⟨β, hβ, hc⟩ := hsupp n _ (hg1 g) hne
        refine ⟨β, hβ, fun j _ => ?_⟩
        obtain ⟨r, hr, a', ha', k, hk, e⟩ := hc j.1 j.2
        have hs := hS j.1 j.2
        have hbB : b n β j.1 ∈ B j.1 := (hw n β hβ).2.1 j.1
        have hkB : k ∈ B j.1 := hs.le hk
        have hgB : (g j).1 ∈ B j.1 := (g j).2
        dsimp only at e
        rw [extPt_at] at e
        obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ = (g j).1 * k⁻¹ * (b n β j.1)⁻¹ := ⟨_, rfl⟩
        have hr₀B : r₀ ∈ B j.1 := hr₀ ▸ mul_mem (mul_mem hgB (inv_mem hkB)) (inv_mem hbB)
        have hrr : r = (a j.1 * a'⁻¹) * r₀ := by
          have hc' : a'⁻¹ * r₀ = r₀ * a'⁻¹ := hs.comm _ (inv_mem ha') _ hr₀B
          calc r = (r * a' * b n β j.1 * k) * k⁻¹ * (b n β j.1)⁻¹ * a'⁻¹ := by group
            _ = a j.1 * r₀ * a'⁻¹ := by rw [← e, hr₀]; group
            _ = a j.1 * (a'⁻¹ * r₀) := by rw [hc']; group
            _ = (a j.1 * a'⁻¹) * r₀ := by group
        have hr₀R : r₀ ∈ R j.1 := (hs.split _ (mul_mem (ha j.1) (inv_mem ha')) _ hr₀B (by rw [← hrr]; exact hr)).2
        refine ⟨⟨r₀, hr₀B⟩, Subgroup.mem_subgroupOf.2 hr₀R, 1, Subgroup.one_mem _, ⟨k, hkB⟩, Subgroup.mem_subgroupOf.2 hk, ?_⟩
        apply Subtype.ext
        show (g j).1 = r₀ * 1 * (bb n β j.1).1 * k
        rw [hv β hβ, hr₀]
        group
    have hlin := (GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr (Subtype p) (fun j => B j.1) (fun j => (R j.1).subgroupOf (B j.1)) (fun j => ρ' j.1)
      (fun j => μ' j.1) l.attach 1).1 (Fin 2) Finset.univ α (fun n => ∑ β ∈ S n, w n β * q n (a * b n β)) qn
      (fun n _ => hcell n)
    rw [hrel a ha ha1] at hlin
    have ht := niter_sub p ρ' μ' (fun bb : ∀ i, B i => ∑ n ∈ Finset.univ, α n * q n fun i => a i * (bb i).1) 1 l.attach 1 0 hlin
    have e1 : extPt p (1 : ∀ i, B i) (1 : ∀ j : Subtype p, B j.1) = 1 := by
      funext i; simp [extPt]
    rw [e1, List.attach_map_subtype_val] at ht
    exact ht

end GlobalTheory.RowVal
