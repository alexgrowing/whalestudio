import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TermBasic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_smul (n : S.GLV) (Λ : Submodule L.O S.V) (x : S.V) :
    x ∈ n • Λ ↔ ∃ y ∈ Λ, n y = x :=
  Submodule.mem_smul_pointwise_iff_exists x n Λ

theorem smul_eq_map (n : S.GLV) (Λ : Submodule L.O S.V) :
    n • Λ = Λ.map (n.toLinearMap.restrictScalars L.O) := by
  ext x
  rw [mem_smul, Submodule.mem_map]
  rfl

theorem isSD_smul {n : S.GLV} (hn : n ∈ isomG L S.Hm) {Λ : Submodule L.O S.V} (h : IsSD L S.Hm Λ) :
    IsSD L S.Hm (n • Λ) := by
  obtain ⟨⟨hfg, hsp⟩, hd⟩ := h
  have hn' : ∀ x y, hf L S.Hm (n x) (n y) = hf L S.Hm x y := hn
  refine ⟨⟨by rw [smul_eq_map]; exact hfg.map _, ?_⟩, fun y => ?_⟩
  · have : ((n • Λ : Submodule L.O S.V) : Set S.V) = n.toLinearMap '' (Λ : Set S.V) := by
      rw [smul_eq_map]; rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨y, rfl⟩ := n.surjective y
    constructor
    · intro h
      refine (mem_smul S n Λ _).2 ⟨y, (hd y).1 fun x hx => ?_, rfl⟩
      rw [← hn']
      exact h _ ((mem_smul S n Λ _).2 ⟨x, hx, rfl⟩)
    · intro h x hx
      obtain ⟨y', hy', e⟩ := (mem_smul S n Λ _).1 h
      obtain ⟨x', hx', rfl⟩ := (mem_smul S n Λ _).1 hx
      rw [← e, hn']
      exact (hd y').2 hy' x' hx'

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun a (ha : (a : ℕ) < i) => lt_of_lt_of_le ha h)

theorem self_mem (g : Fin (r + 1) → S.V) {i : Fin (r + 1)} {j : ℕ} (h : (i : ℕ) < j) :
    g i ∈ S.spanTo g j := Submodule.subset_span ⟨i, h, rfl⟩

theorem spanTo_top (g : Fin (r + 1) → S.V) :
    S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
  have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
    ext i; simpa using i.2
  rw [Frames.spanTo, hs, Set.image_univ]

section
variable {S} {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
include hg

theorem sub_mem {n : S.GLV} (hn : n ∈ S.Nof g) (i : Fin (r + 1)) : n (g i) - g i ∈ S.spanTo g i := by
  obtain ⟨⟨-, h2⟩, h3⟩ := hn
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine h3.2 _ ?_
    rw [Frames.spanTo, StdLat.image_lt, StdLat.mem_perp_span]
    exact hg _
  · exact (Subgroup.mem_iInf.1 h2 i).2 _ (self_mem S g (by simp))

theorem map_mem {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) {x : S.V} (hx : x ∈ S.spanTo g j) :
    n x ∈ S.spanTo g j := by
  have : S.spanTo g j ≤ (S.spanTo g j).comap n.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h1 := (S.spanTo g j).add_mem (spanTo_mono S g (le_of_lt hi) (sub_mem hg hn i))
      (self_mem S g hi)
    rw [sub_add_cancel] at h1
    exact h1
  exact this hx

theorem map_mem_iff {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) (x : S.V) :
    n x ∈ S.spanTo g j ↔ x ∈ S.spanTo g j := by
  refine ⟨fun h => ?_, map_mem hg hn j⟩
  have := map_mem hg ((S.Nof g).inv_mem hn) j h
  have e : n⁻¹ (n x) = x := n.symm_apply_apply x
  rwa [e] at this

theorem trace_smul {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V} {j : ℕ}
    (h : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g j) ↔ x ∈ Submodule.span L.O (g '' {i | (i : ℕ) < j})) (x : S.V) :
    (x ∈ n • Λ ∧ x ∈ S.spanTo g j) ↔
      x ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}) := by
  have e : Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}) =
      n • Submodule.span L.O (g '' {i | (i : ℕ) < j}) := by
    rw [smul_eq_map, Submodule.map_span, Set.image_image]; rfl
  rw [e, mem_smul, mem_smul]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h2⟩
    exact ⟨y, (h y).1 ⟨hy, (map_mem_iff hg hn j y).1 h2⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, ((h y).2 hy).1, rfl⟩, map_mem hg hn j ((h y).2 hy).2⟩

end

theorem inner_smul {g : Fin (r + 1) → S.V} {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V}
    (x : S.V) :
    (∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r) ↔
      ∃ y ∈ n • Λ, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  obtain ⟨h1, h2⟩ := hn.2
  constructor
  · rintro ⟨y, hy, hp, hx⟩
    refine ⟨n y, (mem_smul S n Λ _).2 ⟨y, hy, rfl⟩, (h1 y).2 hp, ?_⟩
    have := (S.spanTo g r).add_mem (h2 y hp) hx
    rwa [sub_add_sub_cancel] at this
  · rintro ⟨_, hy, hp, hx⟩
    obtain ⟨y, hy0, rfl⟩ := (mem_smul S n Λ _).1 hy
    refine ⟨y, hy0, (h1 y).1 hp, ?_⟩
    have := (S.spanTo g r).sub_mem hx (h2 y ((h1 y).1 hp))
    rwa [sub_sub_sub_cancel_left] at this

theorem term_basic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → IsSD L S.Hm Λ ∧ S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 ∧ S.M d Λ ≤ S.sat Λ ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f j) ↔ x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < j})) ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' j) ↔ x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < j})) ∧ LinearIndependent E (Sum.elim (S.fr d Λ) (S.fr' d Λ)) ∧ S.IsIntCls (S.Fr d Λ) ∧ ∀ d', S.IsTerm d' Λ → d' = d := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  have hW : S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 := by
    rw [Frames.wit, dif_pos hT]
    exact hT.choose_spec
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  obtain ⟨hli, -, -, -, -, hth, -⟩ := FrameBasic.main L r k S
  have det : ∀ d : S.Datum, S.IsTerm d Λ →
      (∀ x, x ∈ d.1 ↔ ∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo S.f r) ∧ y - x ∈ S.spanTo S.f r) ∧
      (∀ x, x ∈ d.2.1 ↔ ∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo S.f' r) ∧ y - x ∈ S.spanTo S.f' r) ∧
      d.2.2 = S.graphOf Λ := by
    rintro d ⟨p, hA, hA', hn, hn', e, e', -, hgr⟩
    refine ⟨fun x => ?_, fun x => ?_, hgr⟩
    · rw [(StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA).2.2 x, inner_smul S hn, ← e]
    · rw [(StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA').2.2 x, inner_smul S hn', ← e']
  obtain ⟨hA, hA', hn, hn', e, e', hth', hgr⟩ := id hW
  obtain ⟨s1, s2, -⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA
  obtain ⟨-, s2', -⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA'
  have hSD : IsSD L S.Hm Λ := by
    have := isSD_smul S hn.1.1 s1
    rwa [← e] at this
  have t : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f j) ↔
      x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < j}) := fun j hj x => by
    have := trace_smul hg hn (s2 j hj) x
    rwa [← e] at this
  have t' : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' j) ↔
      x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < j}) := fun j hj x => by
    have := trace_smul hg' hn' (s2' j hj) x
    rwa [← e'] at this
  have m : ∀ b, S.fr d Λ b ∈ Λ ∧ S.fr d Λ b ∈ S.spanTo S.f (r + 1) := fun b =>
    (t _ le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)
  have m' : ∀ b, S.fr' d Λ b ∈ Λ ∧ S.fr' d Λ b ∈ S.spanTo S.f' (r + 1) := fun b =>
    (t' _ le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)
  refine ⟨hSD, hW, ?_, t, t', ?_, ⟨⟨_, hn, _, hn', rfl⟩, ?_⟩, fun d' hd' => ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨(m b).1, Submodule.mem_sup_left (m b).2⟩
    · refine ⟨?_, S.ME.smul_mem _ (S.ME.sub_mem (Submodule.mem_sup_right (m' b).2)
        (Submodule.mem_sup_left (m b).2))⟩
      obtain ⟨y, hy, e2⟩ := hth' b
      have e3 : S.fr' d Λ b - S.fr d Λ b = algebraMap F E S.th • y := e2
      simp only [e3, smul_smul, ← map_mul, inv_mul_cancel₀ hth, map_one, one_smul]
      exact hy
  · obtain ⟨l1, l2, l3⟩ := linearIndependent_sum.1 hli
    refine LinearIndependent.sum_type (l1.map' (S.wit d Λ).1.toLinearMap (LinearEquiv.ker _))
      (l2.map' (S.wit d Λ).2.toLinearMap (LinearEquiv.ker _)) (l3.mono ?_ ?_)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have := (m b).2
      rw [spanTo_top] at this
      exact this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have := (m' b).2
      rw [spanTo_top] at this
      exact this
  · rintro p ⟨A, A', hi, hi', -, -, -, h1, h2⟩ a b
    refine (hSD.2 _).2 ?_ _ ?_
    · rw [h1]
      exact Λ.sum_mem fun i _ => Λ.smul_mem (⟨_, hi i a⟩ : L.O) (m i).1
    · rw [h2]
      exact Λ.sum_mem fun i _ => Λ.smul_mem (⟨_, hi' i b⟩ : L.O) (m' i).1
  · obtain ⟨a1, a2, a3⟩ := det d hT
    obtain ⟨b1, b2, b3⟩ := det d' hd'
    exact Prod.ext (Submodule.ext fun x => (b1 x).trans (a1 x).symm)
      (Prod.ext (Submodule.ext fun x => (b2 x).trans (a2 x).symm) (b3.trans a3.symm))

end GlobalTheory.HL.TermBasic
