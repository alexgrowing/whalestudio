import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVTOver

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.StdPairCoord

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_lat_iff {D : D7} {p : SplitPt D k} {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank)
    (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)} (h : β.IsLat L Λ) (x : Fin S.rank → k) :
    x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := by
  rw [h x, GlobalTheory.SeeSaw.StdOff.mem_latV_int hL]
  exact forall_congr' fun r =>
    ((p.int_iff _).trans (and_iff_right (GlobalTheory.SeeSaw.StdOff.sec_mem_idAt p _)).symm).symm

theorem hasVal_mulVec {n : ℕ} (Q : Pair k (Fin n)) (b' : Matrix (Fin n) (Fin n) k) (s : Fin n → 𝒪[k])
    (h : ∀ r, Q.HasVal (b' *ᵥ Pi.single r 1) (residue 𝒪[k] (s r))) (y : Fin n → 𝒪[k]) :
    Q.HasVal (b' *ᵥ fun r => (y r : k)) (∑ r, residue 𝒪[k] (y r) * residue 𝒪[k] (s r)) := by
  have h1 : ∀ t : Finset (Fin n), Q.HasVal (∑ r ∈ t, y r • (b' *ᵥ Pi.single r 1))
      (∑ r ∈ t, residue 𝒪[k] (y r) * residue 𝒪[k] (s r)) := fun t => by
    induction t using Finset.induction_on with
    | empty => exact ⟨by simp, by simp only [Finset.sum_empty]; exact map_zero Q.fn⟩
    | insert r t hr ih =>
      rw [Finset.sum_insert hr, Finset.sum_insert hr]
      exact ((h r).smul _).add ih
  convert h1 Finset.univ using 1
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.AdForm.StdPairCoord

open GlobalTheory.AdForm.StdPairCoord in

theorem GlobalTheory.AdForm.stdT_pair_coords : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)) (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)), GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ i (r₀ : Fin ((I.rec7 l Z).sp.X j).rank), r₀.1 + 1 = ((I.rec7 l Z).sp.X j).rank → ∀ (x : Fin ((I.rec7 l Z).sp.X j).rank → k) (a : 𝓀[k]), (Q j i).HasVal x a ↔ ∃ y : Fin ((I.rec7 l Z).sp.X j).rank → 𝒪[k], (∀ r, (y r : k) = ((β j i).b *ᵥ x) r) ∧ ∃ s : 𝒪[k], (s : k) = (p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E))) ∧ a = residue 𝒪[k] (s * y r₀) := by
  intro B X I l Z u k _ _ _ _ ι p β Q L hS j hj i r₀ hr₀ x a
  obtain ⟨-, hT⟩ := hS
  obtain ⟨hL, hT'⟩ := hT j hj
  obtain ⟨hlat, hfn⟩ := hT' i
  have hmem := mem_lat_iff hL (β j i) hlat
  have hs : ∀ r, ∃ s : 𝒪[k], (s : k) = (if r = r₀ then (p i).pr (incA (I.rec7 l Z)
      (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E))) else 0) ∧
      (Q j i).HasVal ((β j i).b' *ᵥ Pi.single r 1) (residue 𝒪[k] s) := fun r => by
    have hz : (Pi.single r 1 : Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E) ∈ L j := (hL _).2 fun t => by
      rw [Pi.single_apply]
      split_ifs
      exacts [isIntegral_one, isIntegral_zero]
    obtain ⟨s, hs1, hs2⟩ := hfn _ hz r₀ hr₀
    have e : (fun r' => (p i).pr (incA (I.rec7 l Z) ((Pi.single r 1 : Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E) r'))) =
        Pi.single r 1 := funext fun r' => by
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs
      · rw [map_one, map_one]
      · rw [map_zero, map_zero]
    rw [e] at hs2
    refine ⟨s, ?_, hs2⟩
    rw [hs1, Pi.single_apply]
    by_cases h : r₀ = r
    · subst h
      rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero, map_zero, map_zero]
  choose s hs using hs
  have key : ∀ y : Fin ((I.rec7 l Z).sp.X j).rank → 𝒪[k], (Q j i).HasVal ((β j i).b' *ᵥ fun r => (y r : k))
      (residue 𝒪[k] (s r₀ * y r₀)) := fun y => by
    have h1 := hasVal_mulVec (Q j i) (β j i).b' s (fun r => (hs r).2) y
    convert h1 using 1
    rw [Finset.sum_eq_single r₀ (fun r _ hr => ?_) (fun h => (h (Finset.mem_univ _)).elim), map_mul, mul_comm]
    have : s r = 0 := Subtype.ext ((hs r).1.trans (if_neg hr))
    rw [this, map_zero, mul_zero]
  constructor
  · intro h
    have hx := (hmem x).1 h.mem
    refine ⟨fun r => ⟨_, hx r⟩, fun r => rfl, s r₀, (hs r₀).1.trans (if_pos rfl), h.unique ?_⟩
    have := key fun r => ⟨_, hx r⟩
    rwa [show ((β j i).b' *ᵥ fun r => (((⟨_, hx r⟩ : 𝒪[k]) : k))) = x by
      rw [show (fun r => (((⟨_, hx r⟩ : 𝒪[k]) : k))) = (β j i).b *ᵥ x from rfl, Matrix.mulVec_mulVec, (β j i).b'b,
        Matrix.one_mulVec]] at this
  · rintro ⟨y, hy, s', hs', rfl⟩
    obtain rfl : s' = s r₀ := Subtype.ext (hs'.trans ((hs r₀).1.trans (if_pos rfl)).symm)
    have hx : x = (β j i).b' *ᵥ fun r => (y r : k) := by
      rw [show (fun r => (y r : k)) = (β j i).b *ᵥ x from funext hy, Matrix.mulVec_mulVec, (β j i).b'b, Matrix.one_mulVec]
    rw [hx]
    exact key y

end
