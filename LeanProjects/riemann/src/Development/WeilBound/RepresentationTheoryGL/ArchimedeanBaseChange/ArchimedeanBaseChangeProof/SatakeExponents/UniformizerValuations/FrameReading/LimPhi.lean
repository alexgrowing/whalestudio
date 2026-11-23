import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev chComm {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb)
    (hg : ∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op))
    (hX : ∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) (hXs : IsSelfAdjoint X) : CommRing (ChAlg g X) :=
  StarAlgebra.adjoinCommRingOfComm ℂ
    (by
      rintro u (⟨x, rfl⟩ | rfl) v (⟨y, rfl⟩ | rfl)
      · exact (hg x y).1
      · exact ((hX x).1).symm
      · exact (hX y).1
      · rfl)
    (by
      rintro u (⟨x, rfl⟩ | rfl) v (⟨y, rfl⟩ | rfl)
      · exact (hg x y).2
      · rw [hXs.star_eq]; exact ((hX x).1).symm
      · exact (hX y).2
      · rw [hXs.star_eq])

def genO {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) : Option Γ → (B.Hb →L[ℂ] B.Hb) :=
  fun o => o.elim X fun x => (g x).op

theorem range_genO {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) :
    Set.range (genO g X) = gOps g ∪ {X} := by
  ext z
  constructor
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Or.inr rfl
    | some x => exact Or.inl ⟨x, rfl⟩
  · rintro (⟨x, rfl⟩ | rfl)
    · exact ⟨some x, rfl⟩
    · exact ⟨none, rfl⟩

def letter {B : Block E} {Γ : Type} (g : Γ → BGen B) (tX : PT B) : Option Γ × Bool → BGen B
  | (none, false) => Sum.inr tX
  | (none, true) => Sum.inr tX.adj
  | (some x, false) => g x
  | (some x, true) => (g x).adj

theorem letter_ok (hO : BlockOperatorsProductAdjoint) (hW : BlockWordOperators) {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (tX t₀ : PT B) (hg : ∀ x, (g x).Ok) (htX : tX.Ok) (hX : X = tX.op) (h₀ : t₀.Ok)
    (p : Option Γ × Bool) :
    (letter g tX p).Ok ∧ (letter g tX p).op = if p.2 then star (genO g X p.1) else genO g X p.1 := by
  have hadj := (hW E B [] t₀ 0 (by simp) h₀ le_rfl (by simp)).2.2.2.2.1
  obtain ⟨o, s⟩ := p
  cases o with
  | none =>
    cases s with
    | false => exact ⟨htX, hX.symm⟩
    | true =>
      have := hO E B tX tX htX htX
      refine ⟨this.2.2.2.2.1, ?_⟩
      show tX.adj.op = star X
      rw [this.2.2.2.2.2.1, hX, ContinuousLinearMap.star_eq_adjoint]
  | some x =>
    cases s with
    | false => exact ⟨hg x, rfl⟩
    | true =>
      refine ⟨(hadj (g x) (hg x)).1, ?_⟩
      show (g x).adj.op = star (g x).op
      rw [(hadj (g x) (hg x)).2, ContinuousLinearMap.star_eq_adjoint]

theorem phiEx (hO : BlockOperatorsProductAdjoint) (hW : BlockWordOperators) (hS : BlockLinearCombinations) (hA : AdjWords) {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (tX t₀ : PT B) (hg : ∀ x, (g x).Ok) (htX : tX.Ok) (hX : X = tX.op) (h₀ : t₀.Ok)
    (y : ChAlg g X) : ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ ((y : B.Hb →L[ℂ] B.Hb) * t₀.op) := by
  have hy : (y : B.Hb →L[ℂ] B.Hb) ∈ StarAlgebra.adjoin ℂ (Set.range (genO g X)) := by
    rw [range_genO]; exact y.2
  obtain ⟨J, hJ, c, w, L, -, hyw, -⟩ := hA (B.Hb →L[ℂ] B.Hb) (Option Γ) (genO g X) _ hy
  have hl := letter_ok hO hW g X tX t₀ hg htX hX h₀

  let bw : J → List (BGen B) := fun j => (w j).map (letter g tX)
  have bok : ∀ j, ∀ b ∈ bw j, b.Ok := fun j b hb => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hb
    exact (hl p).1
  have bop : ∀ j, ((bw j).map BGen.op).prod = wdVal (genO g X) (w j) := fun j => by
    simp only [bw, wdVal, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    exact (hl p).2
  let R : J → ℝ := fun j => ((bw j).map fun b => Sum.elim (fun _ => (0 : ℝ)) (fun s => |s.T| + |s.r + B.c|) b).sum
  have hR0 : ∀ j, 0 ≤ R j := fun j => by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hz
    rcases b with _ | s
    · exact le_rfl
    · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hRs : ∀ j, ∀ s, Sum.inr s ∈ bw j → s.T ≤ R j ∧ s.r + B.c ≤ R j := fun j s hs => by
    have hle : |s.T| + |s.r + B.c| ≤ R j := by
      have := List.single_le_sum (l := (bw j).map fun b => Sum.elim (fun _ => (0 : ℝ)) (fun s => |s.T| + |s.r + B.c|) b)
        (fun z hz => by
          obtain ⟨b, -, rfl⟩ := List.mem_map.1 hz
          rcases b with _ | s
          · exact le_rfl
          · exact add_nonneg (abs_nonneg _) (abs_nonneg _))
        _ (List.mem_map.2 ⟨Sum.inr s, hs, rfl⟩)
      exact this
    exact ⟨(le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans hle),
      (le_abs_self _).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans hle)⟩
  have hwd := fun j => hW E B (bw j) t₀ (R j) (bok j) h₀ (hR0 j) (hRs j)
  have hsum := hS E B.a B.b B.D B.I J Finset.univ (fun j => c j * BGen.sc (bw j)) (fun j => (BGen.wd (bw j) t₀).Φ)
    (fun j => (BGen.wd (bw j) t₀).op) (fun j _ => by
      have := hO E B _ _ (hwd j).1 (hwd j).1
      exact ⟨this.1, this.2.1⟩)
  refine ⟨_, hsum.1, ?_⟩
  convert hsum.2 using 1
  rw [hyw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, ← bop, (hwd j).2.1, smul_smul]

end PositivityTheory.Rg.BcB.F.Rd

end
