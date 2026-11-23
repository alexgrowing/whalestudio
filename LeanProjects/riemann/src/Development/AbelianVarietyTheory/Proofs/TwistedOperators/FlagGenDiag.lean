import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCore
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

variable {D : D7}

section Rescale

variable {S S₀ : HSp D} {ρ : ℕ}

theorem sandwich {m n : ℕ} (A : Matrix (Fin S.rank) (Fin m) D.host.E) (B : Matrix (Fin S.rank) (Fin n) D.host.E)
    (P : Matrix (Fin m) (Fin m) D.host.E) (Q : Matrix (Fin n) (Fin n) D.host.E) :
    (A * P)ᴴ * S.gram * (B * Q) = Pᴴ * (Aᴴ * S.gram * B) * Q := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

def diagDec (d : HypDec S S₀ ρ) (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) : HypDec S S₀ ρ where
  e := d.e * diagonal l
  e' := d.e' * diagonal fun a => (star (l a))⁻¹
  i₀ := d.i₀
  ee := by rw [sandwich, d.ee, Matrix.mul_zero, Matrix.zero_mul]
  e'e' := by rw [sandwich, d.e'e', Matrix.mul_zero, Matrix.zero_mul]
  e'e := by
    rw [sandwich, d.e'e, Matrix.mul_one, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply, star_inv₀, star_star]
    exact inv_mul_cancel₀ (hl a)
  iso := d.iso
  i₀e := by rw [← Matrix.mul_assoc, d.i₀e, Matrix.zero_mul]
  i₀e' := by rw [← Matrix.mul_assoc, d.i₀e', Matrix.zero_mul]
  rank_add := d.rank_add

theorem perp_diag {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0)
    (x : Fin S.rank → D.host.E) (hx : ((e * diagonal l)ᴴ * S.gram).mulVec x = 0) : (eᴴ * S.gram).mulVec x = 0 := by
  rw [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, ← mulVec_mulVec] at hx
  funext j
  have := congrFun hx j
  rw [mulVec_diagonal] at this
  simp only [Pi.zero_apply, Pi.star_apply, mul_eq_zero, star_eq_zero] at this
  rcases this with h | h
  · exact absurd h (hl j)
  · exact h

theorem flagGen_diag {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) (g : GA D S)
    (hg : (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne S g).mulVec (ratV fun k => e k i) = (e.map (incA D)).mulVec a) ∧
      ∀ x : Fin S.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * S.gram).mulVec x = 0 →
        ∃ a : Fin ρ → AE D, (subOne S g).mulVec (ratV x) = (e.map (incA D)).mulVec a) :
    (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne S g).mulVec (ratV fun k => (e * diagonal l) k i) = ((e * diagonal l).map (incA D)).mulVec a) ∧
      ∀ x : Fin S.rank → D.host.E,
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (e * diagonal l) * S.gram).mulVec x = 0 →
        ∃ a : Fin ρ → AE D, (subOne S g).mulVec (ratV x) = ((e * diagonal l).map (incA D)).mulVec a := by
  have hmv : ∀ a : Fin ρ → AE D, ((e * diagonal l).map (incA D)).mulVec (fun j => incA D (l j)⁻¹ * a j) =
      (e.map (incA D)).mulVec a := fun a => by
    funext k
    simp only [mulVec, dotProduct, Matrix.map_apply, mul_diagonal]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_assoc, ← mul_assoc (incA D (l j)), ← map_mul, mul_inv_cancel₀ (hl j), map_one, one_mul]
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha0, ha⟩ := hg.1 i
    refine ⟨fun j => incA D (l j)⁻¹ * (incA D (l i) * a j), fun j hj => ?_, ?_⟩
    · show incA D (l j)⁻¹ * (incA D (l i) * a j) = 0
      rw [ha0 j hj, mul_zero, mul_zero]
    have hcol : (ratV fun k => (e * diagonal l) k i) = incA D (l i) • ratV fun k => e k i := by
      funext k
      show incA D ((e * diagonal l) k i) = incA D (l i) * incA D (e k i)
      rw [mul_diagonal, map_mul, mul_comm]
    rw [hcol, mulVec_smul, ha, ← mulVec_smul, ← hmv]
    rfl
  · have h1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (e * diagonal l) = (e * diagonal l)ᴴ := rfl
    have h2 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e = eᴴ := rfl
    rw [h1] at hx
    obtain ⟨a, ha⟩ := hg.2 x (by rw [h2]; exact perp_diag l hl x hx)
    exact ⟨_, ha.trans (hmv a).symm⟩

theorem nFlag_diag (e : Matrix (Fin S.rank) (Fin ρ) D.host.E) (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) :
    NFlag S (e * diagonal l) = NFlag S e := by
  have hl' : ∀ a, (l a)⁻¹ ≠ 0 := fun a => inv_ne_zero (hl a)
  have e0 : diagonal l * diagonal (fun a => (l a)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (hl a)
  have e1 : e * diagonal l * diagonal (fun a => (l a)⁻¹) = e := by
    rw [Matrix.mul_assoc, e0, Matrix.mul_one]
  unfold NFlag
  congr 1
  ext g
  refine ⟨fun h => ?_, fun h => flagGen_diag l hl g h⟩
  have := flagGen_diag (e := e * diagonal l) (fun a => (l a)⁻¹) hl' g h
  rwa [e1] at this

def trMeas {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (ν : Measure N) : Measure N' := h ▸ ν

def trSet {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (𝓝 : Set N) : Set N' := h ▸ 𝓝

theorem isUnit_trans {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (ν : Measure N) (𝓝 : Set N)
    (hu : ν.IsHaarMeasure ∧ IsFundamentalDomain ((GQ S).subgroupOf N) 𝓝 ν ∧ ν 𝓝 = 1) :
    (trMeas h ν).IsHaarMeasure ∧ IsFundamentalDomain ((GQ S).subgroupOf N') (trSet h 𝓝) (trMeas h ν) ∧
      trMeas h ν (trSet h 𝓝) = 1 := by
  subst h
  exact hu

def volNOf {S₀' : HSp D} {ρ' : ℕ} {d : HypDec S S₀ ρ} {d' : HypDec S S₀' ρ'} (h : NFlag S d.e = NFlag S d'.e)
    (v : VolN d) : VolN d' :=
  ⟨trMeas h v.ν, trSet h v.𝓝, isUnit_trans h v.ν v.𝓝 v.unit⟩

end Rescale

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj

variable {T : Type}

noncomputable def splitFam {S : Arrow T → Type} {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z), (p.comp q).Fam S → p.Fam S × q.Fam S
  | _, .nil, d => (d, ())
  | _, .snoc _ q, d => ((splitFam q d.1).1, ((splitFam q d.1).2, d.2))

theorem all_splitFam {S : Arrow T → Type} (P : ∀ a, S a → Prop) {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : (p.comp q).Fam S), Path.Fam.All P d →
      Path.Fam.All P (splitFam q d).1 ∧ Path.Fam.All P (splitFam q d).2
  | _, .nil, _, h => ⟨h, trivial⟩
  | _, .snoc _ q, d, h => ⟨(all_splitFam P q d.1 h.1).1, (all_splitFam P q d.1 h.1).2, h.2⟩

noncomputable def getD {S : Arrow T → Type} (t : T) (i : ℕ) : ∀ (n : ℕ), (downPath t i n).Fam S → ∀ j, j < n → S (.down t i j)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, j, h =>
    if hj : j < n then getD t i n (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).2 j hj
    else (show n = j by omega) ▸ (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).1.2

theorem getD_all {S : Arrow T → Type} (P : ∀ a, S a → Prop) (t : T) (i : ℕ) :
    ∀ (n : ℕ) (d : (downPath t i n).Fam S), Path.Fam.All P d → ∀ j (h : j < n), P (.down t i j) (getD t i n d j h)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, hd, j, h => by
    have hs := all_splitFam P (p := Path.one (.down t i n)) (downPath t i n) d hd
    unfold getD
    split_ifs with hj
    · exact getD_all P t i n _ hs.2 j hj
    · obtain rfl : n = j := by omega
      exact hs.1.2

end GlobalTheory.RowChain
