import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSecondBlockOf

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MacInvPf

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MLM
open PositivityTheory.Rg.BcN.F2 (mconv LocOpUniformizer)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mconv_right {a b : ℕ} {w : Pl E} {u v : GLw a w × GLw b w → ℂ} {l : GLw a w × GLw b w}
    (hv : ∀ m, v (m * l) = v m) (m : GLw a w × GLw b w) : mconv u v (m * l) = mconv u v m := by
  unfold mconv
  congr 1
  funext z
  rw [← mul_assoc, hv]

theorem pw_right (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E} {l : GLw a w × GLw (n - a) w}
    (hβ : ∀ x y : d.kap w, ∀ g, (d.betaL a ha).m w x y (g * l) = (d.betaL a ha).m w x y g) (k : ℕ) :
    ∀ (x y : d.kap w) (g : GLw a w × GLw (n - a) w),
      (pw (d.betaL a ha) k).m w x y (g * l) = (pw (d.betaL a ha) k).m w x y g := by
  induction k with
  | zero => exact hβ
  | succ k ih =>
    intro x y g
    show (∑ z, mconv ((d.betaL a ha).m w x z) ((pw (d.betaL a ha) k).m w z y)) (g * l) =
      (∑ z, mconv ((d.betaL a ha).m w x z) ((pw (d.betaL a ha) k).m w z y)) g
    rw [Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun z _ => mconv_right (ih z y) g

theorem macInvOf : MacInvOf := by
  intro h3 h1 E _ _ _ n d hd _ a ha w hw x y
  have hT : w ∉ d.T := fun h => Finset.disjoint_left.1 hd.disj.1 h hw
  have hP : w ∈ d.P := Finset.mem_union_right _ hw
  have hSB : w ∈ d.S₀ ∪ d.Bad := Finset.mem_union_left _ hw
  have hl : d.lev a w = d.L a w := by simp [LocData.lev, hT, hSB]
  have hH : ∀ x y : d.kap w, IsHecke (d.L a w) ((d.betaL a ha).m w x y) := fun x y => by
    have h := PositivityTheory.Rg.BcB.F.LocComm.hecke_beta d (h3 E) hd ha hP x y
    rwa [hl] at h
  refine ⟨hH x y, fun m => ?_⟩
  obtain ⟨ho, hle⟩ := GlobalTheory.CompanionTheory.MatchLMPlaces.L_open_le d hd ha hSB
  refine GlobalTheory.CompanionTheory.FmPowP.mconv_idem_right ho hle _ fun u hu g => ?_
  rw [GlobalTheory.CompanionTheory.MatchLMPlaces.tr_one d _ hP, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  show (∑ z, mconv ((d.fixL a).m w t z) ((pw (d.betaL a ha) m).m w z t)) (g * u) =
    (∑ z, mconv ((d.fixL a).m w t z) ((pw (d.betaL a ha) m).m w z t)) g
  rw [Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun z _ =>
    mconv_right (pw_right d ha (fun x y g => ((hH x y).2 u hu g).2) m z t) g

end GlobalTheory.CompanionTheory.MacInvPf

end
