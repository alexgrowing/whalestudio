import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BlockSumMultiplicities
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SecondTwistSmallIffExactlyAtAndFinClause
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField

noncomputable section

namespace GlobalTheory.SmallJumpExample

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW GlobalTheory.IndefiniteRowSideFullHecke
open scoped Formalism.Per

theorem isField_bdR (D : D7) (l : ℕ) [Fact l.Prime] : IsField (D.loc l).R.BdR :=
  MulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1 (D.locT l).eD.toMulEquiv

section Count

variable {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (n : ℕ)

def dj (y : ℤ) : ℤ :=
  if s then -(⌊P.e j⌋ + y + ((R.t : ℤ) + 1) / 2) else ⌊P.e j⌋ + y - ((R.t : ℤ) + 1) / 2

theorem card_small : ((jT2 P j s).filter fun u : ℤ => |u| ≤ (n : ℤ)).card =
    (Finset.univ.filter fun i : Fin (R.k - 1) => |dj P j s ⌊P.v i⌋| ≤ (n : ℤ)).card +
    (Finset.univ.filter fun i : Fin R.m => |dj P j s (-⌊P.b i⌋)| ≤ (n : ℤ)).card := by
  obtain ⟨c, hc⟩ := R.t_odd
  have h : jT2 P j s = (Finset.univ : Finset (Fin (R.k - 1))).val.map (fun i => dj P j s ⌊P.v i⌋) +
      (Finset.univ : Finset (Fin R.m)).val.map (fun i => dj P j s (-⌊P.b i⌋)) := by
    cases s <;>
      simp only [jT2, GlobalTheory.HTW.jW, cloud, lows, dj, Multiset.map_add, Multiset.map_map, if_true,
        Bool.false_eq_true, if_false] <;>
      congr 1 <;> refine Multiset.map_congr rfl fun i _ => ?_ <;>
      simp only [Function.comp] <;> omega
  rw [h, Multiset.filter_add, Multiset.card_add, Multiset.filter_map, Multiset.filter_map,
    Multiset.card_map, Multiset.card_map]
  rfl

end Count

variable {D : D7} (L : SizeData₂ D)

theorem lows_small (g : D.R.GG) (j : Fin D.R.m) (s : Bool) (i : Fin D.R.m) :
    |dj (hcAt D g) j s (-⌊(hcAt D g).b i⌋)| ≤ (etaHat L : ℤ) := by
  have h := L.be_close (D.eTau.symm ⟨plc g, plc_mem g⟩) i j
  change |((((hcAt D g).b i - (hcAt D g).e j : ℚ)) : ℝ)| ≤ _ at h
  obtain ⟨b, hb⟩ := (hcAt D g).b_int i
  obtain ⟨e, he⟩ := (hcAt D g).e_int j
  have h1 : (((b - e).natAbs : ℕ) : ℝ) ≤ L.etaSz := by
    rw [hb, he] at h
    rw [Nat.cast_natAbs]
    push_cast at h ⊢
    exact h
  have h2 := Nat.le_floor h1
  unfold dj etaHat
  rw [hb, he, Int.floor_intCast, Int.floor_intCast, abs_le]
  push_cast
  split_ifs <;> omega

theorem cloud_large (g : D.R.GG) (j : Fin D.R.m) (s : Bool)
    (h : (etaHat L : ℤ) < szT (hcAt D g) j s) (i : Fin (D.R.k - 1)) :
    ¬ |dj (hcAt D g) j s ⌊(hcAt D g).v i⌋| ≤ (etaHat L : ℤ) := by
  have h0 := (L.cloud_v (D.eTau.symm ⟨plc g, plc_mem g⟩) i).1
  have h1 : 0 ≤ ⌊(hcAt D g).v i⌋ := Int.floor_nonneg.2 (by exact_mod_cast h0)
  unfold dj
  unfold szT at h
  rw [abs_le]
  split_ifs at h ⊢ <;> omega

theorem count_eq (g : D.R.GG) (j : Fin D.R.m) (s : Bool)
    (h : (etaHat L : ℤ) < szT (hcAt D g) j s) :
    ((jT2 (hcAt D g) j s).filter fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
  rw [card_small, Finset.filter_false_of_mem fun i _ => cloud_large L g j s h i,
    Finset.filter_true_of_mem fun i _ => lows_small L g j s i]
  simp

end GlobalTheory.SmallJumpExample
