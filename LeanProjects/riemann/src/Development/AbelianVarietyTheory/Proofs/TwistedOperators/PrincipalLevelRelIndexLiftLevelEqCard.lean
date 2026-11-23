import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevIdx

open Formalism.IndefR.Lev (finE)

variable {D : D7} {T0 : Type} (C : LevCh D T0) (i : Fin D.R.m)

theorem mem_levG_datWp (P : LevelP C.Pg D.R.r ℂ) (κ : GA D (Wc D i)) :
    κ ∈ levG (Wc D i) (C.βW i) (C.datWp i P) ↔ κ ∈ GfC (Wc D i) ∧
      finE (Wc D i) κ ∈ parLev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i C.triv) ∧
      rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) κ) ∈ P.H := by
  rw [levG, Formalism.IndefR.Lev.mem_levA]
  refine and_congr_right fun _ => ?_
  exact Iff.rfl

def blkHom (P : LevelP C.Pg D.R.r ℂ) : levG (Wc D i) (C.βW i) (C.datWp i P) →* G0 C.Pg D.R.r where
  toFun κ := rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) κ.1)
  map_one' := by
    show rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) 1) = 1
    rw [map_one]; exact rTup_one
  map_mul' x y := by
    show rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) (x.1 * y.1)) = _
    rw [map_mul]
    exact rTup_mul (hc := D.sp.cm) (J := (Wc D i).gram) ((mem_levG_datWp C i P _).1 x.2).2.1
      ((mem_levG_datWp C i P _).1 y.2).2.1

theorem ker_blkHom (P : LevelP C.Pg D.R.r ℂ) :
    (blkHom C i P).ker = (levG (Wc D i) (C.βW i) (C.datWp i C.triv)).subgroupOf
      (levG (Wc D i) (C.βW i) (C.datWp i P)) := by
  ext κ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_levG_datWp C i C.triv]
  obtain ⟨hG, hpar, -⟩ := (mem_levG_datWp C i P κ.1).1 κ.2
  constructor
  · intro h1
    exact ⟨hG, hpar, Subgroup.mem_bot.2 h1⟩
  · rintro ⟨-, -, hb⟩
    exact Subgroup.mem_bot.1 hb

theorem range_blkHom {μ0 : T0} (hC : C.Is μ0) (P : LevelP C.Pg D.R.r ℂ) : (blkHom C i P).range = P.H := by
  ext g
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨κ, rfl⟩
    exact ((mem_levG_datWp C i P κ.1).1 κ.2).2.2
  · intro hg
    obtain ⟨c, hB⟩ := hC.βW i
    have hsep := (GlobalTheory.StepLifts.places_apart C hC μ0).1
    obtain ⟨κ, hG, hpar, hred⟩ := GlobalTheory.ParahoricLift.liftsExist (Wc D i) (C.βW i) (C.datWp i C.triv) (C.ΛW i) _ hB
      (fun PP hPP PP' hPP' => hsep PP hPP PP' (hPP'.elim Or.inl fun h => absurd h (Finset.notMem_empty PP')))
      (Finset.disjoint_empty_right _) g
    have hmem : κ ∈ levG (Wc D i) (C.βW i) (C.datWp i P) := by
      refine (mem_levG_datWp C i P κ).2 ⟨hG, hpar, ?_⟩
      rw [hred]
      exact hg
    exact ⟨⟨κ, hmem⟩, hred⟩

theorem levidx : ∀ (D : D7) (T0 : Type) (C : LevCh D T0) (μ0 : T0), C.Is μ0 → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → C.Pg ⊆ Z → ∀ (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ), levG (Wc D i) (C.βW i) (C.datWp i C.triv) ≤ levG (Wc D i) (C.βW i) (C.datWp i P) ∧ (levG (Wc D i) (C.βW i) (C.datWp i C.triv)).relIndex (levG (Wc D i) (C.βW i) (C.datWp i P)) = Nat.card P.H ∧ Nat.card P.H ≠ 0 := by
  intro D T0 C μ0 hC _ _ _ _ i P
  have hle : levG (Wc D i) (C.βW i) (C.datWp i C.triv) ≤ levG (Wc D i) (C.βW i) (C.datWp i P) := by
    intro κ hκ
    obtain ⟨h1, h2, h3⟩ := (mem_levG_datWp C i C.triv κ).1 hκ
    refine (mem_levG_datWp C i P κ).2 ⟨h1, h2, ?_⟩
    rw [Subgroup.mem_bot.1 h3]
    exact P.H.one_mem
  refine ⟨hle, ?_, Nat.card_pos.ne'⟩
  rw [Subgroup.relIndex, ← ker_blkHom C i P, Subgroup.index_ker, range_blkHom C i hC P]

end GlobalTheory.LevIdx
