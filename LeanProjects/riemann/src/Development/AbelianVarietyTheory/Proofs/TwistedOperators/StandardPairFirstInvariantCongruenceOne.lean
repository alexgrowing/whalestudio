import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitCharEqOfNatCong

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdFstInv

theorem mul_sub_mem {R : Type} [CommRing R] (O : Subring R) (c : R) {b a : ℕ} (Z : Matrix (Fin b) (Fin b) R)
    (hZ : ∀ i j, ∃ w ∈ O, Z i j - (1 : Matrix (Fin b) (Fin b) R) i j = c * w)
    (Y : Matrix (Fin b) (Fin a) R) (hY : ∀ i j, Y i j ∈ O) (i : Fin b) (j : Fin a) :
    ∃ w ∈ O, (Z * Y) i j - Y i j = c * w := by
  choose w hwO hw using hZ
  refine ⟨∑ k, w i k * Y k j, O.sum_mem fun k _ => O.mul_mem (hwO i k) (hY k j), ?_⟩
  have hsplit : (Z * Y) i j - Y i j = ∑ k, (Z i k - (1 : Matrix (Fin b) (Fin b) R) i k) * Y k j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.one_mul]
  rw [hsplit, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hw i k, mul_assoc]

theorem mem_iff {R : Type} [CommRing R] (O : Subring R) (J : Ideal O) (N : ℕ) (hN : (N : O) ∈ J) {p q w : R}
    (hp : p ∈ O) (hw : w ∈ O) (h : q - p = (N : R) * w) :
    (∃ h : q ∈ O, (⟨q, h⟩ : O) ∈ J) ↔ ∃ h : p ∈ O, (⟨p, h⟩ : O) ∈ J := by
  have hq : q ∈ O := by
    have e : q = p + (N : R) * w := by linear_combination h
    rw [e]
    exact O.add_mem hp (O.mul_mem (natCast_mem O N) hw)
  have key : (⟨q, hq⟩ : O) = ⟨p, hp⟩ + (N : O) * ⟨w, hw⟩ := by
    apply Subtype.ext
    show q = p + ((N : O) : R) * w
    rw [show ((N : O) : R) = (N : R) from map_natCast O.subtype N]
    linear_combination h
  have hNw : (N : O) * ⟨w, hw⟩ ∈ J := J.mul_mem_right _ hN
  constructor
  · rintro ⟨_, hJ⟩
    refine ⟨hp, ?_⟩
    rw [key] at hJ
    exact (J.add_mem_iff_left hNw).1 hJ
  · rintro ⟨_, hJ⟩
    refine ⟨hq, ?_⟩
    rw [key]
    exact J.add_mem hJ hNw

theorem fixed_mul {R : Type} [CommRing R] {b a : ℕ} (e : R) (M : Matrix (Fin b) (Fin b) R) (x : Matrix (Fin b) (Fin a) R)
    (H : ∀ i j, e * x i j = x i j) (i : Fin b) (j : Fin a) : e * (M * x) i j = (M * x) i j := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, H k j]

theorem fixed_iff {R : Type} [CommRing R] {b a : ℕ} (e : R) (M : GL (Fin b) R) (P : Matrix (Fin a) (Fin a) R) (hP : P = 1)
    (x : Matrix (Fin b) (Fin a) R) :
    (∀ i j, e * (M.val * x * P) i j = (M.val * x * P) i j) ↔ ∀ i j, e * x i j = x i j := by
  subst hP
  simp only [Matrix.mul_one]
  constructor
  · intro h i j
    have hx : x = (M⁻¹).val * (M.val * x) := by
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [hx]
    exact fixed_mul e _ _ h i j
  · intro h i j
    exact fixed_mul e _ _ h i j

variable {D : D7}

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V (1 : GA D V)⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [inv_one, map_one, Units.val_one]

theorem actO_neg_one (A WW : HSp D) (κ : GA D WW) (x : WO A WW) :
    actO (GlobalTheory.Grid.neg A) WW 1 κ x = actO A WW 1 κ x := by
  unfold actO
  rw [mt_one, mt_one]

theorem isHalf_iff (A WW : HSp D) (κ : GA D WW) (e : AE D) (x : WO A WW) :
    IsHalf e (actO A WW 1 κ x) ↔ IsHalf e x := by
  unfold IsHalf actO
  exact fixed_iff e (matHom WW κ) _ (mt_one A) x

theorem frMapO_eq {A WW : HSp D} (βA : GL (Fin A.rank) (Lev.EAf D)) {βW : GL (Fin WW.rank) (Lev.EAf D)}
    {κ : GA D WW} {z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hz : Formalism.L2.DIV.frGL βW z = Lev.finE WW κ) (x : WO A WW) :
    frMapO A WW βA βW (actO A WW 1 κ x) =
      ((intGL D.host.F D.host.E _ z⁻¹)⁻¹).val * frMapO A WW βA βW x *
        (intGL D.host.F D.host.E _ (1 : GL (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))).val := by
  have h1 := GlobalTheory.FrameRed.frMapO_actO (βS := βA) (βT := βW) (g := (1 : GA D A)) (h := κ⁻¹)
    (y := 1) (z := z⁻¹) (by rw [map_one, map_one]) (by rw [map_inv, map_inv, hz]) x
  rw [inv_one, inv_inv] at h1
  exact h1
set_option maxHeartbeats 1600000 in

theorem frMapO_eq' {A WW : HSp D} (βA : GL (Fin A.rank) (Lev.EAf D)) {βW : GL (Fin WW.rank) (Lev.EAf D)}
    {κ : GA D WW} {z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hz : Formalism.L2.DIV.frGL βW z = Lev.finE WW κ) (x : WO A WW) :
    frMapO A WW βA βW (actO A WW 1 κ x) = (intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x := by
  rw [frMapO_eq βA hz x, map_inv (intGL D.host.F D.host.E WW.rank), inv_inv,
    map_one (intGL D.host.F D.host.E A.rank), Units.val_one, Matrix.mul_one]

theorem topL_int {b a : ℕ} (k : ℕ) {Y : Matrix (Fin b) (Fin a) (Lev.EAf D)} (hY : IsIntM (D := D) Y) :
    IsIntM (D := D) (topL k Y) := by
  intro i j
  unfold topL
  split_ifs with hij
  · exact hY _ _
  · exact zero_mem _

theorem topL_sub {R : Type} [CommRing R] (O : Subring R) (c : R) {b a : ℕ} (k : ℕ) {Y Y' : Matrix (Fin b) (Fin a) R}
    (h : ∀ i j, ∃ w ∈ O, Y' i j - Y i j = c * w) (i j : Fin k) :
    ∃ w ∈ O, topL k Y' i j - topL k Y i j = c * w := by
  unfold topL
  split_ifs with hij
  · exact h _ _
  · exact ⟨0, O.zero_mem, by rw [sub_self, mul_zero]⟩
set_option maxHeartbeats 1600000 in

theorem stdFst_actO : ∀ (D : D7) (A WW : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin A.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ((N : ℕ) : 𝓞 D.host.E) ∈ I → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ (κ : GA D WW) (z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), Formalism.L2.DIV.frGL βW z = Lev.finE WW κ → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin WW.rank) (Fin WW.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w) → ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (actO (GlobalTheory.Grid.neg A) WW 1 κ x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW x := by
  intro D A WW ν e Sf hSf I βA βW N hN hNI hNS hν κ z hz hz1 x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [actO_neg_one, isHalf_iff, frMapO_eq' βA hz x]
  have hInt : IsIntM (D := D) ((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) ↔
      IsIntM (D := D) (frMapO A WW βA βW x) := by
    have h2 := GlobalTheory.FrameRed.isIntM_iff (D := D) z⁻¹
      (1 : GL (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (frMapO A WW βA βW x)
    rwa [map_inv (intGL D.host.F D.host.E WW.rank), inv_inv, map_one (intGL D.host.F D.host.E A.rank),
      Units.val_one, Matrix.mul_one] at h2
  by_cases hM : IsIntM (D := D) (frMapO A WW βA βW x)
  · have hc : ∀ i j, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
        ((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) i j - frMapO A WW βA βW x i j =
          (N : Lev.EAf D) * w :=
      mul_sub_mem (Formalism.L2.Herm.intAf D.host.F D.host.E) (N : Lev.EAf D) (intGL D.host.F D.host.E _ z).val hz1 _ hM
    have hNJ : ((N : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ Formalism.L2.DIV.idS D.host.F I := by
      rw [← map_natCast (Formalism.L2.DIV.oToS D.host.F D.host.E) N]
      exact Ideal.mem_map_of_mem _ hNI
    have hId : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) i j) ↔
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA βW x i j) := fun i j => by
      obtain ⟨w, hw, hq⟩ := hc i j
      exact GlobalTheory.StdFstInv.mem_iff _ _ N hNJ (hM i j) hw hq
    have hU := GlobalTheory.UnitCharCong.unitChar_eq_of_natCong D ν e Sf hSf N hN hNS hν _ _ (topL_int A.rank hM)
      (topL_sub _ _ A.rank hc)
    rw [hU]
    have hcond := and_congr (Iff.rfl (a := IsHalf e x)) (and_congr hInt
      (forall_congr' fun (i : Fin WW.rank) => forall_congr' fun (j : Fin A.rank) =>
        imp_congr (Iff.rfl (a := A.rank ≤ (i : ℕ))) (hId i j)))
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hcond.1 h1) h2
    · exact absurd (hcond.2 h2) h1
    · rfl
  · rw [if_neg (fun h => hM (hInt.1 h.2.1)), if_neg (fun h => hM h.2.1)]

end GlobalTheory.StdFstInv

end
