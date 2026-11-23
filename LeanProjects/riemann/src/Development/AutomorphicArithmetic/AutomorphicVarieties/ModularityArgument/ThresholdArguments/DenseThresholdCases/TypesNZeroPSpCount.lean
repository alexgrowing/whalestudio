import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroSDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spCount
section Abstract
variable {M W : Type} [Group M] [AddCommGroup W] [Module ℂ W]
end Abstract
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ}
variable (G : Grp k n)
end Local
end UpperTheory.TNZ.Grp.P_spCount
namespace UpperTheory.TNZ.Grp
open P_spCount
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open scoped Classical in
set_option maxHeartbeats 800000 in
theorem step_spCount_alt {n : ℕ} (G : Grp k n) : G.Step_spCount_alt := by
  intro hL c hc hres
  have hE : G.etaSp (jacU G.e (prinSeries c)) =
      eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta (jac G.e (parInd (points (Fin n)) (ρc c))) :=
    eS_jacU_eq G.e (parInd (points (Fin n)) (ρc c)) G.eta
  obtain ⟨N, b, hb⟩ := (hL.loc.geo k).1 (Fin n) (Fin G.s) (Fin n) (fun _ => Unit)
    (fun a => Fin (G.d a)) (points (Fin n)) G.e
  obtain ⟨S, hmono, h0, hN, hS⟩ := hb ℂ (ρc c) (isSmooth_ρc c hc)
  obtain ⟨fr⟩ : Nonempty (∀ t : Fin N, ∀ i, (Σ j, Fin ((b t).1 i j)) ≃ (fun _ : Fin n => Unit) i) :=
    ⟨fun t => (b t).nonempty_rows.some⟩
  obtain ⟨gc⟩ : Nonempty (∀ t : Fin N, ∀ j, (Σ i, Fin ((b t).1 i j)) ≃ (fun a : Fin G.s => Fin (G.d a)) j) :=
    ⟨fun t => (b t).nonempty_cols.some⟩
  have hr : ∀ t : Fin N, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (subQuot (S t.succ) (S t.castSucc))) ≤ Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a)))
        G.eta (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := by
    intro t
    have e : Nonempty ((subQuot (S t.succ) (S t.castSucc)).Equiv
        (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := hS t (fr t) (gc t)
    exact rank_eS_le_of_equiv _ _ e.some
  have hr1 : ∀ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) ≤
        ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := by
    intro t
    split_ifs with hP
    · refine (rank_eS_le (gc t) (cellRep G c (b t) (fr t) (gc t)) G.eta).trans
        ((rank_quotient_le _).trans (le_of_eq ?_))
      rw [Module.rank_self, Nat.cast_one]
    · refine (rank_eS_eq_zero _ _ _ ?_).trans_le zero_le
      intro F hF
      by_contra hne
      apply hP
      intro i a h
      by_contra hab
      apply G.dist a (G.bl i) hab
      refine MonoidHom.ext fun w => ?_
      have h1 := cell_char G c (b t) (fr t) (gc t) F hF hne i a h w
      have h2 : c i (unitIncl k w) = G.μ (G.bl i) (unitIncl k w) := DFunLike.congr_fun (hres i) w
      exact h1.symm.trans h2
  have hsum : ∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) ≤ 1 := by
    rw [← Finset.card_filter]
    refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    exact b.injective (good_unique G ht ht')
  have hrank : Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 := by
    calc _ ≤ ∑ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
          (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) :=
          rank_le_of_filtration _ _ S hmono h0 hN _ hr
      _ ≤ ∑ t : Fin N, ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := Finset.sum_le_sum fun t _ => hr1 t
      _ = ((∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) : ℕ) : Cardinal) := (Nat.cast_sum _ _).symm
      _ ≤ 1 := by exact_mod_cast hsum
  haveI : Module.Free ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) := Module.Free.of_divisionRing ℂ _
  have hfin : FiniteDimensional ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.one_lt_aleph0)
  have hfr : Module.finrank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 :=
    Module.finrank_le_of_rank_le (n := 1) (by rw [Nat.cast_one]; exact hrank)
  rw [hE]
  exact ⟨hfin, hfr⟩
end UpperTheory.TNZ.Grp
end
end
