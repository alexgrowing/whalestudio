import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorDisjointSupportSmulAdd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix GlobalTheory.FinPl GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OverSwap

variable {D : D7}

theorem eq_zero_of_two {v v' : Pl D} (hne : v ≠ v') {z : AE D} (h : z ∈ idAt D (· = v))
    (h' : z ∈ idAt D (· = v')) : z = 0 := by
  have hc : compAt D v z = 0 := by
    unfold idAt at h'
    exact (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 h').2 ⟨v, hne⟩
  rw [GlobalTheory.FinPl.Model.eq_single h, hc]
  exact (GlobalTheory.AdelicU.Supp.singleTens D.host.E v).map_zero'

theorem cA_mem_idAt {v : Pl D} {y : AE D} (h : y ∈ idAt D (· = v)) : cA D y ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

theorem symplO_eq_zero_of_ne {v v' : Pl D} (hne : v ≠ v') {S T : HSp D} {x y : WO S T} (hx : MxAt (· = v) x)
    (hy : MxAt (· = v') y) : symplO S T x y = 0 := by
  have hh : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : cA D (y c b) * x d a = 0 :=
      eq_zero_of_two hne (Ideal.mul_mem_left _ _ (hx d a)) (Ideal.mul_mem_right _ _ (cA_mem_idAt (hy c b)))
    calc incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a
        = incA D (S.gram⁻¹ a b) * incA D (T.gram c d) * (cA D (y c b) * x d a) := by ring
      _ = 0 := by rw [h0, mul_zero]
  unfold symplO
  rw [hh, mul_zero, map_zero]

theorem comb_comm {v v' : Pl D} (hne : v ≠ v') (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {c c' : WO S T →₀ ℂ}
    (hc : CombAt (· = v) c) (hc' : CombAt (· = v') c') (f : WO S T → ℂ) :
    GlobalTheory.SeeSaw.comb ψ S T c (GlobalTheory.SeeSaw.comb ψ S T c' f) = GlobalTheory.SeeSaw.comb ψ S T c' (GlobalTheory.SeeSaw.comb ψ S T c f) :=
  (GlobalTheory.HeisComb.main D ψ S T).2.1 c c' (fun x hx y hy => symplO_eq_zero_of_ne hne (hc x hx) (hc' y hy)) f

end GlobalTheory.FinPl.OverSwap

namespace GlobalTheory.FinPl

open GlobalTheory.FinPl.OverSwap in

theorem overSwap : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p p' : SplitPt D k) (n n' m m' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype m]
    [DecidableEq m] [Fintype m'] [DecidableEq m'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA →
    p'.UnitAA → p.v ≠ p'.v → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (α' : Frame p' S m')
    (β' : Frame p' T m) (LS : Lat S) (LT : Lat T) (f₀ g h : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ)
    (Ψ' : Matrix m m' k → ℂ), Vac ψ S T LS LT (· = p'.v) f₀ → Over ψ α β LS LT f₀ Ψ g →
      Over ψ α' β' LS LT g Ψ' h → ∃ g', Over ψ α' β' LS LT f₀ Ψ' g' ∧ Over ψ α β LS LT g' Ψ h := by
  intro D k _ _ _ _ p p' n n' m m' _ _ _ _ _ _ _ _ ψ hψ hp hp' hne S T α β α' β' LS LT f₀ g h Ψ Ψ' hv' hO1 hO2
  obtain ⟨hLS, hLT, hf₀, hΨ, -⟩ := id hO1
  obtain ⟨-, -, hg, hΨ', -⟩ := id hO2
  obtain ⟨c, hc, hcO⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hψ hp S T α β LS LS LT LT hLS hLT hLS hLT).2 Ψ hΨ
  obtain ⟨c', hc', hcO'⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p' m m' ψ hψ hp' S T α' β' LS LS LT LT hLS hLT hLS hLT).2 Ψ' hΨ'
  have eg : g = GlobalTheory.SeeSaw.comb ψ S T c f₀ :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ S T α β LS LT hLS hLT f₀ hf₀).1 Ψ hΨ).unique hO1 (hcO f₀ hf₀)
  have eh : h = GlobalTheory.SeeSaw.comb ψ S T c' g :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p' m m' ψ hψ S T α' β' LS LT hLS hLT g hg).1 Ψ' hΨ').unique hO2 (hcO' g hg)
  have hO3 := hcO' f₀ hv'
  have hvac : Vac ψ S T LS LT (· = p.v) (GlobalTheory.SeeSaw.comb ψ S T c' f₀) :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p' m m' ψ hψ S T α' β' LS LT hLS hLT f₀ hv').2.1 Ψ' _ hO3).2 LS LT (· = p.v)
      (fun e => hne e.symm) hf₀
  refine ⟨_, hO3, ?_⟩
  have e : h = GlobalTheory.SeeSaw.comb ψ S T c (GlobalTheory.SeeSaw.comb ψ S T c' f₀) := by
    rw [eh, eg, comb_comm hne ψ hc hc']
  rw [e]
  exact hcO _ hvac

end GlobalTheory.FinPl

end
