import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
open CategoryTheory.Limits
open GlobalTheory.Twist (resM app_resM)

set_option autoImplicit false

namespace GlobalTheory.FlagCls

theorem exists_adapted_upTo {Y : Scheme.{0}} {N : Y.Modules} {r : ℕ} (fl : Vert.Flag N r) {p : Y} {U : Y.Opens}
    (hp : p ∈ U) (k : Fin (r + 1)) :
    ∃ (W : Y.Opens) (s : ℕ → Γ(N, W)), W ≤ U ∧ p ∈ W ∧ ∀ j : Fin (r + 1), j ≤ k →
      ∃ t : Fin j → Γ(fl.F j, W), IsFrame t ∧ ∀ i : Fin j, (fl.ι j).app W (t i) = s i := by
  induction k using Fin.induction with
  | zero =>
    obtain ⟨W, e, -, hpW, hWU, he⟩ := (fl.isVB 0).exists_affine hp
    refine ⟨W, fun _ => 0, hWU, hpW, fun j hj => ?_⟩
    obtain rfl : j = 0 := Fin.le_zero_iff.1 hj
    exact ⟨e, he, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨W, s, hWU, hpW, H⟩ := ih
    obtain ⟨V, c, -, hpV, hVW, hc⟩ := (fl.isVB_gr k).exists_affine hpW
    obtain ⟨T, hTV, hpT, u, hu⟩ := VBExt.exists_lifts (fl.π k) c hpV
    have hTW : T ≤ W := hTV.trans hVW
    refine ⟨T, fun n => if n = k then (fl.ι k.succ).app T (u 0) else resM N hTW (s n),
      hTW.trans hWU, hpT, fun j hj => ?_⟩
    rcases hj.lt_or_eq with hj | rfl
    · have hj' : j ≤ k.castSucc := Fin.le_castSucc_iff.2 hj
      obtain ⟨t, ht, e⟩ := H j hj'
      refine ⟨_, ht.res hTW, fun i => ?_⟩
      have : (i : ℕ) ≠ k := by
        have h1 := i.2
        have h2 : (j : ℕ) ≤ k := hj'
        omega
      simp only [if_neg this]
      rw [app_resM, e]
    · obtain ⟨t, ht, e⟩ := H k.castSucc le_rfl
      have hS : (ShortComplex.mk (fl.step k) (cokernel.π (fl.step k)) (cokernel.condition _)).ShortExact :=
        { exact := ShortComplex.exact_cokernel _ }
      have hu' : IsFrame fun i => (fl.π k).app T (u i) := by
        rw [funext hu]; exact hc.res hTV
      have hf := (VBExt.isFrame_sumElim hS (ht.res hTW) hu').comp_equiv
        (finSumFinEquiv (m := k) (n := 1)).symm
      refine ⟨_, hf, fun i : Fin (k + 1) => ?_⟩
      induction i using Fin.addCases with
      | left i =>
        have : ((Fin.castAdd 1 i : Fin (k + 1)) : ℕ) ≠ k := i.2.ne
        simp only [if_neg this, Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
        refine (QCoh.app_app _ _ _ _).trans ?_
        rw [fl.step_ι, app_resM]
        exact congrArg _ (e i)
      | right i =>
        obtain rfl : i = 0 := Subsingleton.elim _ _
        have : ((Fin.natAdd k (0 : Fin 1) : Fin (k + 1)) : ℕ) = k := rfl
        simp only [if_pos this, Function.comp_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

theorem exists_adapted : ∀ (Y : Scheme.{0}) (N : Y.Modules) (r : ℕ) (fl : Vert.Flag N r) (p : Y) (U : Y.Opens),
    p ∈ U → ∃ (W : Y.Opens) (s : Fin r → Γ(N, W)), W ≤ U ∧ p ∈ W ∧ Adapted fl s := by
  intro Y N r fl p U hp
  obtain ⟨W, s, hWU, hpW, H⟩ := exists_adapted_upTo fl hp (Fin.last r)
  refine ⟨W, fun i => s i, hWU, hpW, ?_, fun k => H k (Fin.le_last k)⟩
  obtain ⟨t, ht, e⟩ := H (Fin.last r) le_rfl
  have := ht.map_iso (fl.ι (Fin.last r))
  rw [funext e] at this
  exact this

end GlobalTheory.FlagCls
