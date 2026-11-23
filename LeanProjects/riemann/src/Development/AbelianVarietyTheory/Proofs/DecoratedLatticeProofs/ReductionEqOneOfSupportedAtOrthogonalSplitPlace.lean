import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpZeroMemLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffPlaceRed

theorem pr_add_conj_eq_zero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (a : Formalism.L2.Theta.AE D)
    (h : a * (q.e + cA D q.e) = 0) : q.pr a = 0 := by
  have h1 : q.pr q.e = 1 := by
    have h2 := q.pr_sec 1
    have h3 := q.sec_pr 1
    rw [map_one, mul_one] at h3
    rwa [h3] at h2
  have h4 : q.pr (cA D q.e) = 0 := by
    have := congrArg q.pr q.split.2.1
    rwa [map_mul, h1, one_mul, map_zero] at this
  have := congrArg q.pr h
  rwa [map_mul, map_add, h1, h4, add_zero, mul_one, map_zero] at this

theorem bc_eq_one_of_isRed {S κ k : Type} [CommRing S] [CommRing κ] [Field k] [ValuativeRel k] {φ : S →+* κ}
    {ψ : S →+* k} (hred : GlobalTheory.FunObj.Comparison₂.IsRed φ ψ) {n : ℕ} (m : GL (Fin n) S) (h : Formalism.UG.bc ψ m = 1) :
    Formalism.UG.bc φ m = 1 := by
  apply Units.ext
  ext i j
  have h6 : ψ (m.val i j) = (1 : Matrix (Fin n) (Fin n) k) i j :=
    congrArg (fun x : GL (Fin n) k => x.val i j) h
  show φ (m.val i j) = (1 : Matrix (Fin n) (Fin n) κ) i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq] at h6 ⊢
    have h7 := (hred.ker (m.val i i - 1)).2 (by
      rw [map_sub, map_one, h6, sub_self, map_zero]; exact zero_lt_one)
    rwa [map_sub, map_one, sub_eq_zero] at h7
  · rw [Matrix.one_apply_ne hij] at h6 ⊢
    refine (hred.ker (m.val i j)).2 ?_
    rw [h6, map_zero]; exact zero_lt_one

theorem bc_comp_eq_one {S A k : Type} [CommRing S] [CommRing A] [CommRing k] (ι : S →+* A) (π : A →+* k) {n : ℕ}
    (m : GL (Fin n) S) (β x : GL (Fin n) A) (hx : β * Formalism.UG.bc ι m * β⁻¹ = x) (h : Formalism.UG.bc π x = 1) :
    Formalism.UG.bc (π.comp ι) m = 1 := by
  rw [← hx, map_mul, map_mul, map_inv, mul_inv_eq_one, mul_eq_left] at h
  exact h

theorem redFn_eq_one_of_suppAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (e : Formalism.L2.Theta.AE D), (e + cA D e) * (q.e + cA D q.e) = 0 → ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (g : GA D V), Formalism.L2.Theta.SuppAt e V g → finE V g ∈ St β → redFn β PP (finE V g) = 1 := by
  intro D k _ _ _ _ q PP hq e he V β g hg hst
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D k q PP hq
  obtain ⟨m, hm⟩ := hst
  have h0 : q.pr (e + cA D e) = 0 := pr_add_conj_eq_zero q _ he
  have h1 : (finE V g).val.map π' = 1 := by
    ext i j
    have h2 : q.pr ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
      rw [← hg i j, map_mul, h0, zero_mul]
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h2
    show π' (toEAf D (Formalism.L2.Theta.mt V g i j)) = _
    rw [hπ, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : Formalism.UG.bc π' (finE V g) = 1 := Units.ext h1
  rw [← hm, redFn_frGL]
  exact bc_eq_one_of_isRed hred m (bc_comp_eq_one _ π' m β _ hm h3)

end GlobalTheory.OffPlaceRed

end
