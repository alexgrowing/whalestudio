import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.OneMapBase

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Scale

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

theorem phi_smul (u : ℂ) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : C.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    O.phi (u • cc) f h = u * O.phi cc f h := by
  show u * cc _ * _ * _ = u * (cc _ * _ * _)
  ring

theorem equivAt_smul (u : ℂ) {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (h : O.EquivAt κ cc) : O.EquivAt κ (u • cc) := by
  intro g k hk f hf
  obtain ⟨h1, h2⟩ := h g k hk f hf
  refine ⟨h1, fun x => ?_⟩
  rw [phi_smul, phi_smul, h2 x]
  ring

theorem phRat_smul (u : ℂ) {v₀ : (R.MW i (sg0 D A)).Vec} {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} {ph : ℂ}
    (h : O.PhRat κ v₀ cc ph) : O.PhRat κ v₀ (u • cc) (u * ph) := by
  intro x
  obtain ⟨n, a, f, hf⟩ := h x
  refine ⟨n, a, f, fun y => ?_⟩
  rw [mul_assoc, hf y, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [phi_smul]
  ring

end Scale

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m)

theorem oneMapRow0_of_rows (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ)
    (hpins : OMPins T R κ v₀ O i)
    (hequiv : (O i).EquivAt (κ i) cc)
    (hid : OneMapRow (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (Wc D i)
      (unfBC (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c')) (O i).dict (O i).mu (xiR D) (wtA (κ i))
      (actLev (O i).c' (O i).lev2) (O i).dδ (O i).Cl' (O i).w (O i).La (O i).Nc (O i).gam (O i).vol (O i).ep (O i).io
      (O i).thAd (O i).Plc D.what₂.embLL.toRatAlgHom.fieldRange
      (cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) cc ph)
    (hrat : (O i).PhRat (κ i) (v₀ i (sg0 D A)) cc ph) :
    OneMapRow0 T R κ v₀ O i :=
  ⟨cc, ph, hequiv, ⟨hpins.1.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ (O i).hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O i).hle _ _ hpins.2.act.1).2, hid⟩, hrat⟩

theorem oneMapRow0_of_rows_smul (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph u u' : ℂ) (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hpins : OMPins T R κ v₀ O i)
    (hequiv : (O i).EquivAt (κ i) (u • cc))
    (hid : OneMapRow (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (Wc D i)
      (unfBC (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c')) (O i).dict (O i).mu (xiR D) (wtA (κ i))
      (actLev (O i).c' (O i).lev2) (O i).dδ (O i).Cl' (O i).w (O i).La (O i).Nc (O i).gam (O i).vol (O i).ep (O i).io
      (O i).thAd (O i).Plc D.what₂.embLL.toRatAlgHom.fieldRange
      (cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) cc ph)
    (hrat : (O i).PhRat (κ i) (v₀ i (sg0 D A)) (u' • cc) (u' * ph)) :
    OneMapRow0 T R κ v₀ O i := by
  have h1 := equivAt_smul (O i) (κ i) u⁻¹ hequiv
  have h2 := phRat_smul (O i) (κ i) u'⁻¹ hrat
  rw [inv_smul_smul₀ hu] at h1
  rw [inv_smul_smul₀ hu', inv_mul_cancel_left₀ hu'] at h2
  exact oneMapRow0_of_rows T R κ v₀ O i cc ph hpins h1 hid h2

end GlobalTheory.OneMapBase
