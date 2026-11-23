import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxGood

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good2

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem mem_R_none {p : PlF D} (hA : Agree δ M p) (hs : (M p).split = none) (x : (D.s.atP p).Ep) :
    x ∈ (M p).R ↔ x ∈ (D.s.atP p).O := by
  obtain ⟨-, -, -, hO, -, -⟩ := hA
  show x ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R ↔ _
  rw [hs]
  show x ∈ (M p).L.O ↔ _
  rw [hO]

theorem bOf_int {p : PlF D} (g : Formalism.L2.SG.Pf.VolPinAsm.StG w)
    (hg : ∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O)
    (hpv : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (Formalism.L2.SG.Pf.pv w.1 a) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE ((Formalism.L2.SG.Pf.pv w.1 a)⁻¹) ∈ (D.s.atP p).O) :
    ∀ i j, (D.s.atP p).ιE (Formalism.L2.SG.Pf.VolPinAsm.bOf w g i j) ∈ (D.s.atP p).O := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ x, σ (σ x) = x := Formalism.L2.SG.Pf.fσ_fσ w
  set ν : Fin (D.R.rS + 1) → D.host.E := fun x => Formalism.L2.SG.Pf.pv w.1 x
  have hν : ∀ x, IsUnit (ν x) := fun x => isUnit_iff_ne_zero.2 (Formalism.L2.SG.Pf.pv_ne' w x)
  set a := ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)
  set b := Formalism.L2.SG.Pf.VolPinAsm.bOf w g
  obtain ⟨-, hb, hW⟩ := ProdE.bOf_spec w g
  have hfix := fix_cOf hσ ν hν a
  have hWu : IsUnit (ptMat w).det := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit w
  have hcb : cOf σ ν a * b = 1 := by
    have h1 : ptMat w * (cOf σ ν a * b) = ptMat w * 1 := by
      rw [Matrix.mul_one, ← Matrix.mul_assoc]
      conv_lhs => rw [ptMat_mono]
      rw [← hfix, ← ptMat_mono]
      exact hW
    have := congrArg (fun X => (ptMat w)⁻¹ * X) h1
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul] using this
  have hbinv : b = (cOf σ ν a)⁻¹ := (Matrix.inv_eq_right_inv hcb).symm
  have hcU : IsUpUni (cOf σ ν a) := by
    have := (ZsVolGrp.isUpUni_inv hb).1
    rwa [show b⁻¹ = cOf σ ν a from Matrix.inv_eq_left_inv hcb] at this
  have hdet : (cOf σ ν a).det = 1 :=
    ZsVolGrp.det_up (fun x => (hcU x x).2 rfl) (fun x y hxy => (hcU x y).1 hxy)
  have hcO : ∀ x y, (D.s.atP p).ιE (cOf σ ν a x y) ∈ (D.s.atP p).O := by
    intro x y
    simp only [cOf, Matrix.of_apply, Ring.inverse_eq_inv', map_mul]
    exact (D.s.atP p).O.mul_mem ((D.s.atP p).O.mul_mem (hpv (σ x)).2 (hg _ _)) (hpv (σ y)).1
  intro i j
  rw [hbinv, ZsVolGrp.inv_eq_adj hdet]
  have e := congrFun (congrFun (RingHom.map_adjugate (D.s.atP p).ιE (cOf σ ν a)) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
  rw [e]
  exact ZsVolGrp.adj_mem (D.s.atP p).O (fun x y => by simpa using hcO x y) i j

end Good2

end Formalism.L2.SG.Pf.ProdEApprox
