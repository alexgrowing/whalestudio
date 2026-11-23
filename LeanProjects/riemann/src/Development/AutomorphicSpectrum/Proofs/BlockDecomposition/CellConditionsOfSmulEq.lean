import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfComps
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem isIdem_mul_self_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) : e * e = e := by
  have h : e * e - e = 0 := by
    refine GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D _ (fun w => ?_) (fun v => ?_)
    · rw [RingHom.map_sub, RingHom.map_mul, he.1 w, mul_one, sub_self]
    · rw [RingHom.map_sub, RingHom.map_mul, he.2 v]
      split_ifs
      · rw [mul_one, sub_self]
      · rw [mul_zero, sub_self]
  exact sub_eq_zero.1 h

theorem entry_sub_one_of_bc {B : Type} [CommRing B] (φ : AE D →+* B) {u : G D p}
    (h : Formalism.UG.bc φ (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig (Jst D p) u) = 1)
    (i j : Fin (p + p)) : φ ((mat u - 1) i j) = 0 := by
  have h1 : φ.mapMatrix (mat u) = 1 := congrArg Units.val h
  have h2 : φ.mapMatrix (mat u - 1) = 0 := by
    rw [map_sub, h1, map_one, sub_self]
  exact congrFun (congrFun h2 i) j

theorem smul_mat_sub_one_eq_zero {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {u : G D p}
    (hu : u ∈ KOff D p S) : e • (mat u - 1) = 0 := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.AdelicU.mem_levelOff.1 hu
  have h1' := GlobalTheory.AdelicU.mem_finPts_iff_forall.1 h1
  ext i j
  change e * (mat u - 1) i j = 0
  refine GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D _ (fun w => ?_) (fun v => ?_)
  · have hb := GlobalTheory.AdelicU.matHom_projArch D.sp.cm.sig (Jst D p) w u
    rw [h1' w, map_one] at hb
    rw [RingHom.map_mul, entry_sub_one_of_bc _ (Units.ext (congrArg Units.val hb.symm)) i j, mul_zero]
  · rw [RingHom.map_mul, he.2 v]
    split_ifs with hv
    · have hb := GlobalTheory.AdelicU.matHom_proj D.sp.cm.sig (Jst D p) v u
      rw [h2 v hv, map_one] at hb
      have hc : cv D v ((mat u - 1) i j) = 0 :=
        entry_sub_one_of_bc _ (Units.ext (congrArg Units.val hb.symm)) i j
      rw [hc, mul_zero]
    · rw [zero_mul]

theorem smul_mat_mul_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (g : G D p) {u : G D p}
    (hu : u ∈ KOff D p S) : e • mat (g * u) = e • mat g := by
  have h1 : e • mat u = e • (1 : Mx D (p + p) (p + p)) := by
    have := smul_mat_sub_one_eq_zero he hu
    rwa [smul_sub, sub_eq_zero] at this
  have h2 : mat (g * u) = mat g * mat u := rfl
  rw [h2, ← Matrix.mul_smul, h1, Matrix.mul_smul, mul_one]

theorem smul_lowC_mul_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (g : G D p) {u : G D p}
    (hu : u ∈ KOff D p S) : e • lowC (g * u) = e • lowC g := by
  have h := smul_mat_mul_right he g hu
  ext i j
  exact congrFun (congrFun h _) _

theorem smul_lowD_mul_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (g : G D p) {u : G D p}
    (hu : u ∈ KOff D p S) : e • lowD (g * u) = e • lowD g := by
  have h := smul_mat_mul_right he g hu
  ext i j
  exact congrFun (congrFun h _) _

theorem cell_conditions_of_smul_eq {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] {e : R}
    (hee : e * e = e) {c c' d d' x y : Matrix n n R} (hc : e • c' = e • c) (hd : e • d' = e • d)
    (hxe : e • x = x) (hy : y * c = e • (1 : Matrix n n R)) (hx : c * x = e • d) :
    (e • y) * c' = e • (1 : Matrix n n R) ∧ c' * x = e • d' := by
  constructor
  · rw [Matrix.smul_mul, ← Matrix.mul_smul, hc, Matrix.mul_smul, hy, smul_smul, hee]
  · calc c' * x = c' * (e • x) := by rw [hxe]
      _ = (e • c') * x := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (e • c) * x := by rw [hc]
      _ = c * (e • x) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = c * x := by rw [hxe]
      _ = e • d := hx
      _ = e • d' := hd.symm

theorem isB_of_smul_eq {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {g g' : G D p}
    (hc : e • lowC g' = e • lowC g) (hd : e • lowD g' = e • lowD g) (x : hermS D p e)
    (h : IsB e g x) : IsB e g' x := by
  obtain ⟨⟨y, hy⟩, hx⟩ := h
  have hxe : e • x.1.1 = x.1.1 := x.2
  obtain ⟨h1, h2⟩ := cell_conditions_of_smul_eq (isIdem_mul_self_right he) hc hd hxe hy hx
  exact ⟨⟨e • y, h1⟩, h2⟩

theorem isB_mul_right_iff {D : D7} {p : ℕ} {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e)
    {g u : G D p} (hu : u ∈ KOff D p S) (x : hermS D p e) : IsB e (g * u) x ↔ IsB e g x :=
  ⟨isB_of_smul_eq he (smul_lowC_mul_right he g hu).symm (smul_lowD_mul_right he g hu).symm x,
    isB_of_smul_eq he (smul_lowC_mul_right he g hu) (smul_lowD_mul_right he g hu) x⟩

end GlobalTheory.CompanionTheory.MuC

end
