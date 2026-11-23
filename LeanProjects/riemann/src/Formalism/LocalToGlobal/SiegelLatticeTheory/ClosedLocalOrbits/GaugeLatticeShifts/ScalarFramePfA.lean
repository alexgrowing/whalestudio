import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

section Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem h_swap (x y : V) : H.h x y = M.L.cj (H.h y x) := H.h_herm y x

def hl (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := by simp only [H.h_smul_left, smul_eq_mul, RingHom.id_apply]

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [h_swap H x (y + y'), H.h_add_left, map_add, ← h_swap H x y, ← h_swap H x y']

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [h_swap H x (a • y), H.h_smul_left, map_mul, ← h_swap H x y]

theorem h_zero_right (x : V) : H.h x 0 = 0 := by
  rw [h_swap H x 0, H.h_zero_left, map_zero]

theorem h_neg_left (x y : V) : H.h (-x) y = - H.h x y := by
  rw [← neg_one_smul E x, H.h_smul_left, neg_one_mul]

theorem h_neg_right (x y : V) : H.h x (-y) = - H.h x y := by
  rw [← neg_one_smul E y, h_smul_right H, map_neg, map_one, neg_one_mul]

theorem h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, H.h_add_left, h_neg_left H, ← sub_eq_add_neg]

theorem h_sub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [sub_eq_add_neg, h_add_right H, h_neg_right H, ← sub_eq_add_neg]

theorem h_sum_left {ι : Type} (s : Finset ι) (g : ι → V) (y : V) :
    H.h (∑ i ∈ s, g i) y = ∑ i ∈ s, H.h (g i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]
    exact H.h_zero_left y
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, H.h_add_left, ih]

theorem mem_perp_span (s : Set V) (v : V) :
    v ∈ H.perp (Submodule.span E s) ↔ ∀ x ∈ s, H.h v x = 0 := by
  have key : ∀ S : Submodule E V, v ∈ H.perp S ↔ ∀ x ∈ S, H.h v x = 0 := fun S => Iff.rfl
  rw [key]
  constructor
  · intro hv x hx
    exact hv x (Submodule.subset_span hx)
  · intro hs x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hs y hy
    | zero => exact h_zero_right H v
    | add y z _ _ hy hz => rw [h_add_right H, hy, hz, add_zero]
    | smul a y _ hy => rw [h_smul_right H, hy, mul_zero]

theorem h_eq_of_sub_mem (S : Submodule E V) (hS : ∀ a ∈ S, ∀ b ∈ S, H.h a b = 0)
    {x x₂ y y₂ : V} (hx : x ∈ H.perp S) (hy : y ∈ H.perp S) (ha : x - x₂ ∈ S) (hb : y - y₂ ∈ S) :
    H.h x₂ y₂ = H.h x y := by
  have hx' : ∀ z ∈ S, H.h x z = 0 := hx
  have hy' : ∀ z ∈ S, H.h y z = 0 := hy
  obtain ⟨a, haS, rfl⟩ : ∃ a ∈ S, x₂ = x - a := ⟨x - x₂, ha, (sub_sub_cancel x x₂).symm⟩
  obtain ⟨b, hbS, rfl⟩ : ∃ b ∈ S, y₂ = y - b := ⟨y - y₂, hb, (sub_sub_cancel y y₂).symm⟩
  have hay : H.h a y = 0 := by rw [h_swap H a y, hy' a haS, map_zero]
  rw [h_sub_left H, h_sub_right H, h_sub_right H, hx' b hbS, hay, hS a haS b hbS]
  simp only [sub_zero]

end Gen

section Loc

variable {D : D7}

def sF (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) : (D.s.atP p).Ep := sgnP D p a * frFac Z.δ p a

def sF' (Z : LocDat D) (p : PlF D) (b : Fin (D.R.rS + 1)) : (D.s.atP p).Ep :=
  sgnP' D p b * frFac Z.δ p b

theorem gpart_ne (p : PlF D) : (gpart p : ℚ) ≠ 0 := by
  unfold gpart
  split_ifs <;> simp [(D.host.g_prime _).ne_zero]

theorem unitAt_ne (p : PlF D) : (uP p : D.host.E) ≠ 0 := by
  unfold uP
  have h1 : gpart p ≠ 0 := by exact_mod_cast gpart_ne p
  have h2 : Lat.gS D ≠ 0 := by
    unfold Lat.gS
    exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  simp [h1, h2]

theorem isUnit_frFac (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (frFac Z.δ p a) := by
  unfold frFac
  have hδ : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)) :=
    (isUnit_iff_ne_zero.2 (Z.agree p).2.1).map _
  have hu : IsUnit ((D.s.atP p).ιE (uP p : D.host.E)) := (isUnit_iff_ne_zero.2 (unitAt_ne p)).map _
  have h : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) *
      (D.s.atP p).ιE (uP p : D.host.E)) ^ (D.R.rS - a.val)) := (hδ.mul hu).pow _
  simpa using h

private theorem isUnit_sgnP (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (sgnP D p a) := by
  unfold sgnP
  split
  · exact IsUnit.map _ (Prod.isUnit_iff.2 ⟨isUnit_one.neg.pow _, isUnit_one⟩)
  · exact isUnit_one

theorem isUnit_sF (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (sF Z p a) := by
  unfold sF
  exact (isUnit_sgnP p a).mul (isUnit_frFac Z p a)

theorem isUnit_sF' (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (sF' Z p a) := by
  unfold sF'
  refine IsUnit.mul ?_ (isUnit_frFac Z p a)
  unfold sgnP'
  split
  · exact isUnit_sgnP p a
  · exact isUnit_one.neg.pow _

end Loc

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

section Transfer

variable {D : D7}

def GZ (u v : Fin (D.R.rS + 1) → (VS D).V) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  Matrix.of fun a b => brS (VS D) (v b) (u a)

def GDl (u v : Fin (D.R.rS + 1) → (VS D).V) (l : ℕ) : D.host.E :=
  if hl : l ≤ D.R.rS + 1 then ((GZ u v).submatrix (Fin.castLE hl) (Fin.castLE hl)).det else 0

def Gom' (u v : Fin (D.R.rS + 1) → (VS D).V) : (VS D).V :=
  ∑ b, (GZ u v).adjugate b (Fin.last _) • v b

def Gom (u v : Fin (D.R.rS + 1) → (VS D).V) : (VS D).V :=
  ∑ a, star ((GZ u v).adjugate (Fin.last _) a) • u a

variable (Z : LocDat D) (p : PlF D)

private theorem brS_eq_double_sum_repr_gramV (x y : (VS D).V) :
    brS (VS D) x y = ∑ i, ∑ j, (VS D).frame.repr x i * star ((VS D).frame.repr y j) * gramV D i j := by
  conv_lhs => rw [← (VS D).frame.sum_repr x, ← (VS D).frame.sum_repr y]
  simp only [brS, gramV, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem h_bcP (a b : (D.s.atP p).Ep) (x y : (VS D).V) :
    (locH Z p).h (a • baseChange₂ D p x) (b • baseChange₂ D p y) =
      a * (Z.M p).L.cj b * (D.s.atP p).ιE (brS (VS D) x y) := by
  rw [(locH Z p).h_smul_left, h_smul_right (locH Z p), ← mul_assoc]
  congr 1
  rw [brS_eq_double_sum_repr_gramV]
  simp only [locH, locHerm, LocFacts₂, baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, cj_iota (Z.hcj p), map_sum, map_mul]

theorem baseChangeAt_sum {ι : Type} (s : Finset ι) (c : ι → D.host.E) (v : ι → (VS D).V) :
    baseChange₂ D p (∑ i ∈ s, c i • v i) = ∑ i ∈ s, (D.s.atP p).ιE (c i) • baseChange₂ D p (v i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  funext j
  simp [baseChange₂, map_mul]

theorem zhat_loc (u v : Fin (D.R.rS + 1) → (VS D).V) (c c' : Fin (D.R.rS + 1) → (D.s.atP p).Ep) :
    (locH Z p).Zhat (fun a => c a • baseChange₂ D p (u a)) (fun b => c' b • baseChange₂ D p (v b)) =
      Matrix.diagonal (fun a => (Z.M p).L.cj (c a)) * (GZ u v).map (D.s.atP p).ιE *
        Matrix.diagonal c' := by
  ext a b
  simp only [Loc.HermSp.Zhat, Matrix.of_apply, h_bcP Z p, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, GZ]
  ring

theorem dl_loc (u v : Fin (D.R.rS + 1) → (VS D).V) (c c' : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (l : ℕ)
    (hl : l ≤ D.R.rS + 1) :
    (locH Z p).Dl (fun a => c a • baseChange₂ D p (u a)) (fun b => c' b • baseChange₂ D p (v b)) l =
      (∏ i : Fin l, (Z.M p).L.cj (c (Fin.castLE hl i))) * (∏ i : Fin l, c' (Fin.castLE hl i)) *
        (D.s.atP p).ιE (GDl u v l) := by
  rw [Loc.HermSp.Dl, dif_pos hl, zhat_loc, GDl, dif_pos hl]
  have e : (Matrix.diagonal (fun a => (Z.M p).L.cj (c a)) * (GZ u v).map (D.s.atP p).ιE *
      Matrix.diagonal c').submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i => (Z.M p).L.cj (c (Fin.castLE hl i))) *
        ((GZ u v).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE *
        Matrix.diagonal (fun i => c' (Fin.castLE hl i)) := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, RingHom.map_det]
  simp only [RingHom.mapMatrix_apply]
  ring

theorem om'_loc (u v : Fin (D.R.rS + 1) → (VS D).V) (c c' : Fin (D.R.rS + 1) → (D.s.atP p).Ep) :
    (locH Z p).om' (fun a => c a • baseChange₂ D p (u a)) (fun b => c' b • baseChange₂ D p (v b)) =
      ((∏ j, c' j) * ∏ j ∈ Finset.univ.erase (Fin.last _), (Z.M p).L.cj (c j)) • baseChange₂ D p (Gom' u v) := by
  have hadj : ((GZ u v).map (D.s.atP p).ιE).adjugate = (GZ u v).adjugate.map (D.s.atP p).ιE :=
    (RingHom.map_adjugate (D.s.atP p).ιE (GZ u v)).symm
  rw [Loc.HermSp.om', zhat_loc, Gom', baseChangeAt_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, Matrix.adjugate_diagonal,
    Matrix.adjugate_diagonal, hadj]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, smul_smul]
  rw [← Finset.mul_prod_erase Finset.univ c' (Finset.mem_univ b)]
  congr 1
  ring

theorem om_loc (u v : Fin (D.R.rS + 1) → (VS D).V) (c c' : Fin (D.R.rS + 1) → (D.s.atP p).Ep) :
    (locH Z p).om (fun a => c a • baseChange₂ D p (u a)) (fun b => c' b • baseChange₂ D p (v b)) =
      ((Z.M p).L.cj (∏ j ∈ Finset.univ.erase (Fin.last _), c' j) * ∏ j, c j) • baseChange₂ D p (Gom u v) := by
  have hadj : ((GZ u v).map (D.s.atP p).ιE).adjugate = (GZ u v).adjugate.map (D.s.atP p).ιE :=
    (RingHom.map_adjugate (D.s.atP p).ιE (GZ u v)).symm
  rw [Loc.HermSp.om, zhat_loc, Gom, baseChangeAt_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, Matrix.adjugate_diagonal,
    Matrix.adjugate_diagonal, hadj]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, smul_smul, map_mul, map_prod,
    (Z.M p).L.cj_cj, cj_iota (Z.hcj p)]
  rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ a)]
  congr 1
  ring

end Transfer

end Formalism.L2.SG.Pf.ScalarFramePf
