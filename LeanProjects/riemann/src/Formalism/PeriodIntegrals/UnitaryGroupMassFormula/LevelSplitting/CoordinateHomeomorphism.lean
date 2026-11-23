import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCIface
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2

noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Q : Type} [AddCommGroup Q] [TopologicalSpace Q] [ContinuousAdd Q]

structure CoordHyp (N A N1 Z : Subgroup G) (Lev : G → G) (sH : Q → G) (yQ : N1 → Q) : Prop where
  hAN : A ≤ N
  coordinate_level_le : N1 ≤ N
  hZN1 : Z ≤ N1
  cLev : Continuous Lev
  csH : Continuous sH
  cyQ : Continuous yQ
  lev_mem : ∀ n ∈ N, Lev n ∈ A
  lev_rest : ∀ n ∈ N, (Lev n)⁻¹ * n ∈ N1
  triv : ∀ u ∈ A, u ∈ N1 → u = 1
  norm1 : ∀ n ∈ N, ∀ m ∈ N1, n * m * n⁻¹ ∈ N1
  sH_mem : ∀ y, sH y ∈ N1
  dec : ∀ m : N1, (sH (yQ m))⁻¹ * (m : G) ∈ Z
  yQ_sH : ∀ y z (hz : z ∈ Z), yQ ⟨sH y * z, N1.mul_mem (sH_mem y) (hZN1 hz)⟩ = y
  cent : ∀ z ∈ Z, ∀ m ∈ N1, z * m = m * z
  mul : ∀ y y', sH y * sH y' * (sH (y + y'))⁻¹ ∈ Z

variable {N A N1 Z : Subgroup G} {Lev : G → G} {sH : Q → G} {yQ : N1 → Q}

theorem lev_eq (H : CoordHyp N A N1 Z Lev sH yQ) (u : A) (w : G) (hw : w ∈ N1) :
    Lev ((u : G) * w) = u := by
  have hg : (u : G) * w ∈ N := N.mul_mem (H.hAN u.2) (H.coordinate_level_le hw)
  set v := Lev ((u : G) * w) with hv
  have h1 : v⁻¹ * (u : G) ∈ N1 := by
    have : v⁻¹ * (u : G) = (v⁻¹ * ((u : G) * w)) * w⁻¹ := by group
    rw [this]
    exact N1.mul_mem (H.lev_rest _ hg) (N1.inv_mem hw)
  have h2 : v⁻¹ * (u : G) ∈ A := A.mul_mem (A.inv_mem (H.lev_mem _ hg)) u.2
  have h3 := H.triv _ h2 h1
  have : (u : G) = v := by
    calc (u : G) = v * (v⁻¹ * u) := by group
      _ = v := by rw [h3, mul_one]
  exact this.symm

def cfun (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) : N :=
  ⟨(p.1 : G) * sH p.2.1 * (p.2.2 : G),
    N.mul_mem (N.mul_mem (H.hAN p.1.2) (H.coordinate_level_le (H.sH_mem _))) (H.coordinate_level_le (H.hZN1 p.2.2.2))⟩

def cm (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : N1 :=
  ⟨(Lev n)⁻¹ * (n : G), H.lev_rest n n.2⟩

def cinv (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : A × (Q × Z) :=
  (⟨Lev n, H.lev_mem n n.2⟩, yQ (cm H n), ⟨(sH (yQ (cm H n)))⁻¹ * (cm H n : G), H.dec _⟩)

theorem cinv_cfun (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) :
    cinv H (cfun H p) = p := by
  obtain ⟨u, y, z⟩ := p
  have hw : sH y * (z : G) ∈ N1 := N1.mul_mem (H.sH_mem y) (H.hZN1 z.2)
  have hL : Lev ((u : G) * sH y * (z : G)) = u := by
    rw [mul_assoc]; exact lev_eq H u _ hw
  have hm : cm H (cfun H (u, y, z)) = ⟨sH y * (z : G), hw⟩ := by
    apply Subtype.ext
    simp only [cm, cfun]
    rw [hL]; group
  have hy : yQ (cm H (cfun H (u, y, z))) = y := by
    rw [hm]; exact H.yQ_sH y z z.2
  refine Prod.ext (Subtype.ext ?_) (Prod.ext hy (Subtype.ext ?_))
  · simp only [cinv, cfun]; exact hL
  · simp only [cinv]
    rw [hy, hm]
    group

theorem cfun_cinv (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : cfun H (cinv H n) = n := by
  apply Subtype.ext
  simp only [cfun, cinv, cm]
  group

theorem continuous_cm (H : CoordHyp N A N1 Z Lev sH yQ) : Continuous (cm H) :=
  Continuous.subtype_mk ((H.cLev.comp continuous_subtype_val).inv.mul continuous_subtype_val) _

def cHomeo (H : CoordHyp N A N1 Z Lev sH yQ) : (A × (Q × Z)) ≃ₜ N where
  toFun := cfun H
  invFun := cinv H
  left_inv := cinv_cfun H
  right_inv := cfun_cinv H
  continuous_toFun := Continuous.subtype_mk
    (((continuous_subtype_val.comp continuous_fst).mul
      (H.csH.comp (continuous_fst.comp continuous_snd))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))) _
  continuous_invFun := by
    have h1 := continuous_cm H
    refine Continuous.prodMk (Continuous.subtype_mk (H.cLev.comp continuous_subtype_val) _)
      (Continuous.prodMk (H.cyQ.comp h1) (Continuous.subtype_mk ?_ _))
    exact (H.csH.comp (H.cyQ.comp h1)).inv.mul (continuous_subtype_val.comp h1)

theorem cHomeo_apply (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) :
    ((cHomeo H p : N) : G) = (p.1 : G) * sH p.2.1 * (p.2.2 : G) := rfl

theorem coord_skew (H : CoordHyp N A N1 Z Lev sH yQ) (n0 : N) :
    ∃ (a0 : A) (t : A → Q) (c : A × Q → Z), Continuous t ∧ Continuous c ∧
      ∀ u y z, n0 * cHomeo H (u, y, z) = cHomeo H (a0 * u, y + t u, c (u, y) * z) := by
  set a0 : A := ⟨Lev n0, H.lev_mem n0 n0.2⟩
  set n1 : G := (Lev n0)⁻¹ * (n0 : G) with hn1
  have hn1m : n1 ∈ N1 := H.lev_rest n0 n0.2
  have hmf : ∀ u : A, (u : G)⁻¹ * n1 * u ∈ N1 := fun u => by
    have := H.norm1 ((u : G)⁻¹) (N.inv_mem (H.hAN u.2)) n1 hn1m
    simpa using this
  let mf : A → N1 := fun u => ⟨(u : G)⁻¹ * n1 * u, hmf u⟩
  have cmf : Continuous mf := Continuous.subtype_mk
    ((continuous_subtype_val.inv.mul continuous_const).mul continuous_subtype_val) _
  let t : A → Q := fun u => yQ (mf u)
  have ct : Continuous t := H.cyQ.comp cmf
  let zm : A → G := fun u => (sH (t u))⁻¹ * (mf u : G)
  have hzm : ∀ u, zm u ∈ Z := fun u => H.dec (mf u)
  let k : A × Q → G := fun p => sH (t p.1) * sH p.2 * (sH (t p.1 + p.2))⁻¹
  have hk : ∀ p, k p ∈ Z := fun p => H.mul _ _
  let c : A × Q → Z := fun p => ⟨k p * zm p.1, Z.mul_mem (hk p) (hzm p.1)⟩
  have cc : Continuous c := by
    refine Continuous.subtype_mk ?_ _
    have ct1 : Continuous (fun p : A × Q => t p.1) := ct.comp continuous_fst
    refine (((H.csH.comp ct1).mul (H.csH.comp continuous_snd)).mul
      (H.csH.comp (ct1.add continuous_snd)).inv).mul ?_
    exact (H.csH.comp ct1).inv.mul (continuous_subtype_val.comp (cmf.comp continuous_fst))
  refine ⟨a0, t, c, ct, cc, fun u y z => ?_⟩
  apply Subtype.ext
  show (n0 : G) * ((u : G) * sH y * (z : G)) = (Lev n0 * u) * sH (y + t u) * (k (u, y) * zm u * z)
  have e2 : (mf u : G) = sH (t u) * zm u := by
    show (mf u : G) = sH (t u) * ((sH (t u))⁻¹ * (mf u : G)); group
  have e3 : zm u * sH y = sH y * zm u := H.cent _ (hzm u) _ (H.sH_mem y)
  have e4 : sH (t u) * sH y = sH (t u + y) * k (u, y) := by
    have h := H.cent _ (hk (u, y)) _ (H.sH_mem (t u + y))
    calc sH (t u) * sH y = k (u, y) * sH (t u + y) := by show _ = sH (t u) * sH y * (sH (t u + y))⁻¹ * sH (t u + y); group
      _ = sH (t u + y) * k (u, y) := h
  have e1 : (n0 : G) * ((u : G) * sH y * (z : G)) = Lev n0 * u * (mf u : G) * sH y * z := by
    show _ = Lev n0 * u * ((u : G)⁻¹ * ((Lev n0)⁻¹ * (n0 : G)) * u) * sH y * z
    group
  rw [e1, e2, add_comm y (t u)]
  calc Lev n0 * (u : G) * (sH (t u) * zm u) * sH y * (z : G)
      = Lev n0 * u * sH (t u) * (zm u * sH y) * z := by group
    _ = Lev n0 * u * sH (t u) * (sH y * zm u) * z := by rw [e3]
    _ = Lev n0 * u * (sH (t u) * sH y) * zm u * z := by group
    _ = Lev n0 * u * (sH (t u + y) * k (u, y)) * zm u * z := by rw [e4]
    _ = (Lev n0 * u) * sH (t u + y) * (k (u, y) * zm u * z) := by group

end Gen

end PI.LevelKSplit.W.NC
