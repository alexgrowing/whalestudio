import Formalism.LocalToGlobal.Columns.TiedGlRec

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.UG Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hCh : d.Ch.Ok)
  (hl : d.lev = colLevS d.Ch) (hlP : d.levP = (rowTyG d.Ch (rPsharp d.Ch)).inv)

set_option maxHeartbeats 1000000 in

theorem recFrExt (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hP' : PtSurjP d) (u : d.what₂.Word)
    (hiX : ∀ (y : Fin (d.R.N d.R.m - 1) → d.host.E) (x : Fin (d.R.N d.R.m)),
      CF.iXc (d.colRec a) y x = if h : (x : ℕ) < d.R.N d.R.m - 1 then y ⟨x, h⟩ else 0) :
    CF.FrExt (D := d.colRec a) (u := u) (Pi.single (lastIdx (d.R.N d.R.m)) (d.piT u : d.host.E))
      (recGLev a S hCh hl hS hH hP u d.R.m le_rfl) (recGLevP a S hCh hlP hS hH hP' u) := by
  intro i v h
  have e1 : (recGLev a S hCh hl hS hH hP u d.R.m le_rfl).fr i v h = glvD (d.R.N d.R.m) v (recUnit S u d.R.m i v h) :=
    congrFun (congrFun (congrFun (recGLev_fr a S hCh hl hS hH hP u d.R.m le_rfl) i) v) h
  have e2 : (recGLevP a S hCh hlP hS hH hP' u).fr i v h = 1 :=
    congrFun (congrFun (congrFun (recGLevP_fr a S hCh hlP hS hH hP' u) i) v) h
  have hD : ∀ x y : Fin (d.R.N d.R.m), (glvD (d.R.N d.R.m) v (recUnit S u d.R.m i v h)).1 x y =
      if x = y then ((glvU (d.R.N d.R.m) v (recUnit S u d.R.m i v h) x : v.adicCompletionIntegers d.X.F) : v.adicCompletion d.X.F)
        else 0 := fun x y => Matrix.diagonal_apply _ x y
  constructor
  · intro (x : Fin (d.R.N d.R.m)) (b : Fin (d.R.N d.R.m - 1)) (b' : Fin (d.R.N d.R.m)) (hb : (b : ℕ) = b')
    rw [e1, e2, hD, Units.val_one, Matrix.mul_one, Matrix.map_apply]
    have hx : CF.iXm (d.colRec a) x b = if x = b' then 1 else 0 := by
      show LinearMap.toMatrix' (CF.iXc (d.colRec a)) x b = _
      rw [LinearMap.toMatrix'_apply, hiX]
      by_cases hxb : x = b'
      · subst hxb
        have hlt : (x : ℕ) < d.R.N d.R.m - 1 := by rw [← hb]; exact b.2
        have hbx : (⟨(x : ℕ), hlt⟩ : Fin (d.R.N d.R.m - 1)) = b := Fin.ext hb.symm
        rw [if_pos rfl, dif_pos hlt, hbx, Pi.single_eq_same]
      · rw [if_neg hxb]
        by_cases h1 : (x : ℕ) < d.R.N d.R.m - 1
        · rw [dif_pos h1, Pi.single_eq_of_ne]
          intro h2
          apply hxb
          apply Fin.ext
          rw [← hb, ← h2]
        · rw [dif_neg h1]
    rw [hx]
    by_cases hxb : x = b'
    · rw [if_pos hxb, if_pos hxb, map_one]
      have hne : x ≠ lastIdx (d.R.N d.R.m) := by
        intro hl
        have h3 : (x : ℕ) = d.R.N d.R.m - 1 := by rw [hl]; rfl
        have h4 := b.2
        rw [hxb, ← hb] at h3
        omega
      unfold glvU
      rw [if_neg hne]
      rfl
    · rw [if_neg hxb, if_neg hxb, map_zero]
  · intro (x : Fin (d.R.N d.R.m)) (l : Fin (d.R.N d.R.m)) (hl : (l : ℕ) + 1 = d.R.N d.R.m)
    have hll : l = lastIdx (d.R.N d.R.m) := Fin.ext (by show (l : ℕ) = d.R.N d.R.m - 1; omega)
    rw [e1, hD, hll, Pi.single_apply]
    by_cases hx : x = lastIdx (d.R.N d.R.m)
    · rw [if_pos hx, if_pos hx]
      unfold glvU recUnit
      rw [if_pos hx, if_pos rfl]
      rfl
    · rw [if_neg hx, if_neg hx, map_zero, map_zero]

end Formalism.L2.Col
