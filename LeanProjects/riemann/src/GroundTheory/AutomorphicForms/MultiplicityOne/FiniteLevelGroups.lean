import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Smoothing

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem finEmb_mul_centralSection_inv_mem (u : AdelicGLn.FiniteAdelicGL K n) :
    finEmb K n u * (centralSection K n (detModule K n (finEmb K n u)))⁻¹ ∈ normOneGL K n := by
  rw [mem_normOneGL_iff_detModule, map_mul, map_inv]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.AdelicGL K 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    rw [Subsingleton.elim (finEmb K 0 u) 1, Subsingleton.elim (centralSection K 0 _) 1]
    simp
  · rw [detModule_centralSection hn, mul_inv_cancel]

variable (K n) in

def finProjFun (u : AdelicGLn.FiniteAdelicGL K n) : AdelicGLn.AdelicGL K n :=
  finEmb K n u * (centralSection K n (detModule K n (finEmb K n u)))⁻¹

theorem finProjFun_mul (u v : AdelicGLn.FiniteAdelicGL K n) :
    finProjFun K n (u * v) = finProjFun K n u * finProjFun K n v := by
  unfold finProjFun
  simp only [map_mul, mul_inv_rev]
  simp only [mul_assoc]
  rw [← mul_assoc (centralSection K n (detModule K n (finEmb K n u)))⁻¹ (finEmb K n v),
    centralSection_inv_mul_comm (detModule K n (finEmb K n u)) (finEmb K n v),
    mul_assoc (finEmb K n v), centralSection_inv_mul_inv_comm (detModule K n (finEmb K n u))]

variable (K n) in

def finProj : AdelicGLn.FiniteAdelicGL K n →* normOneGL K n where
  toFun u := ⟨finProjFun K n u, finEmb_mul_centralSection_inv_mem u⟩
  map_one' := Subtype.ext (by simp [finProjFun])
  map_mul' u v := Subtype.ext (finProjFun_mul u v)

@[simp] theorem coe_finProj (u : AdelicGLn.FiniteAdelicGL K n) :
    (finProj K n u : AdelicGLn.AdelicGL K n) =
      finEmb K n u * (centralSection K n (detModule K n (finEmb K n u)))⁻¹ := rfl

theorem continuous_finProj : Continuous (finProj K n) := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun u : AdelicGLn.FiniteAdelicGL K n =>
    finEmb K n u * (centralSection K n (detModule K n (finEmb K n u)))⁻¹
  exact continuous_finEmb.mul ((continuous_centralSection.comp
    (continuous_detModule.comp continuous_finEmb)).inv)

theorem finProj_of_mem {u : AdelicGLn.FiniteAdelicGL K n} (hu : finEmb K n u ∈ normOneGL K n) :
    finProj K n u = ⟨finEmb K n u, hu⟩ := by
  ext1
  rw [coe_finProj, (mem_normOneGL_iff_detModule).1 hu, map_one, inv_one, mul_one]

theorem finProj_eq_finOne (u : AdelicGLn.integralFiniteGL K n) :
    finProj K n u = finOne K n u :=
  finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact u.2))

theorem finProj_mul_archProj_comm (u : AdelicGLn.FiniteAdelicGL K n) (A : ArchUnits K n) :
    finProj K n u * archProj K n A = archProj K n A * finProj K n u := by
  refine Subtype.ext ?_
  change (finProj K n u : AdelicGLn.AdelicGL K n) * archProj K n A =
    (archProj K n A : AdelicGLn.AdelicGL K n) * finProj K n u
  rw [coe_finProj, mul_assoc, centralSection_inv_mul_comm, ← mul_assoc,
    ← archProj_mul_finEmb_comm, mul_assoc]

theorem exists_archProj_mul_finProj (x : normOneGL K n) :
    ∃ (A : ArchUnits K n) (u : AdelicGLn.FiniteAdelicGL K n), archProj K n A * finProj K n u = x := by
  set g : AdelicGLn.AdelicGL K n := (x : AdelicGLn.AdelicGL K n)
  set A : ArchUnits K n := ((archEquiv K n (AdelicGLn.prodEquiv K n g).1 : archGroup K n) : ArchUnits K n)
  set u := (AdelicGLn.prodEquiv K n g).2
  refine ⟨A, u, Subtype.ext ?_⟩
  have hg : archIncl K n A * finEmb K n u = g := infEmb_mul_finEmb g
  have hx : detModule K n g = 1 := (mem_normOneGL_iff_detModule).1 x.2
  change (archProj K n A : AdelicGLn.AdelicGL K n) * finProj K n u = g
  rw [coe_archProj, coe_finProj]
  set a := detModule K n (archIncl K n A)
  set b := detModule K n (finEmb K n u)
  have hab : b * a = 1 := by
    rw [mul_comm, ← map_mul, hg, hx]
  calc archIncl K n A * (centralSection K n a)⁻¹ * (finEmb K n u * (centralSection K n b)⁻¹)
      = archIncl K n A * ((centralSection K n a)⁻¹ * finEmb K n u) * (centralSection K n b)⁻¹ := by
        simp only [mul_assoc]
    _ = archIncl K n A * (finEmb K n u * (centralSection K n a)⁻¹) * (centralSection K n b)⁻¹ := by
        rw [centralSection_inv_mul_comm]
    _ = (archIncl K n A * finEmb K n u) * ((centralSection K n b) * (centralSection K n a))⁻¹ := by
        rw [mul_inv_rev]
        simp only [mul_assoc]
    _ = g := by rw [hg, ← map_mul, hab, map_one, inv_one, mul_one]

end MultiplicityOne

end

end GroundTheory.Automorphic
