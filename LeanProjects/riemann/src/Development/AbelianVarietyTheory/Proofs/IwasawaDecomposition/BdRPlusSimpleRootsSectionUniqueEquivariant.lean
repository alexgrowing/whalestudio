import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariantStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section
namespace GlobalTheory.MemLoc.SecUniq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem root_eq {K R C : Type} [Field K] [CommRing R] [Field C] (θ : R →+* C)
    (hu : ∀ y : R, θ y ≠ 0 → IsUnit y) (o : K →+* R) (x : K) (y : R) (f : Polynomial K)
    (hy : θ y = θ (o x)) (h0 : f.eval x = 0) (h1 : f.derivative.eval x ≠ 0)
    (h2 : (f.map o).eval y = 0) : y = o x := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map o) (o x) (y - o x)
  rw [add_sub_cancel, h2, Polynomial.derivative_map, Polynomial.eval_map_apply,
    Polynomial.eval_map_apply, h0, map_zero, zero_add] at hk
  have hθ : θ (y - o x) = 0 := by rw [map_sub, hy, sub_self]
  have hun : IsUnit (o (f.derivative.eval x) + k * (y - o x)) := by
    apply hu
    rw [map_add, map_mul, hθ, mul_zero, add_zero]
    exact (map_ne_zero (θ.comp o)).2 h1
  have : (o (f.derivative.eval x) + k * (y - o x)) * (y - o x) = 0 := by
    rw [hk]; ring
  exact sub_eq_zero.1 ((hun.mul_right_eq_zero).1 this)

variable {l : ℕ} [Fact l.Prime]

theorem padicInt_hom_ext_pt {R : Type} [CommRing R] [IsHausdorff (Ideal.span {((l : ℕ) : R)}) R]
    (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  refine sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {((l : ℕ) : R)}) inferInstance _ fun n => ?_)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n z)
  have hz : z = (PadicInt.appr z n : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by rw [← hw]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨f w - g w, ?_⟩
  have h1 := congrArg f hz
  have h2 := congrArg g hz
  rw [map_add, map_mul, map_pow, map_natCast, map_natCast] at h1 h2
  rw [h1, h2]
  ring

theorem sigA_zA (g : Per.Gq l) (z : ℤ_[l]) : Per.σA g (Per.zA l z) = Per.zA l z := by
  haveI : IsAdicComplete (Ideal.span {((l : ℕ) : Per.Ainf l)}) (Per.Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  exact padicInt_hom_ext_pt ((Per.σA g).comp (Per.zA l)) (Per.zA l) z

theorem sigDp_aDp (g : Per.Gq l) (a : Per.Ainf l) : Per.σDp g (aDp l a) = aDp l (Per.σA g a) := by
  simp only [aDp, RingHom.comp_apply]
  rw [GlobalTheory.RingIface.sigDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]

theorem sec_root (o : Om l →+* Per.BdRp l) (ho : IsSec o) (x : Om l) (y : Per.BdRp l)
    (f : Polynomial (Om l)) (hy : Per.θD l y = (x : ℂ_[l])) (h0 : f.eval x = 0)
    (h1 : f.derivative.eval x ≠ 0) (h2 : (f.map o).eval y = 0) : y = o x :=
  root_eq (Per.θD l) (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.1 o x y f (by rw [hy, ho.th]) h0 h1 h2

theorem sec_uniq (o : Om l →+* Per.BdRp l) (ho : IsSec o) (o' : Om l →+* Per.BdRp l) (ho' : IsSec o') :
    o' = o := by
  have hq : o'.comp (algebraMap ℚ_[l] (Om l)) = o.comp (algebraMap ℚ_[l] (Om l)) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun z => ?_)
    exact (ho'.z z).trans (ho.z z).symm
  refine RingHom.ext fun x => ?_
  have hs : IsSeparable ℚ_[l] x := Algebra.IsSeparable.isSeparable ℚ_[l] x
  refine sec_root o ho x (o' x) ((minpoly ℚ_[l] x).map (algebraMap ℚ_[l] (Om l))) (ho'.th x) ?_ ?_ ?_
  · rw [Polynomial.eval_map_algebraMap, minpoly.aeval]
  · rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact Polynomial.Separable.aeval_derivative_ne_zero hs (minpoly.aeval _ _)
  · rw [Polynomial.map_map, ← hq, ← Polynomial.map_map, Polynomial.eval_map_apply,
      Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]

theorem sec_equiv (o : Om l →+* Per.BdRp l) (ho : IsSec o) (g : Per.Gq l) (x : Om l) :
    Per.σDp g (o x) = o (g x) := by
  have h : IsSec (((Per.σDp g).comp o).comp (g.symm : Om l →+* Om l)) := by
    constructor
    · intro x
      change Per.θD l (Per.σDp g (o (g.symm x))) = _
      rw [(GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.2, ho.th, GlobalTheory.RingBasics.σC_coe, AlgEquiv.apply_symm_apply]
    · intro z
      change Per.σDp g (o (g.symm (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])))) = _
      rw [AlgEquiv.commutes, ho.z, sigDp_aDp, sigA_zA]
  have := RingHom.congr_fun (sec_uniq o ho _ h) (g x)
  rw [← this]
  change _ = Per.σDp g (o (g.symm (g x)))
  rw [AlgEquiv.symm_apply_apply]

theorem main : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → (∀ (x : Om l) (y : Per.BdRp l) (f : Polynomial (Om l)), Per.θD l y = (x : ℂ_[l]) → f.eval x = 0 → f.derivative.eval x ≠ 0 → (f.map o).eval y = 0 → y = o x) ∧ (∀ o' : Om l →+* Per.BdRp l, IsSec o' → o' = o) ∧ ∀ (g : Per.Gq l) (x : Om l), Per.σDp g (o x) = o (g x) :=
  fun _ _ o ho => ⟨sec_root o ho, sec_uniq o ho, sec_equiv o ho⟩

end GlobalTheory.MemLoc.SecUniq
