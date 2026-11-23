import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.RCurveAlg

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} {g0 : B.Cusp j wF}

namespace CurveModel

variable (M : CurveModel G la g0)

def JA : Ideal ↥M.A' :=
  Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) => (⟨sfr (xplus X E hM) la G.w i.succ, M.sA i⟩ : ↥M.A'))

theorem map_JA : M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)) = Jid (xplus X E hM) la G.w := by
  rw [JA, Ideal.map_span, ← Set.range_comp]
  rfl

theorem bij_quot : Function.Bijective (Ideal.quotientMap (M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)))
    (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)) Ideal.le_comap_map) := by
  refine ReciprocityTheory.ChartRestriction.G.I2.quotientMap_bijective_of_loc M.h M.JA M.h_one (fun b => ?_) Subtype.val_injective
  obtain ⟨m, a, ha⟩ := M.loc b
  exact ⟨m, a, by rw [map_pow]; exact ha⟩

def quotEquiv : (↥M.A' ⧸ M.JA) ≃ₐ[Kp (xplus X E hM) la G.N] OsK (xplus X E hM) la G.w :=
  AlgEquiv.ofBijective
    ((Ideal.quotientEquivAlgOfEq (Kp (xplus X E hM) la G.N) M.map_JA).toAlgHom.comp
      (Ideal.quotientMapₐ (M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)))
        (IsScalarTower.toAlgHom (Kp (xplus X E hM) la G.N) ↥M.A' ↥(Frac0 (xplus X E hM) la G.w))
        Ideal.le_comap_map))
    ((Ideal.quotientEquivAlgOfEq (Kp (xplus X E hM) la G.N) M.map_JA).bijective.comp M.bij_quot)

theorem toOsK_h : toOsK (xplus X E hM) la G.w (M.h : ↥(Frac0 (xplus X E hM) la G.w)) = 1 := by
  have h1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) - 1) ∈ Jid (xplus X E hM) la G.w := by
    rw [← M.map_JA]
    have := Ideal.mem_map_of_mem (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)) M.h_one
    rwa [map_sub, map_one] at this
  have h2 := (toOsK_eq_zero_iff (xplus X E hM) la G.w _).2 h1
  rw [map_sub, map_one, sub_eq_zero] at h2
  exact h2

theorem fractionToIntegralSection_smul_eq (b : ↥(Frac0 (xplus X E hM) la G.w)) (n : ↥(HK (xplus X E hM) la G.w wF)) :
    toA0K (xplus X E hM) la G.w wF (b • n) = toOsK (xplus X E hM) la G.w b • toA0K (xplus X E hM) la G.w wF n := by
  rw [map_smul]
  exact (algebraMap_smul (OsK (xplus X E hM) la G.w) b _).symm

theorem coe_smul_base_cusp_form (b : ↥(Frac0 (xplus X E hM) la G.w)) :
    ((b • toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ : ↥(HK (xplus X E hM) la G.w wF)) : Lw (xplus X E hM) la G.w) =
      (b : Lw (xplus X E hM) la G.w) * algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0)) := by
  rw [Submodule.coe_smul, coe_toHK0]
  rfl

theorem coe_smul' (b : ↥(Frac0 (xplus X E hM) la G.w)) (n : ↥(HK (xplus X E hM) la G.w wF)) : ((b • n : ↥(HK (xplus X E hM) la G.w wF)) : Lw (xplus X E hM) la G.w) = (b : Lw (xplus X E hM) la G.w) * (n : Lw (xplus X E hM) la G.w) := by
  rw [Submodule.coe_smul]
  rfl

set_option maxHeartbeats 1000000 in

theorem JH_mem (z : ↥(HK (xplus X E hM) la G.w wF)) (hz : z ∈ Jid (xplus X E hM) la G.w • (⊤ : Submodule ↥(Frac0 (xplus X E hM) la G.w) ↥(HK (xplus X E hM) la G.w wF))) :
    ∃ m : ℕ, ∃ a' ∈ M.JA, ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • z) = ((a' : ↥(Frac0 (xplus X E hM) la G.w)) •
      toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩) := by
  set e0 : ↥(HK (xplus X E hM) la G.w wF) := toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ with he0
  have key : ∀ r ∈ Jid (xplus X E hM) la G.w, ∀ n : ↥(HK (xplus X E hM) la G.w wF), ∃ m : ℕ, ∃ a' ∈ M.JA,
      ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • (r • n)) = ((a' : ↥(Frac0 (xplus X E hM) la G.w)) • e0) := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro n
      obtain ⟨m, a, ha⟩ := M.base_form_local n
      refine ⟨m, ⟨sfr (xplus X E hM) la G.w i.succ, M.sA i⟩ * a, Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩), ?_⟩
      apply Subtype.ext
      rw [coe_smul', coe_smul', he0, coe_smul_base_cusp_form]
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [mul_left_comm, ha]
      ring
    | zero => intro n; exact ⟨0, 0, Ideal.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      intro n
      obtain ⟨m, a, ha, he⟩ := hx n
      obtain ⟨m', a', ha', he'⟩ := hy n
      refine ⟨m + m', M.h ^ m' * a + M.h ^ m * a', Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha)
        (Ideal.mul_mem_left _ _ ha'), ?_⟩
      have e1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • (x • n) = ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
        rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_comm, mul_smul, he, ← mul_smul]
      have e2 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • (y • n) = ((M.h ^ m * a' : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
        rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_smul, he', ← mul_smul]
      rw [add_smul, smul_add, pow_add, e1, e2, ← add_smul, ← AddMemClass.coe_add]
    | smul c x _ hx =>
      intro n
      obtain ⟨m, a, ha, he⟩ := hx ((c • n : ↥(HK (xplus X E hM) la G.w wF)))
      refine ⟨m, a, ha, ?_⟩
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact he
  refine Submodule.smul_induction_on hz (fun r hr n _ => key r hr n) ?_
  rintro x y ⟨m, a, ha, he⟩ ⟨m', a', ha', he'⟩
  refine ⟨m + m', M.h ^ m' * a + M.h ^ m * a', Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha)
    (Ideal.mul_mem_left _ _ ha'), ?_⟩
  have e1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • x = ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_comm, mul_smul, he, ← mul_smul]
  have e2 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • y = ((M.h ^ m * a' : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_smul, he', ← mul_smul]
  rw [smul_add, pow_add, e1, e2, ← add_smul, ← AddMemClass.coe_add]

theorem isGen (M : CurveModel G la g0) : IsGen (OsK (xplus X E hM) la G.w) (resF G la g0) := by
  set e0 : ↥(HK (xplus X E hM) la G.w wF) := toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ with he0
  have hres : resF G la g0 = toA0K (xplus X E hM) la G.w wF e0 := rfl
  unfold IsGen
  rw [hres]
  constructor
  · intro u v huv
    rw [← sub_eq_zero]
    have hw : (u - v) • toA0K (xplus X E hM) la G.w wF e0 = 0 := by rw [sub_smul]; exact sub_eq_zero.2 huv
    obtain ⟨b, hb⟩ := toOsK_surjective (xplus X E hM) la G.w (u - v)
    obtain ⟨m, a, ha⟩ := M.loc b
    have hta : toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)) = u - v := by
      rw [← ha, map_mul, map_pow, M.toOsK_h, one_pow, one_mul, hb]
    rw [← hta, ← fractionToIntegralSection_smul_eq] at hw
    obtain ⟨m', a', ha', he'⟩ := M.JH_mem _ ((reduction_eq_zero_iff_mem_ideal_smul (xplus X E hM) la G.w wF _).1 hw)
    have hinj : M.h ^ m' * a = a' := by
      apply M.base_form_injective
      have := congrArg (fun n : ↥(HK (xplus X E hM) la G.w wF) => (n : Lw (xplus X E hM) la G.w)) he'
      rw [he0] at this
      simp only [coe_smul', coe_toHK0, SubmonoidClass.coe_pow] at this
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [mul_assoc]
      exact this
    have hJ : ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) ∈ Jid (xplus X E hM) la G.w := by
      rw [hinj, ← M.map_JA]; exact Ideal.mem_map_of_mem _ ha'
    have h0 := (toOsK_eq_zero_iff (xplus X E hM) la G.w _).2 hJ
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, M.toOsK_h, one_pow, one_mul] at h0
    rw [← hta]
    exact h0
  · intro n
    obtain ⟨x, rfl⟩ := reductionMap_surjective (xplus X E hM) la G.w wF n
    obtain ⟨m, a, ha⟩ := M.base_form_local x
    refine ⟨toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)), ?_⟩
    have hx : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • x) = ((a : ↥(Frac0 (xplus X E hM) la G.w)) • e0) := by
      apply Subtype.ext
      rw [coe_smul', he0, coe_smul_base_cusp_form]
      simpa only [Subalgebra.coe_pow, SubmonoidClass.coe_pow] using ha
    show toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)) • toA0K (xplus X E hM) la G.w wF e0 = toA0K (xplus X E hM) la G.w wF x
    rw [← fractionToIntegralSection_smul_eq, ← hx, fractionToIntegralSection_smul_eq, map_pow, M.toOsK_h, one_pow, one_smul]

end CurveModel

theorem inCurveSec (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : InCurveSecSt (E := E) G la := by
  intro y hs g0 hMod _
  obtain ⟨M⟩ := hMod
  refine ⟨?_, ?_, M.isGen⟩
  · haveI : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥M.A' ⧸ M.JA) := M.fin
    exact LinearEquiv.finiteDimensional M.quotEquiv.toLinearEquiv
  · haveI : IsReduced (↥M.A' ⧸ M.JA) := M.red
    exact isReduced_of_injective M.quotEquiv.symm.toRingHom M.quotEquiv.symm.injective

end Formalism.L2.Pj
