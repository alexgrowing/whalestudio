import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf
import Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.T0

namespace GlobalTheory.SecPoint

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem range_mul_step {m : ℕ} {x y : X.Forms} (hx : x ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m)))
    (hy : y ∈ LinearMap.range (X.inc wL)) : x * y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + 1))) := by
  obtain ⟨F, rfl⟩ := hx
  obtain ⟨G, rfl⟩ := hy
  obtain ⟨H, hH⟩ := X.inc_mul wL _ G F
  rw [← wadd_addL, mul_comm, hH]
  exact ⟨H, rfl⟩

theorem range_pow {m : ℕ} {y x : X.Forms} (hy : y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m)))
    (hx : x ∈ LinearMap.range (X.inc wL)) (e : ℕ) :
    y * x ^ e ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + e))) := by
  induction e with
  | zero => simpa using hy
  | succ e ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact range_mul_step X ih hx

theorem range_prod (d : Fin N →₀ ℕ) {m : ℕ} {y : X.Forms}
    (hy : y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m))) (s : Finset (Fin N)) :
    y * ∏ i ∈ s, X.inc wL (w i) ^ d i ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + ∑ i ∈ s, d i))) := by
  classical
  refine Finset.induction_on s (by rwa [Finset.prod_empty, Finset.sum_empty, mul_one, add_zero]) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  have e1 : y * (X.inc wL (w a) ^ d a * ∏ i ∈ s, X.inc wL (w i) ^ d i) =
      (y * ∏ i ∈ s, X.inc wL (w i) ^ d i) * X.inc wL (w a) ^ d a := by ring
  have e2 : m + (d a + ∑ i ∈ s, d i) = m + ∑ i ∈ s, d i + d a := by ring
  rw [e1, e2]
  exact range_pow X ih ⟨w a, rfl⟩ (d a)

theorem range_aeval {k : ℕ} (Pw : MvPolynomial (Fin N) B.KO) (hPw : Pw.IsHomogeneous k) {m : ℕ} {y : X.Forms}
    (hy : y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m))) :
    y * MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + k))) := by
  classical
  rw [Pw.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, mul_left_comm, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : ∑ i ∈ d.support, d i = k := by
    have := hPw (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h := range_prod X N w d hy d.support
  rw [hdeg] at h
  exact h

theorem exists_ratio {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (hB : CurveLoc.BirAt X N w gF) (hk : ∃ k, gF (X.inc wL (w k)) ≠ 0) (a : Ω) :
    ∃ (m : ℕ) (p q : B.Cusp j (addL (wt0 D j) wL m)), gF (X.inc _ p) ≠ 0 ∧ a * gF (X.inc _ p) = gF (X.inc _ q) := by
  obtain ⟨k0, hk0⟩ := hk
  obtain ⟨k, g, Pw, hPw, hne, he⟩ := hB a
  have h1 : X.inc wL (w k0) ∈ LinearMap.range (X.inc (addL (wt0 D j) wL 1)) := by
    rw [add_zero_weight_one_eq]; exact ⟨_, rfl⟩
  obtain ⟨p, hp⟩ := range_aeval X N w Pw hPw h1
  have hG : X.inc wL (w k0) * X.inc (wsmul k wL) g ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (1 + k))) := by
    obtain ⟨H, hH⟩ := X.inc_mul wL _ (w k0) g
    rw [add_comm, ← wadd_addL, addL, zero_weight_add, hH]
    exact ⟨H, rfl⟩
  obtain ⟨q, hq⟩ := hG
  have hPv : gF (MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw) =
      MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw :=
    MvPolynomial.comp_aeval_apply (fun i => X.inc wL (w i)) gF Pw
  refine ⟨1 + k, p, q, ?_, ?_⟩
  · rw [hp, map_mul, hPv]
    exact mul_ne_zero hk0 hne
  · rw [hp, hq, map_mul, map_mul, hPv, ← he]
    ring

def evK {F : Type} [Field F] (ev : Rp X la N →+* F) : Kp X la N →+* F :=
  ev.comp (algebraMap (Kp X la N) (Rp X la N))

theorem ev_smul {F : Type} [Field F] (ev : Rp X la N →+* F) (c : Kp X la N) (g : Rp X la N) :
    ev (c • g) = evK X la N ev c * ev g := by
  rw [Algebra.smul_def, map_mul]; rfl

theorem lift_algKp {F : Type} [Field F] (ev : Rp X la N →+* F) (hu : IsUnit (ev (sec X la w 0))) (c : Kp X la N) :
    IsLocalization.Away.lift (sec X la w 0) hu
      ((algebraMap (Kp X la N) ↥(Frac0 X la w) c : ↥(Frac0 X la w)) : Lw X la w) = evK X la N ev c := by
  show IsLocalization.Away.lift (sec X la w 0) hu (algebraMap (Kp X la N) (Lw X la w) c) = _
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), liftEv_alg]
  rfl

section Fam

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem exists_point [Finite ι]
    (hinj : ∀ (u : WeightFamilies.Wt D j) (G : B.Cusp j u), (∀ Z, gF Z (X.inc u G) = 0) → G = 0)
    (hsplit : ∀ (Z : ι) (k : Fin N), ∃ g : B.Cusp j wL, gF Z (X.inc wL g) = gF Z (X.inc wL (w k)) ∧
      ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0)
    (hB : ∀ Z, CurveLoc.BirAt X N w (gF Z)) (hC : ∀ Z, CurveLoc.CountQAt X la N w (gF Z))
    {F : Type} [Field F] (ev : Rp X la N →+* F) (hu : IsUnit (ev (sec X la w 0)))
    (honS : ∀ i : Fin (WeightFamilies.dimY D j), ev (sec X la w i.succ) = 0) :
    ∃ (Z : ι) (τ : Ω Z →+* F) (σ : F), σ ≠ 0 ∧
      (∀ (u : WeightFamilies.Wt D j) (G : B.Cusp j u), gF Z (X.inc u G) = 0 → ev (emb X la N (X.inc u G)) = 0) ∧
      (∀ a : B.KO, τ (algebraMap B.KO (Ω Z) a) =
        evK X la N ev (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) ∧
      ∀ (k : ℕ) (G : X.Forms), emb X la N G ∈ Vw X la N (addL (wt0 D j) wL k) →
        ev (emb X la N G) = τ (gF Z G) * σ ^ k := by
  classical
  have := Fintype.ofFinite ι
  letI : Algebra (Kp X la N) F := (evK X la N ev).toAlgebra
  let ψ : ↥(Frac0 X la w) →ₐ[Kp X la N] F :=
    { (IsLocalization.Away.lift (sec X la w 0) hu).comp (Frac0 X la w).val.toRingHom with
      commutes' := fun c => lift_algKp X la N w ev hu c }
  have hψ : ∀ (x : ↥(Frac0 X la w)) (k : ℕ) (g : Rp X la N), (x : Lw X la w) = frac X la w k g →
      ψ x = ev g * (ev (sec X la w 0))⁻¹ ^ k := fun x k g hx => by
    show IsLocalization.Away.lift (sec X la w 0) hu (x : Lw X la w) = _
    rw [hx, liftEv_frac]
  have hQ : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime _
  have hJ : Jid X la w ≤ RingHom.ker ψ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hψ _ 1 _ (coe_sfr X la w i.succ), honS, zero_mul]
  have hinf : (Finset.univ : Finset ι).inf (fun Z => RingHom.ker (phiZ X la N (Ω Z) (gF Z) w)) ≤ RingHom.ker ψ := by
    intro f hf
    have hf' : ∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0 := fun Z =>
      RingHom.mem_ker.1 (Finset.inf_le (f := fun Z => RingHom.ker (phiZ X la N (Ω Z) (gF Z) w))
        (Finset.mem_univ Z) hf)
    rw [CurveInj.fraction_zero_injective X la N Ω gF w hinj f hf']
    exact Ideal.zero_mem _
  obtain ⟨Z, -, hZ⟩ := (Ideal.IsPrime.inf_le' hQ).1 hinf
  obtain ⟨χ, hχ⟩ := pos_factor (phiZ X la N (Ω Z) (gF Z) w) ψ
    (fun f hf => RingHom.mem_ker.1 (hZ (RingHom.mem_ker.2 hf))) (fun r => by
      obtain ⟨a, p, hp, hr⟩ := CurveLoc.loc_of_bir X la N w (gF Z) (hB Z) (hC Z) r
      exact ⟨a, p, fun h0 => hp _ hQ hJ hZ (RingHom.mem_ker.2 h0), hr⟩)
  have hs := pos_sec_ne X la N w (gF Z) χ
  have hs0 := hu.ne_zero
  refine ⟨Z, χ.toRingHom.comp (CurveLoc.psiZ X la N w (gF Z)), ev (sec X la w 0) *
    (χ (algebraMap (RZ X la N (Ω Z)) (RZs X la N (Ω Z) (gF Z) w) (rzMap X la N (Ω Z) (gF Z) (sec X la w 0))))⁻¹,
    mul_ne_zero hs0 (inv_ne_zero hs), fun u G h0 => ?_,
    fun a => (congrArg χ (pos_psiZ_alg X la N w (gF Z) a)).trans (χ.commutes _), fun k G hG => ?_⟩
  · choose g hg using hsplit Z
    have hmem : frac X la w 1 (CurveLoc.secOf X la N g) ∈ Frac0 X la w :=
      Algebra.subset_adjoin (frac_mem_Hfr X la w (by rw [add_zero_weight_one_eq]; exact CurveLoc.secOf_mem X la N g))
    have h1 : (⟨_, hmem⟩ : ↥(Frac0 X la w)) - 1 ∈ RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) := by
      rw [RingHom.mem_ker, map_sub, map_one, CurveLoc.phiZ_of_eq X la N w (gF Z) _ 1 _ rfl,
        CurveLoc.rzMap_secOf X la N (gF Z) g w (fun k => (hg k).1), CurveLoc.secOf_self, pow_one,
        CurveLoc.weight_zero_section_mul_inv, sub_self]
    have h2 := hZ h1
    rw [RingHom.mem_ker, map_sub, map_one, hψ _ 1 _ rfl, pow_one, sub_eq_zero] at h2
    have he : ev (CurveLoc.secOf X la N g) ≠ 0 := left_ne_zero_of_mul_eq_one h2
    have hHe : emb X la N (X.inc u G) * CurveLoc.secOf X la N g = 0 :=
      CurveInj.vw_inj X la N Ω gF (wadd u wL) (hinj _)
        (mul_mem_Vw X la N (emb_mem_Vw X la N u G) (CurveLoc.secOf_mem X la N g))
        fun Z' => by
          rw [map_mul]
          by_cases hZ' : Z' = Z
          · subst hZ'
            rw [rzMap_emb, h0, TensorProduct.tmul_zero, TensorProduct.tmul_zero, zero_mul]
          · rw [CurveLoc.rzMap_secOf_zero X la N (gF Z') g (fun k => (hg k).2 Z' hZ'), mul_zero]
    have h3 := congrArg ev hHe
    rw [map_mul, map_zero] at h3
    exact (mul_eq_zero.1 h3).resolve_right he
  · have h1 := ((hχ _).trans (hψ _ k _ rfl)).symm.trans (phi_fraction_base_value X la N w (gF Z) χ k G hG)
    show _ = χ (CurveLoc.psiZ X la N w (gF Z) (gF Z G)) * _
    rw [mul_pow, mul_left_comm, ← h1, mul_left_comm, ← mul_pow, mul_inv_cancel₀ hs0, one_pow, mul_one]

end Fam

section One

variable {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

theorem ev_sec {F : Type} [Field F] (ev : Rp X la N →+* F) (τ : Ω →+* F) (σ : F)
    (hc : ∀ (k : ℕ) (G : X.Forms), emb X la N G ∈ Vw X la N (addL (wt0 D j) wL k) →
      ev (emb X la N G) = τ (gF G) * σ ^ k) (i : Fin (WeightFamilies.dimY D j + 1)) :
    ev (sec X la w i) = (∑ k, evK X la N ev (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i, k))) *
      τ (gF (X.inc wL (w k)))) * σ := by
  unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ev_smul, hc 1 _ (by rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la N wL (w k)), pow_one, mul_assoc]

end One

end Rec

end GlobalTheory.SecPoint
