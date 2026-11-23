import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf
import Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountQAtStGenericSectionPrimes
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.AlgebraMapMemMax

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.T0

namespace GlobalTheory.GenSep

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

theorem exists_ne {F : Type} [Field F] (ev : Rp X la N →+* F) (hu : IsUnit (ev (sec X la w 0))) (τ : Ω →+* F) (σ : F)
    (hc : ∀ (k : ℕ) (G : X.Forms), emb X la N G ∈ Vw X la N (addL (wt0 D j) wL k) →
      ev (emb X la N G) = τ (gF G) * σ ^ k) : ∃ k, gF (X.inc wL (w k)) ≠ 0 := by
  by_contra h
  push Not at h
  apply hu.ne_zero
  rw [ev_sec X la N w gF ev τ σ hc]
  simp [h]

theorem cross {F : Type} [Field F] (ev : Rp X la N →+* F) (hu : IsUnit (ev (sec X la w 0))) (τ : Ω →+* F) (σ : F)
    (hσ : σ ≠ 0) (hB : CurveLoc.BirAt X N w gF)
    (ha : ∀ (u : WeightFamilies.Wt D j) (G : B.Cusp j u), gF (X.inc u G) = 0 → ev (emb X la N (X.inc u G)) = 0)
    (hc : ∀ (k : ℕ) (G : X.Forms), emb X la N G ∈ Vw X la N (addL (wt0 D j) wL k) →
      ev (emb X la N G) = τ (gF G) * σ ^ k) (u : WeightFamilies.Wt D j) (G G' : B.Cusp j u) :
    τ (gF (X.inc u G)) * ev (emb X la N (X.inc u G')) = τ (gF (X.inc u G')) * ev (emb X la N (X.inc u G)) := by
  by_cases h0 : gF (X.inc u G') = 0
  · rw [ha u G' h0, h0, map_zero, zero_mul, mul_zero]
  obtain ⟨m, p, q, hp, hpq⟩ := exists_ratio X N w gF hB (exists_ne X la N w gF ev hu τ σ hc)
    (gF (X.inc u G) / gF (X.inc u G'))
  obtain ⟨H1, hH1⟩ := X.inc_mul u _ G p
  obtain ⟨H2, hH2⟩ := X.inc_mul u _ G' q
  have h1 := ha _ (H1 - H2) (by
    rw [map_sub, map_sub, ← hH1, ← hH2, map_mul, map_mul, ← hpq]
    field_simp
    ring)
  rw [map_sub, map_sub, map_sub, ← hH1, ← hH2, map_mul, map_mul, map_mul, map_mul,
    hc m _ (emb_mem_Vw X la N _ p), hc m _ (emb_mem_Vw X la N _ q), ← hpq, map_mul, map_div₀, sub_eq_zero] at h1
  have h2 : τ (gF (X.inc u G')) ≠ 0 := (map_ne_zero τ).2 h0
  have h3 : τ (gF (X.inc _ p)) * σ ^ m ≠ 0 := mul_ne_zero ((map_ne_zero τ).2 hp) (pow_ne_zero _ hσ)
  apply mul_right_cancel₀ h3
  rw [mul_assoc (τ (gF (X.inc u G'))), h1]
  field_simp

theorem pair_mem {F F' : Type} [Field F] [Field F'] (ev : Rp X la N →+* F) (hu : IsUnit (ev (sec X la w 0)))
    (τ : Ω →+* F) (σ : F) (hσ : σ ≠ 0)
    (hc : ∀ (k : ℕ) (G : X.Forms), emb X la N G ∈ Vw X la N (addL (wt0 D j) wL k) →
      ev (emb X la N G) = τ (gF G) * σ ^ k)
    (ev' : Rp X la N →+* F') (hu' : IsUnit (ev' (sec X la w 0))) (τ' : Ω →+* F') (σ' : F') (hσ' : σ' ≠ 0)
    (hc' : ∀ (k : ℕ) (G : X.Forms), emb X la N G ∈ Vw X la N (addL (wt0 D j) wL k) →
      ev' (emb X la N G) = τ' (gF G) * σ' ^ k)
    (A : Subring (F × F')) (h1 : ∀ a, (τ a, τ' a) ∈ A) (h2 : ∀ c, (evK X la N ev c, evK X la N ev' c) ∈ A)
    (h3 : ∀ y y', (y, y') ∈ A → y ≠ 0 → y' ≠ 0 → (y⁻¹, y'⁻¹) ∈ A) (x : ↥(Frac0 X la w)) :
    (IsLocalization.Away.lift (sec X la w 0) hu (x : Lw X la w),
      IsLocalization.Away.lift (sec X la w 0) hu' (x : Lw X la w)) ∈ A := by
  have key : ∀ k, ∀ g ∈ Vw X la N (addL (wt0 D j) wL k), (ev g * σ⁻¹ ^ k, ev' g * σ'⁻¹ ^ k) ∈ A := by
    intro k g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨G, rfl⟩ := hx
      simp only
      rw [hc k _ (emb_mem_Vw X la N _ G), hc' k _ (emb_mem_Vw X la N _ G), mul_assoc, mul_assoc, ← mul_pow, ← mul_pow,
        mul_inv_cancel₀ hσ, mul_inv_cancel₀ hσ', one_pow, one_pow, mul_one, mul_one]
      exact h1 _
    | zero =>
      rw [map_zero, map_zero, zero_mul, zero_mul]
      exact A.zero_mem
    | add x y _ _ hx hy =>
      have := A.add_mem hx hy
      rwa [Prod.mk_add_mk, ← add_mul, ← add_mul, ← map_add, ← map_add] at this
    | smul c x _ hx =>
      have := A.mul_mem (h2 c) hx
      rwa [Prod.mk_mul_mk, ← mul_assoc, ← mul_assoc, ← ev_smul, ← ev_smul] at this
  obtain ⟨k, g, hg, hx⟩ := (mem_Hfr X la w).1 ((mem_Frac0 X la w).1 x.2)
  have hs := key 1 _ (by rw [add_zero_weight_one_eq]; exact sec_mem_Vw X la w 0)
  have hs0 := hu.ne_zero
  have hs0' := hu'.ne_zero
  have hi := h3 _ _ hs (mul_ne_zero hs0 (pow_ne_zero _ (inv_ne_zero hσ)))
    (mul_ne_zero hs0' (pow_ne_zero _ (inv_ne_zero hσ')))
  have := A.mul_mem (key k g hg) (A.pow_mem hi k)
  rw [hx, liftEv_frac, liftEv_frac]
  convert this using 1
  ext
  · simp only [Prod.fst_mul, Prod.pow_fst, pow_one, mul_inv, inv_inv, mul_pow, inv_pow]
    field_simp
  · simp only [Prod.snd_mul, Prod.pow_snd, pow_one, mul_inv, inv_inv, mul_pow, inv_pow]
    field_simp

end One

end Rec

section Pt

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

def valT (T : CDVR) : AddValuation T.Fr (WithTop ℤ) :=
  ValPl.addv T.Fr (IsDiscreteValuationRing.maximalIdeal T.V)

theorem valT_apply (T : CDVR) {x : T.Fr} (hx : x ≠ 0) : valT T x = (vV T.V x : ℤ) :=
  ValPl.addv_apply _ hx

theorem valT_nonneg (T : CDVR) (s : T.V) : 0 ≤ valT T (algebraMap T.V T.Fr s) := ValPl.addv_nonneg _ s

theorem valT_pos_iff (T : CDVR) (s : T.V) : 0 < valT T (algebraMap T.V T.Fr s) ↔ ¬ IsUnit s :=
  ValPl.addv_pos_iff _ s

theorem valT_irreducible (T : CDVR) {s : T.V} (hs : Irreducible s) : valT T (algebraMap T.V T.Fr s) = 1 := by
  have h0 : algebraMap T.V T.Fr s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hs.ne_zero
  rw [valT, ValPl.addv_apply _ h0, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton _ hs.ne_zero hs.maximalIdeal_eq]
  simp

theorem nval_lt_of_pos (T : CDVR) {a b : T.Fr} (hb : b ≠ 0) (ha : 0 < valT T a) :
    nval T.V 1 b < nval T.V 1 (a * b) := by
  by_cases h0 : a = 0
  · rw [h0, zero_mul, nval_zero, nval_of_ne hb]
    exact EReal.coe_lt_top _
  rw [valT_apply T h0] at ha
  have ha' : (0 : ℤ) < vV T.V a := by exact_mod_cast ha
  rw [nval_of_ne hb, nval_of_ne (mul_ne_zero h0 hb), vV_mul h0 hb, EReal.coe_lt_coe_iff]
  have : (0 : ℝ) < vV T.V a := by exact_mod_cast ha'
  push_cast
  linarith

variable {ζ : PtsG G la} {y : E.Pt' la} (h : FromW ζ y)

theorem evK_op (o : Op (xplus X E hM) la G.N) :
    evK (xplus X E hM) la G.N h.ev (algebraMap _ (Kp (xplus X E hM) la G.N) o) =
      algebraMap h.T.V h.T.Fr (h.ι (algebraMap _ (Loc ζ) o)) := by
  rw [← lift_algKp (xplus X E hM) la G.N G.w h.ev h.s0,
    h.evW _ (algebraMap _ _ o) ((toOsK (xplus X E hM) la G.w).commutes _), ← IsScalarTower.algebraMap_apply]

theorem pos_iff_mem (x : ↥(Frac0 (xplus X E hM) la G.w))
    (a : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)))
    (hx : toOsK (xplus X E hM) la G.w x = (a : OsK (xplus X E hM) la G.w)) :
    0 < valT h.T (IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) h.s0 (x : Lw (xplus X E hM) la G.w)) ↔
      a ∈ ζ.asIdeal := by
  have := h.loc
  rw [h.evW x a hx, valT_pos_iff, isUnit_map_iff, IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal]
  exact not_not

theorem exists_val_one : ∃ x : ↥(Frac0 (xplus X E hM) la G.w),
    valT h.T (IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) h.s0 (x : Lw (xplus X E hM) la G.w)) = 1 := by
  obtain ⟨ϖ, -, hϖ⟩ := h.unr
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj ζ.asIdeal.primeCompl ϖ
  obtain ⟨x, hx⟩ := toOsK_surjective (xplus X E hM) la G.w a
  refine ⟨x, ?_⟩
  rw [h.evW x a hx]
  refine valT_irreducible _ ?_
  have hu : IsUnit (h.ι (algebraMap _ (Loc ζ) (s : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))))) :=
    (IsLocalization.map_units (Loc ζ) s).map _
  simp only at hs
  rw [← hs, map_mul]
  exact (irreducible_mul_isUnit hu).2 hϖ

theorem overGauss {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : (xplus X E hM).Forms →ₐ[B.KO] Ω)
    (τ : Ω →+* h.T.Fr) (σ : h.T.Fr) (hσ : σ ≠ 0)
    (hb : ∀ a : B.KO, τ (algebraMap B.KO Ω a) = evK (xplus X E hM) la G.N h.ev
      (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) (algebraMap B.KO ((xplus X E hM).Kl la) a)))
    (hc : ∀ (k : ℕ) (F : (xplus X E hM).Forms),
      emb (xplus X E hM) la G.N F ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) →
      h.ev (emb (xplus X E hM) la G.N F) = τ (gF F) * σ ^ k) :
    OverGauss la ((algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N)).comp
        (algebraMap (Pol (xplus X E hM) la G.N) (Op (xplus X E hM) la G.N)))
      (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N))
      (fun k => gF ((xplus X E hM).inc wL (G.w k))) (valT h.T) τ (evK (xplus X E hM) la G.N h.ev) := by
  have := h.loc
  refine ⟨fun Q => ?_, fun Q => ?_, hb, fun i => ?_⟩
  · rw [RingHom.comp_apply, evK_op]
    exact valT_nonneg _ _
  · rw [RingHom.comp_apply, evK_op, valT_pos_iff, isUnit_map_iff, isUnit_map_iff,
      IsLocalization.AtPrime.isUnit_to_map_iff (Op (xplus X E hM) la G.N) (gI (xplus X E hM) la G.N),
      ← MvPolynomial.mem_map_C_iff]
    exact not_not
  · have e := ev_sec (xplus X E hM) la G.N G.w gF h.ev τ σ hc i.succ
    rw [h.onS i] at e
    exact (mul_eq_zero.1 e.symm).resolve_right hσ

theorem kl_eq (Xr : PJ D B P j) (N : ℕ) (o : Xr.Ol la) :
    algebraMap (Xr.Kl la) (Kp Xr la N) o = ((algebraMap (Op Xr la N) (Kp Xr la N)).comp
      (algebraMap (Pol Xr la N) (Op Xr la N))) (MvPolynomial.C o) := by
  rw [RingHom.comp_apply, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply (Xr.Ol la) (Pol Xr la N) (Op Xr la N),
    ← IsScalarTower.algebraMap_apply (Xr.Ol la) (Op Xr la N) (Kp Xr la N)]
  exact (IsScalarTower.algebraMap_apply (Xr.Ol la) (Xr.Kl la) (Kp Xr la N) o).symm

theorem kp_frac (Xr : PJ D B P j) (N : ℕ) (c : Kp Xr la N) : ∃ a b,
    ((algebraMap (Op Xr la N) (Kp Xr la N)).comp (algebraMap (Pol Xr la N) (Op Xr la N))) b ≠ 0 ∧
    ((algebraMap (Op Xr la N) (Kp Xr la N)).comp (algebraMap (Pol Xr la N) (Op Xr la N))) b * c =
      ((algebraMap (Op Xr la N) (Kp Xr la N)).comp (algebraMap (Pol Xr la N) (Op Xr la N))) a := by
  obtain ⟨o, o', ho', rfl⟩ := IsFractionRing.div_surjective (A := Op Xr la N) c
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (gI Xr la N).primeCompl o
  obtain ⟨⟨a', s'⟩, hs'⟩ := IsLocalization.surj (gI Xr la N).primeCompl o'
  have h0 : algebraMap (Op Xr la N) (Kp Xr la N) o' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ho'
  have h1 := ((IsLocalization.map_units (Op Xr la N) s).map (algebraMap (Op Xr la N) (Kp Xr la N))).ne_zero
  have h2 := ((IsLocalization.map_units (Op Xr la N) s').map (algebraMap (Op Xr la N) (Kp Xr la N))).ne_zero
  simp only at hs hs'
  refine ⟨a * s', s * a', ?_, ?_⟩
  · simp only [RingHom.comp_apply, map_mul, ← hs']
    exact mul_ne_zero h1 (mul_ne_zero h0 h2)
  · simp only [RingHom.comp_apply, map_mul, ← hs', ← hs]
    field_simp

theorem att_lift {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : (xplus X E hM).Forms →ₐ[B.KO] Ω)
    (htr : Algebra.trdeg B.KO Ω = WeightFamilies.dimY D j)
    (τ : Ω →+* h.T.Fr) (σ : h.T.Fr) (hσ : σ ≠ 0)
    (hb : ∀ a : B.KO, τ (algebraMap B.KO Ω a) = evK (xplus X E hM) la G.N h.ev
      (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) (algebraMap B.KO ((xplus X E hM).Kl la) a)))
    (hc : ∀ (k : ℕ) (F : (xplus X E hM).Forms),
      emb (xplus X E hM) la G.N F ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) →
      h.ev (emb (xplus X E hM) la G.N F) = τ (gF F) * σ ^ k)
    {ζ' : PtsG G la} {y' : E.Pt' la} (h' : FromW ζ' y')
    (τ' : Ω →+* h'.T.Fr) (σ' : h'.T.Fr) (hσ' : σ' ≠ 0)
    (hb' : ∀ a : B.KO, τ' (algebraMap B.KO Ω a) = evK (xplus X E hM) la G.N h'.ev
      (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) (algebraMap B.KO ((xplus X E hM).Kl la) a)))
    (hc' : ∀ (k : ℕ) (F : (xplus X E hM).Forms),
      emb (xplus X E hM) la G.N F ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) →
      h'.ev (emb (xplus X E hM) la G.N F) = τ' (gF F) * σ' ^ k)
    (heq : ∀ a, valT h.T (τ a) = valT h'.T (τ' a)) (x : ↥(Frac0 (xplus X E hM) la G.w)) :
    ∃ a : Ω, valT h.T (IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) h.s0 (x : Lw (xplus X E hM) la G.w)) =
        valT h.T (τ a) ∧
      valT h'.T (IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) h'.s0 (x : Lw (xplus X E hM) la G.w)) =
        valT h'.T (τ' a) := by
  obtain ⟨A, hA, h1, h2, h3⟩ := exists_att (kl_eq (xplus X E hM) G.N) (kp_frac (xplus X E hM) G.N) htr
    (exists_ne (xplus X E hM) la G.N G.w gF h.ev h.s0 τ σ hc) (overGauss h gF τ σ hσ hb hc)
    (overGauss h' gF τ' σ' hσ' hb' hc') heq
  exact hA _ (pair_mem (xplus X E hM) la G.N G.w gF h.ev h.s0 τ σ hσ hc h'.ev h'.s0 τ' σ' hσ' hc' A h1 h2 h3 x)

theorem val_one {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : (xplus X E hM).Forms →ₐ[B.KO] Ω)
    (htr : Algebra.trdeg B.KO Ω = WeightFamilies.dimY D j)
    (τ : Ω →+* h.T.Fr) (σ : h.T.Fr) (hσ : σ ≠ 0)
    (hb : ∀ a : B.KO, τ (algebraMap B.KO Ω a) = evK (xplus X E hM) la G.N h.ev
      (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) (algebraMap B.KO ((xplus X E hM).Kl la) a)))
    (hc : ∀ (k : ℕ) (F : (xplus X E hM).Forms),
      emb (xplus X E hM) la G.N F ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) →
      h.ev (emb (xplus X E hM) la G.N F) = τ (gF F) * σ ^ k) : ∃ a : Ω, valT h.T (τ a) = 1 := by
  obtain ⟨x, hx⟩ := exists_val_one h
  obtain ⟨a, ha, -⟩ := att_lift h gF htr τ σ hσ hb hc h τ σ hσ hb hc (fun _ => rfl) x
  exact ⟨a, ha.symm.trans hx⟩

theorem sep {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : (xplus X E hM).Forms →ₐ[B.KO] Ω)
    (htr : Algebra.trdeg B.KO Ω = WeightFamilies.dimY D j) (hB : CurveLoc.BirAt (xplus X E hM) G.N G.w gF)
    (τ : Ω →+* h.T.Fr) (σ : h.T.Fr) (hσ : σ ≠ 0)
    (hb : ∀ a : B.KO, τ (algebraMap B.KO Ω a) = evK (xplus X E hM) la G.N h.ev
      (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) (algebraMap B.KO ((xplus X E hM).Kl la) a)))
    (hc : ∀ (k : ℕ) (F : (xplus X E hM).Forms),
      emb (xplus X E hM) la G.N F ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) →
      h.ev (emb (xplus X E hM) la G.N F) = τ (gF F) * σ ^ k)
    {ζ' : PtsG G la} {y' : E.Pt' la} (h' : FromW ζ' y')
    (τ' : Ω →+* h'.T.Fr) (σ' : h'.T.Fr) (hσ' : σ' ≠ 0)
    (hb' : ∀ a : B.KO, τ' (algebraMap B.KO Ω a) = evK (xplus X E hM) la G.N h'.ev
      (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) (algebraMap B.KO ((xplus X E hM).Kl la) a)))
    (hc' : ∀ (k : ℕ) (F : (xplus X E hM).Forms),
      emb (xplus X E hM) la G.N F ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) →
      h'.ev (emb (xplus X E hM) la G.N F) = τ' (gF F) * σ' ^ k) (hne : ζ ≠ ζ') :
    ∃ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u),
      h.ev (emb (xplus X E hM) la G.N (X.inc u F')) ≠ 0 ∧ h'.ev (emb (xplus X E hM) la G.N (X.inc u F')) ≠ 0 ∧
      nval h.T.V 1 (h.ev (emb (xplus X E hM) la G.N (X.inc u F'))) <
        nval h.T.V 1 (h.ev (emb (xplus X E hM) la G.N (X.inc u F))) ∧
      nval h'.T.V 1 (h'.ev (emb (xplus X E hM) la G.N (X.inc u F'))) <
        nval h'.T.V 1 (h'.ev (emb (xplus X E hM) la G.N (X.inc u F)) -
          h'.ev (emb (xplus X E hM) la G.N (X.inc u F'))) := by
  have hv : (valT h.T).comap τ ≠ (valT h'.T).comap τ' := by
    intro hv
    have heq : ∀ a, valT h.T (τ a) = valT h'.T (τ' a) := fun a => DFunLike.congr_fun hv a
    refine hne (MaximalSpectrum.ext (Ideal.ext fun a => ?_))
    obtain ⟨x, hx⟩ := toOsK_surjective (xplus X E hM) la G.w a
    obtain ⟨b, hb1, hb2⟩ := att_lift h gF htr τ σ hσ hb hc h' τ' σ' hσ' hb' hc' heq x
    rw [← pos_iff_mem h x a hx, ← pos_iff_mem h' x a hx, hb1, hb2, heq]
  obtain ⟨a, ha, ha'⟩ := exists_sep _ _ (val_one h gF htr τ σ hσ hb hc) (val_one h' gF htr τ' σ' hσ' hb' hc') hv
  obtain ⟨m, p, q, hp, hpq⟩ := exists_ratio (xplus X E hM) G.N G.w gF hB
    (exists_ne (xplus X E hM) la G.N G.w gF h.ev h.s0 τ σ hc) a
  have hpq' : a * gF (X.inc _ p) = gF (X.inc _ q) := hpq
  have e1 : h.ev (emb (xplus X E hM) la G.N (X.inc _ p)) = _ := hc m _ (emb_mem_Vw (xplus X E hM) la G.N _ p)
  have e2 : h.ev (emb (xplus X E hM) la G.N (X.inc _ q)) = _ := hc m _ (emb_mem_Vw (xplus X E hM) la G.N _ q)
  have e3 : h'.ev (emb (xplus X E hM) la G.N (X.inc _ p)) = _ := hc' m _ (emb_mem_Vw (xplus X E hM) la G.N _ p)
  have e4 : h'.ev (emb (xplus X E hM) la G.N (X.inc _ q)) = _ := hc' m _ (emb_mem_Vw (xplus X E hM) la G.N _ q)
  have n1 : h.ev (emb (xplus X E hM) la G.N (X.inc _ p)) ≠ 0 := by
    rw [e1]; exact mul_ne_zero ((map_ne_zero τ).2 hp) (pow_ne_zero _ hσ)
  have n2 : h'.ev (emb (xplus X E hM) la G.N (X.inc _ p)) ≠ 0 := by
    rw [e3]; exact mul_ne_zero ((map_ne_zero τ').2 hp) (pow_ne_zero _ hσ')
  refine ⟨_, q, p, n1, n2, ?_, ?_⟩
  · have e : h.ev (emb (xplus X E hM) la G.N (X.inc _ q)) = τ a * h.ev (emb (xplus X E hM) la G.N (X.inc _ p)) := by
      rw [e1, e2, ← hpq', map_mul, mul_assoc]
    rw [e]
    exact nval_lt_of_pos h.T n1 ha
  · have e : h'.ev (emb (xplus X E hM) la G.N (X.inc _ q)) - h'.ev (emb (xplus X E hM) la G.N (X.inc _ p)) =
        τ' (a - 1) * h'.ev (emb (xplus X E hM) la G.N (X.inc _ p)) := by
      rw [e3, e4, ← hpq', map_mul, map_sub, map_one]
      ring
    rw [e]
    exact nval_lt_of_pos h'.T n2 ha'

omit h in

theorem valSep_fam {ι : Type} [Finite ι] (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
    (gF : ∀ Z, (xplus X E hM).Forms →ₐ[B.KO] Ω Z) (val : ∀ Z (u : WeightFamilies.Wt D j), B.Cusp j u → Ω Z)
    (hval : ∀ Z u F, gF Z ((xplus X E hM).inc u F) = val Z u F)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, val Z u F = 0) → F = 0)
    (hsplit : ∀ (Z : ι) (k : Fin G.N), ∃ g : B.Cusp j wL,
      gF Z ((xplus X E hM).inc wL g) = gF Z ((xplus X E hM).inc wL (G.w k)) ∧
      ∀ Z', Z' ≠ Z → gF Z' ((xplus X E hM).inc wL g) = 0)
    (hB : ∀ Z, CurveLoc.BirAt (xplus X E hM) G.N G.w (gF Z))
    (hC : ∀ Z, CurveLoc.CountQAt (xplus X E hM) la G.N G.w (gF Z))
    (htr : ∀ Z, Algebra.trdeg B.KO (Ω Z) = WeightFamilies.dimY D j)
    (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) :
    ∃ (Zc : PtsG G la → ι) (τ : ∀ ζ, Ω (Zc ζ) →+* (hw ζ).T.Fr),
      (∀ ζ, ∃ a : Ω (Zc ζ), vV (hw ζ).T.V (τ ζ a) = 1) ∧
      (∀ ζ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), val (Zc ζ) u F = 0 →
          (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F)) = 0) ∧
      (∀ ζ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u),
        τ ζ (val (Zc ζ) u F) * (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F')) =
          τ ζ (val (Zc ζ) u F') * (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F))) ∧
      ∀ ζ ζ', ζ ≠ ζ' → Zc ζ = Zc ζ' →
        ∃ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u),
          (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F')) ≠ 0 ∧
          (hw ζ').ev (emb (xplus X E hM) la G.N (X.inc u F')) ≠ 0 ∧
          nval (hw ζ).T.V 1 ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F'))) <
            nval (hw ζ).T.V 1 ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F))) ∧
          nval (hw ζ').T.V 1 ((hw ζ').ev (emb (xplus X E hM) la G.N (X.inc u F'))) <
            nval (hw ζ').T.V 1 ((hw ζ').ev (emb (xplus X E hM) la G.N (X.inc u F)) -
              (hw ζ').ev (emb (xplus X E hM) la G.N (X.inc u F'))) := by
  choose Zc τ σ hσ ha hb hc using fun ζ => exists_point (xplus X E hM) la G.N G.w Ω gF
    (fun u F hF => hinj u F fun Z => (hval Z u F).symm.trans (hF Z)) hsplit hB hC (hw ζ).ev (hw ζ).s0 (hw ζ).onS
  refine ⟨Zc, τ, fun ζ => ?_, fun ζ u F hF => ha ζ u F ((hval _ u F).trans hF), fun ζ u F F' => ?_,
    fun ζ ζ' hne hZ => ?_⟩
  · obtain ⟨a, h1⟩ := val_one (hw ζ) (gF _) (htr _) (τ ζ) (σ ζ) (hσ ζ) (hb ζ) (hc ζ)
    have h0 : τ ζ a ≠ 0 := wa_ne_zero_of_coe _ (m := 1) h1
    rw [valT_apply _ h0] at h1
    exact ⟨a, by exact_mod_cast h1⟩
  · rw [← hval, ← hval]
    exact cross (xplus X E hM) la G.N G.w (gF _) (hw ζ).ev (hw ζ).s0 (τ ζ) (σ ζ) (hσ ζ) (hB _) (ha ζ) (hc ζ) u F F'
  · have hb' := hb ζ'
    have hc' := hc ζ'
    generalize τ ζ' = τ' at hb' hc'
    generalize Zc ζ' = Z' at hZ τ' hb' hc'
    subst hZ
    exact sep (hw ζ) (gF _) (htr _) (hB _) (τ ζ) (σ ζ) (hσ ζ) (hb ζ) (hc ζ) (hw ζ') τ' (σ ζ') (hσ ζ') hb' hc' hne

end Pt

theorem valSep_of_curveHyp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ValSepSt h j hj hG G la := by
  intro D T h j hj hG hT ka wL wF G S g0 la hH hV hC hB y hw
  have := CompFin.finite_comp (T.Q.Xo j) T.Q.c
  exact valSep_fam (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (G := G) (la := la)
    (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z) (fun Z => formsEvR j hG hT Z)
    (fun Z u F => evC hG Z ((F : (recB h.toLawsCore).Cusp j u) : T.R j))
    (fun Z u F => formsEvR_inc h j hj hG hT Z u F) hV (fun Z k => split_of h j hj hG hT hC G Z k)
    (fun Z => birAt_of h j hj hG hT G hB Z) (GlobalTheory.SecCount.countQAtSt D T h j hj hG hT ka wL wF G S g0 la hH)
    (GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj).2 y hw

end GlobalTheory.GenSep
