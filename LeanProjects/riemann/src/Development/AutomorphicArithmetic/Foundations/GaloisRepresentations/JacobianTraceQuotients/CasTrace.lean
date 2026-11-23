import GroundTheory.AutomorphicForms.MeasuresGL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExistsAvg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.DcosOp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.HeckeMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.KerKill
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuotAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.DcosVol
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.JacNorm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ImStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}

private def pw (σ : k ≃+* k) (t : Fin n → kˣ) : ℕ → Fin n → kˣ
  | 0 => 1
  | m + 1 => t * fun i => Units.map (σ : k →* k) (pw σ t m i)

private theorem val_pw {σ : k ≃+* k} (h : Isom σ) (t : Fin n → kˣ) (i : Fin n) :
    ∀ m, valuation k (pw σ t m i : k) = valuation k (t i : k) ^ m
  | 0 => by simp [pw]
  | m + 1 => by
    have := h (pw σ t m i)
    simp only [pw, Pi.mul_apply, Units.val_mul, map_mul, Units.coe_map, MonoidHom.coe_coe, this, val_pw h t i m, pow_succ']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem sg_diag (σ : k ≃+* k) (s : Fin n → kˣ) :
    Loc.sg σ (diagT k (Fin n) s) = diagT k (Fin n) fun i => Units.map (σ : k →* k) (s i) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sg_val, val_diagT, val_diagT, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem small {t : Fin n → kˣ} (ht : Strict t) {r : ValueGroupWithZero k} (hr : r ≠ 0) :
    ∀ᶠ m : ℕ in atTop, ∀ i j, i < j → valuation k (t i : k) ^ m ≤ r * valuation k (t j : k) ^ m := by
  simp only [eventually_all]
  intro i j hij
  have h0 : valuation k (t j : k) ≠ 0 := by simp
  have h1 : valuation k (t i : k) / valuation k (t j : k) < 1 := (div_lt_one₀ (zero_lt_iff.2 h0)).2 (ht i j hij)
  obtain ⟨M, hM⟩ := exists_pow_lt₀ h1 (Units.mk0 r hr)
  filter_upwards [eventually_ge_atTop M] with m hm
  have h2 : (valuation k (t i : k) / valuation k (t j : k)) ^ m ≤ r := (pow_le_pow_right_of_le_one' h1.le hm).trans hM.le
  rwa [div_pow, div_le_iff₀ (zero_lt_iff.2 (pow_ne_zero _ h0))] at h2

private theorem unif {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {e : V →ₗ[ℂ] V} (he : IsAvg π K e) (Z : Submodule ℂ V)
    [FiniteDimensional ℂ Z] (hZ : Z ≤ twKer π (unipB k (Fin n)) 1) {t : Fin n → kˣ} (ht : Strict t) {σ : k ≃+* k} (h : Isom σ) :
    ∃ m, 0 < m ∧ ∀ v ∈ Z, e (π (diagT k (Fin n) (pw σ t m)) v) = 0 := by
  obtain ⟨s, hs⟩ := (Submodule.fg_top Z).1 (Module.finite_def.1 inferInstance)
  have : ∀ᶠ m : ℕ in atTop, ∀ v ∈ s, e (π (diagT k (Fin n) (pw σ t m)) v) = 0 := by
    rw [eventually_all_finset]
    intro v hv
    obtain ⟨r, hr, hk⟩ := kerKill k n V π K hK e he v (hZ (hs ▸ Submodule.subset_span hv))
    filter_upwards [small ht hr] with m hm
    exact hk _ fun i j hij => by rw [val_pw h, val_pw h]; exact hm i j hij
  obtain ⟨m, hm, h0⟩ := (this.and (eventually_gt_atTop 0)).exists
  refine ⟨m, h0, fun v hv => ?_⟩
  have : Z ≤ LinearMap.ker (e ∘ₗ π (diagT k (Fin n) (pw σ t m))) := hs ▸ Submodule.span_le.2 hm
  exact this hv

end SlopeTestRemainingChoices

private theorem trIn_smul' {X : Type} [AddCommGroup X] [Module ℂ X] {P : Submodule ℂ X} {T : X →ₗ[ℂ] X}
    (h : ∀ y ∈ P, T y ∈ P) (c : ℂ) : trIn P (c • T) = c * trIn P T := by
  have h' : ∀ y ∈ P, (c • T) y ∈ P := fun y hy => P.smul_mem c (h y hy)
  rw [trIn, trIn, dif_pos h, dif_pos h', ← smul_eq_mul, ← map_smul]
  rfl

theorem UpperTheory.Gal.Join.casTrace :
    UpperTheory.Gal.Join.CasTrace := by
  intro k _ _ _ _ n V _ _ π ha _ _ μ _ K hK σ A hA hσ hst t ht
  have hd : Dom t := fun i j h => (ht i j h).le
  obtain ⟨e, he, hc⟩ := avgEx _ V π ha.1 K hK.co
  have hAe : ∀ v, A (e v) = e (A v) := hc (Loc.sg σ) A hA (fun g hg => (hst g).2 hg) fun g hg => by
    have e1 : Loc.sg σ (Loc.sg σ.symm g) = g := Units.ext (Matrix.ext fun i j => σ.apply_symm_apply _)
    exact ⟨Loc.sg σ.symm g, (hst _).1 (by rwa [e1]), e1⟩
  have hfix : ∀ v ∈ fixed π K, A v ∈ fixed π K := fun v hv => by rw [← he.fix v hv, hAe]; exact he.mem _
  haveI : μ.IsMulRightInvariant := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k n μ
  haveI : FiniteDimensional ℂ (fixed π K) := ha.2 K hK.co.2 hK.co.1
  refine ⟨_, dcosOp _ V μ π ha.1 K hK.co e he (diagT k (Fin n) t), ?_⟩
  obtain ⟨-, s1, s2⟩ := imStab k n V π ha K hK
  change HasFinTrace (((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A) _
  have hq : ((Real.sqrt (deltaB t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (deltaB_pos _)).ne'
  have key := traceQuot V _ (fixed π K) (((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A)
    (twKer π (unipB k (Fin n)) 1).mkQ
    (((μ.real (K : Set (GL (Fin n) k)) : ℂ) * ((Real.sqrt (deltaB t) : ℝ) : ℂ)⁻¹) • (jacB π t ∘ₗ jacA hA))
    (fun v => Submodule.smul_mem _ _ (he.mem _)) (fun v hv => ?_) fun v hv h0 => ?_
  · rwa [trIn_smul' (P := (fixed π K).map (twKer π (unipB k (Fin n)) 1).mkQ) (T := jacB π t ∘ₗ jacA hA)
      fun y hy => s1 t _ (s2 σ A hA hst y hy)] at key
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
    rw [he.fix _ (hfix v hv), (heckeMul k n V π K hK e he t hd _ (hfix v hv)).2, jacNorm k n V π, smul_smul,
      (dcosVol k n μ K hK t hd).2]
    congr 1
    have h2 : ((deltaB t : ℝ) : ℂ) = ((Real.sqrt (deltaB t) : ℝ) : ℂ) * ((Real.sqrt (deltaB t) : ℝ) : ℂ) := by
      exact_mod_cast (Real.mul_self_sqrt (deltaB_pos t).le).symm
    push_cast
    rw [h2]
    field_simp
  · obtain ⟨m, -, hm⟩ := unif hK he (fixed π K ⊓ twKer π (unipB k (Fin n)) 1) inf_le_right ht hσ
    have hZ : ∀ j : ℕ, (A ^ j) v ∈ fixed π K ⊓ twKer π (unipB k (Fin n)) 1 := fun j => by
      induction j with
      | zero => exact ⟨hv, (Submodule.Quotient.mk_eq_zero _).1 h0⟩
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply]
        refine ⟨hfix _ ih.1, (Submodule.Quotient.mk_eq_zero _).1 ?_⟩
        rw [← jacA_mk hA, (Submodule.Quotient.mk_eq_zero _).2 ih.2, map_zero]
    have hP : ∀ j : ℕ, ((((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A) ^ j) v =
        (μ.real (dcos K t) : ℂ) ^ j • e (π (diagT k (Fin n) (pw σ t j)) ((A ^ j) v)) := fun j => by
      induction j with
      | zero => simp [pw, he.fix v hv]
      | succ j ih =>
        have hdj : Dom fun i => Units.map (σ : k →* k) (pw σ t j i) := fun a b hab => by
          have h1 := hσ (pw σ t j a)
          have h2 := hσ (pw σ t j b)
          simp only [Units.coe_map, MonoidHom.coe_coe, h1, h2, val_pw hσ]
          exact pow_le_pow_left' (hd a b hab) j
        rw [pow_succ', Module.End.mul_apply, ih, map_smul]
        simp only [LinearMap.comp_apply, LinearMap.smul_apply]
        rw [hAe, he.fix _ (he.mem _), hA, sg_diag, (heckeMul k n V π K hK e he _ hdj _ (hfix _ (hZ j).1)).1 t hd, smul_smul,
          ← pow_succ, pow_succ' A]
        rfl
    exact ⟨m, by rw [hP, hm _ (hZ m), smul_zero]⟩
