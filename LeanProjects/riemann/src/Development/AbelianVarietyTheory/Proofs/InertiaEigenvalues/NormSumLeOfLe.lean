import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormEqOfMemClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLatticeRationalFormMemLocalUnitBallStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulMemSupLatticeOfMemLocalUnitBallStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightVectorRealizationExistsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisRationalFormsLocalUnitBallStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitBallFiniteUnramifiedDescentComplexPadicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteUnramifiedApproximationPadicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserNormGapPadicEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisTer

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_sum_le_of_le {p : ℕ} [Fact p.Prime] {ι : Type} (s : Finset ι) (g : ι → ℂ_[p]) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ k ∈ s, ‖g k‖ ≤ r) : ‖∑ k ∈ s, g k‖ ≤ r := by
  first
  | exact @_root_.GlobalTheory.SingleStatement.main
  | exact _root_.GlobalTheory.SingleStatement.main
  | (apply _root_.GlobalTheory.SingleStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SingleStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SingleStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SingleStatement.main ..)

section Core

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

theorem fieldRange_embC : (embC YS iC b).fieldRange = (embS S iC b).fieldRange := by
  ext y
  simp only [RingHom.mem_fieldRange]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨c, rfl⟩ := (eKs YS).surjective a
    exact ⟨c, (embC_eKs YS iC b c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨eKs YS c, embC_eKs YS iC b c⟩

theorem kurAt_iff (a : FractionRing (D.ntw.O i)) : a ∈ kurAt YS iC b ↔ iC a ∈ kurC (embS S iC b) := by
  rw [kurAt, Subfield.mem_comap, kurC_congr _ (fieldRange_embC YS iC b)]

def coef {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (x : NX.Fm S i ((j : ℕ) + 1) b) (s : Fin n) :
    FractionRing (D.ntw.O i) :=
  (B.baseChange (NX.KB S i b)).repr x s

variable {b j} in
theorem coef_add {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (x y : NX.Fm S i ((j : ℕ) + 1) b)
    (s : Fin n) : coef b j B (x + y) s = coef b j B x s + coef b j B y s := by
  exact Finsupp.ext_iff.1 (map_add (B.baseChange (NX.KB S i b)).repr x y) s

variable {b j} in
theorem coef_neg {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (x : NX.Fm S i ((j : ℕ) + 1) b)
    (s : Fin n) : coef b j B (-x) s = -coef b j B x s := by
  exact Finsupp.ext_iff.1 (map_neg (B.baseChange (NX.KB S i b)).repr x) s

variable {b j} in
theorem coef_zero {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (s : Fin n) :
    coef b j B (0 : NX.Fm S i ((j : ℕ) + 1) b) s = 0 := by
  exact Finsupp.ext_iff.1 (map_zero (B.baseChange (NX.KB S i b)).repr) s

variable {b j} in
theorem coef_tmul {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (a : NX.KB S i b)
    (f : NX.FmK S ((j : ℕ) + 1)) (s : Fin n) :
    coef b j B (show NX.Fm S i ((j : ℕ) + 1) b from a ⊗ₜ[S.Ks] f) s =
      (show FractionRing (D.ntw.O i) from NX.ιK S i b (B.repr f s)) * (show FractionRing (D.ntw.O i) from a) := by
  exact Module.Basis.baseChange_repr_tmul (b := B) (x := a) (y := f) (i := s)

theorem coef_mem_kurAt {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1)))
    {x : NX.Fm S i ((j : ℕ) + 1) b} (hx : x ∈ ratForms S ((j : ℕ) + 1) b (kurAt YS iC b)) (s : Fin n) :
    coef b j B x s ∈ kurAt YS iC b := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, f, rfl⟩ := hx
    rw [coef_tmul]
    refine (kurAt YS iC b).mul_mem ?_ ha
    rw [kurAt_iff]
    exact mem_kurC (embS S iC b) (B.repr f s)
  | zero => rw [coef_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [coef_add]; exact add_mem hx hy
  | neg x _ hx => rw [coef_neg]; exact neg_mem hx

end Core

end GlobalTheory.GeoTie

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Core2

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

def oneK (f : NX.FmK S ((j : ℕ) + 1)) : NX.Fm S i ((j : ℕ) + 1) b := (1 : NX.KB S i b) ⊗ₜ[S.Ks] f

theorem eq_sum_coef {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (x : NX.Fm S i ((j : ℕ) + 1) b) :
    x = ∑ s, coef b j B x s • oneK b j (B s) := by
  have h := (B.baseChange (NX.KB S i b)).sum_repr x
  simp only [Module.Basis.baseChange_apply] at h
  exact h.symm

theorem valAt_eq_sum {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (x : NX.Fm S i ((j : ℕ) + 1) b)
    (z : FrC YS iC b ((j : ℕ) + 1)) :
    valAt YS fw j z x = ∑ s, iC (coef b j B x s) * valC z (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) := by
  conv_lhs => rw [eq_sum_coef b j B x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [valAt_smul]
  congr 1
  have h1 : iC (1 : NX.KB S i b) = 1 := map_one iC
  exact (valAt_tmul YS fw j z 1 (B s)).trans (by rw [h1, one_mul])

theorem mem_span_locBall
    (hiC : ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range)
    (hC1 : ∃ (n : ℕ) (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))), (∀ s, B s ∈ locBall YS fw iC b j) ∧
      ∀ g ∈ locBall YS fw iC b j, ∀ s, ‖embS S iC b (B.repr g s)‖ ≤ 1)
    (hC2 : ∀ (F' : Type) [Field F'] [NumberField F'] [Algebra S.Ks F'] (φ' : F' →+* ℂ_[D.ntw.l i]), (∀ a, φ' (algebraMap S.Ks F' a) = embS S iC b a) → (∀ a : S.Ks, vLa (placeAt φ') (algebraMap S.Ks F' a) = vLa (placeAt (embS S iC b)) a) → ∀ (n : ℕ) (a : Fin n → F') (f : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ z : Pts YS iC b ((j : ℕ) + 1), ‖∑ s, φ' (a s) * valC z.1 (cuspOf YS fw j (f s) : T0.R ((j : ℕ) + 1))‖ ≤ 1) → ∃ (m : ℕ) (β : Fin m → F') (g : Fin m → NX.FmK S ((j : ℕ) + 1)), (∀ t, ‖φ' (β t)‖ ≤ 1) ∧ (∀ t, g t ∈ locBall YS fw iC b j) ∧ ∑ s, a s ⊗ₜ[S.Ks] f s = ∑ t, β t ⊗ₜ[S.Ks] g t)
    (x : NX.Fm S i ((j : ℕ) + 1) b) (hx : x ∈ urBall YS fw iC b j 1) :
    x ∈ Submodule.span (D.ntw.O i) (oneK b j '' locBall YS fw iC b j) := by
  obtain ⟨n, B, hB, hBc⟩ := hC1
  have hkur : ∀ s, iC (coef b j B x s) ∈ kurC (embS S iC b) := fun s =>
    (kurAt_iff YS iC b _).1 (coef_mem_kurAt YS iC b j B hx.1 s)
  have hval : ∀ z : Pts YS iC b ((j : ℕ) + 1),
      ‖∑ s, iC (coef b j B x s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1))‖ ≤ 1 := fun z => by
    rw [← valAt_eq_sum]
    exact hx.2 z
  have hle : ∀ s, ‖iC (coef b j B x s)‖ ≤ 1 := by
    by_contra hne
    push_neg at hne
    obtain ⟨s1, hs1⟩ := hne
    obtain ⟨s0, -, hs0⟩ := Finset.exists_max_image Finset.univ (fun s => ‖iC (coef b j B x s)‖) ⟨s1, Finset.mem_univ _⟩
    have hM : 1 < ‖iC (coef b j B x s0)‖ := hs1.trans_le (hs0 s1 (Finset.mem_univ _))
    obtain ⟨c, hc⟩ := (GlobalTheory.KurValue.kurC_value_residue (D.ntw.l i) S.Ks (embS S iC b)).1 _ (hkur s0)
    have hcpos : 0 < ‖embS S iC b c‖ := by rw [← hc]; linarith
    have hc0 : embS S iC b c ≠ 0 := norm_pos_iff.1 hcpos
    set w : Fin n → ℂ_[D.ntw.l i] := fun s => iC (coef b j B x s) / embS S iC b c with hw
    have hw1 : ∀ s, ‖w s‖ ≤ 1 := fun s => by
      rw [hw, norm_div, ← hc, div_le_one (by linarith)]
      exact hs0 s (Finset.mem_univ _)
    have hw0 : ‖w s0‖ = 1 := by
      rw [hw, norm_div, ← hc, div_self (by linarith)]
    have hwk : ∀ s, w s ∈ kurC (embS S iC b) := fun s => div_mem (hkur s) (mem_kurC _ c)
    obtain ⟨ϖ, hϖ0, hϖ1, hϖ⟩ := GlobalTheory.T.exists_uniformiser_norm_gap_padic_embedding (D.ntw.l i) S.Ks (embS S iC b)
    set r := ‖embS S iC b ϖ‖ with hr
    have hcr : ‖embS S iC b c‖⁻¹ ≤ r := by
      have h1 : ‖embS S iC b c⁻¹‖ < 1 := by
        rw [map_inv₀, norm_inv, ← hc]
        exact inv_lt_one_of_one_lt₀ hM
      have := hϖ c⁻¹ h1
      rwa [map_inv₀, norm_inv] at this
    have hsum : ∀ z : Pts YS iC b ((j : ℕ) + 1),
        ‖∑ s, w s * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1))‖ ≤ r := fun z => by
      have e : ∑ s, w s * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) =
          (∑ s, iC (coef b j B x s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1))) * (embS S iC b c)⁻¹ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [hw]
        rw [div_eq_mul_inv]
        ring
      rw [e, norm_mul, norm_inv]
      calc _ ≤ 1 * ‖embS S iC b c‖⁻¹ := mul_le_mul_of_nonneg_right (hval z) (by positivity)
        _ ≤ r := by rw [one_mul]; exact hcr
    obtain ⟨F', _, _, _, φ', hφ', hunr, a', ha'⟩ := GlobalTheory.T.exists_finite_unramified_approximation_padic (D.ntw.l i) S.Ks (embS S iC b) n w hwk r hϖ0
    have hsum' : ∀ z : Pts YS iC b ((j : ℕ) + 1),
        ‖∑ s, φ' (a' s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1))‖ ≤ r := fun z => by
      have e : ∑ s, φ' (a' s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) =
          ∑ s, w s * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) +
            ∑ s, (φ' (a' s) - w s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hsum z) ?_)
      refine norm_sum_le_of_le _ _ hϖ0.le fun s _ => ?_
      rw [norm_mul]
      calc _ ≤ r * 1 := by
            refine mul_le_mul ?_ (hB s z) (norm_nonneg _) hϖ0.le
            rw [norm_sub_rev]
            exact (ha' s).le
        _ = r := mul_one r
    have hϖ' : φ' (algebraMap S.Ks F' ϖ) ≠ 0 := by rw [hφ']; exact norm_pos_iff.1 hϖ0
    obtain ⟨m, β, g, hβ, hg, heq⟩ := hC2 F' φ' hφ' hunr n (fun s => a' s * (algebraMap S.Ks F' ϖ)⁻¹) (fun s => B s)
      (fun z => by
        have e : ∑ s, φ' (a' s * (algebraMap S.Ks F' ϖ)⁻¹) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) =
            (∑ s, φ' (a' s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1))) * (φ' (algebraMap S.Ks F' ϖ))⁻¹ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_mul, map_inv₀]
          ring
        rw [e, norm_mul, norm_inv, hφ', ← hr]
        rw [← div_eq_mul_inv, div_le_one hϖ0]
        exact hsum' z)
    have hco := congrArg (fun t => (B.baseChange F').repr t s0) heq
    simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, Module.Basis.baseChange_repr_tmul,
      Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hco
    have h1 : ‖φ' (a' s0 * (algebraMap S.Ks F' ϖ)⁻¹)‖ ≤ 1 := by
      rw [hco, map_sum]
      refine norm_sum_le_of_le _ _ zero_le_one fun t _ => ?_
      rw [Algebra.smul_def, map_mul, hφ', norm_mul]
      calc _ ≤ 1 * 1 := mul_le_mul (hBc (g t) (hg t) s0) (hβ t) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have h2 : ‖φ' (a' s0)‖ ≤ r := by
      rw [map_mul, map_inv₀, hφ', norm_mul, norm_inv, ← hr, ← div_eq_mul_inv, div_le_one hϖ0] at h1
      exact h1
    have h3 : ‖w s0‖ ≤ r := by
      have := IsUltrametricDist.norm_add_le_max (w s0 - φ' (a' s0)) (φ' (a' s0))
      rw [sub_add_cancel] at this
      exact this.trans (max_le (ha' s0).le h2)
    linarith
  rw [eq_sum_coef b j B x]
  refine Submodule.sum_mem _ fun s _ => ?_
  obtain ⟨o, ho⟩ := (hiC (coef b j B x s)).1 (hle s)
  rw [← ho, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨B s, hB s, rfl⟩)

end Core2

end GlobalTheory.GeoTie

theorem GlobalTheory.GeoTie.supDescent_side : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), SupDescent YS fw iC b j := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC hiC b j
  have hA := GlobalTheory.T.supLatticeRationalForm_mem_localUnitBall D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j
  have hbdd := GlobalTheory.T.weight_vector_realization_exists D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j hA
  have h1 : iC (1 : NX.KB S i b) = 1 := map_one iC
  unfold SupDescent
  apply le_antisymm
  · rw [NX.Bsup, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    apply Submodule.subset_span
    refine ⟨tmul_mem_ratForms (b := b) (kurAt YS iC b).one_mem x, fun z => ?_⟩
    rw [valAt_tmul, h1, one_mul]
    exact hA x hx z
  · rw [Submodule.span_le]
    intro x hx
    have h := mem_span_locBall YS fw iC b j hiC (GlobalTheory.T.exists_basis_rationalForms_local_unit_ball D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j hbdd) (GlobalTheory.T.unitBall_finite_unramified_descent_complexPadic D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j hbdd) x hx
    refine (Submodule.span_le.2 ?_) h
    rintro _ ⟨f, hf, rfl⟩
    exact GlobalTheory.T.one_tmul_mem_supLattice_of_mem_localUnitBall D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j f hf
