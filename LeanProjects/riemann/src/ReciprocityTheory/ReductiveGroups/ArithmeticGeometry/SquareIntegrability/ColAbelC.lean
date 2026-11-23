import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TranslationZeroModeLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ActEMemSpanOmega
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelB

namespace ReciprocityTheory.ChartRestriction.G.I2

section

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E}

theorem cab_emb_sep {σ τ : E →+* ℂ} (h : σ ≠ τ) : ∃ α : 𝓞 E, σ (α : E) ≠ τ (α : E) := by
  by_contra hc
  push Not at hc
  apply h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => hc x)

omit [IsCMField E] in
theorem cab_conjugate_ne [IsTotallyComplex E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by
  intro h
  have hr : ComplexEmbedding.IsReal σ := ComplexEmbedding.isReal_iff.2 h
  have hc := IsTotallyComplex.isComplex (InfinitePlace.mk σ)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hr)

theorem cab_actE_inPart {σ : E →+* ℂ} {v : Vsp X.dim} (hv : InPart σ v) (β : E) :
    actE β v = σ β • v := by
  ext j
  simp only [actE_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases h : j.1 = σ
  · rw [h]
  · rw [hv j h, mul_zero, mul_zero]

theorem cab_Hf_K (K : Submodule ℝ (Vsp X.dim)) (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    (v u : Vsp X.dim) (hu : u ∈ K) : Hf v u = ∑ j, Col.z K j u * Col.z K j v := by
  conv_lhs => rw [← Col.proj_one_of_mem hK hu]
  simp only [Col.p1, Col.Hf_sum_r, Col.Hf_smul_r]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hr : (starRingEnd ℂ) (Col.z K j u) = Col.z K j u := by
    apply Complex.conj_eq_iff_im.mpr
    exact hK u hu _ (Col.e_mem K j)
  rw [hr]; rfl

theorem cab_S_zero (K : Submodule ℝ (Vsp X.dim)) (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    (hst : ∀ (α : 𝓞 E) a, a ∈ K → act α a ∈ K) (σ : E →+* ℂ) (v : Vsp X.dim) (hv : InPart σ v) :
    Col.S K v = 0 := by
  obtain ⟨α, hα⟩ := cab_emb_sep (σ := σ) (τ := ComplexEmbedding.conjugate σ) (cab_conjugate_ne σ).symm
  set a : E := (α : E) with ha
  set b : E := IsCMField.complexConj E a with hb
  have hba : IsCMField.complexConj E b = a := by simp [hb]
  have hKa : ∀ u ∈ K, actE a u ∈ K := fun u hu => hst α u hu
  have hKb : ∀ u ∈ K, actE b u ∈ K := fun u hu =>
    hst (IsCMField.ringOfIntegersComplexConj E α) u hu
  have hσb : σ b = (starRingEnd ℂ) (σ a) := by
    simp [hb, IsCMField.complexEmbedding_complexConj]

  have hent : ∀ j k, Col.z K j (actE b (Col.e K k)) = Col.z K k (actE a (Col.e K j)) := by
    intro j k
    simp only [Col.z]
    rw [Hf_actE, hba, Col.Hf_swap (actE a (Col.e K j))]
    apply Complex.conj_eq_iff_im.mpr
    exact hK _ (hKa _ (Col.e_mem K j)) _ (Col.e_mem K k)
  have h1 : σ a * Col.S K v =
      ∑ k, ∑ j, Col.z K j (actE b (Col.e K k)) * Col.z K j v * Col.z K k v := by
    have : ∀ k, Col.z K k (actE a v) = ∑ j, Col.z K j (actE b (Col.e K k)) * Col.z K j v := by
      intro k
      simp only [Col.z]
      rw [Hf_actE, ← hb]
      exact cab_Hf_K K hK v _ (hKb _ (Col.e_mem K k))
    have h2 : ∀ k, Col.z K k (actE a v) = σ a * Col.z K k v := by
      intro k; simp only [Col.z]; rw [cab_actE_inPart hv, Col.Hf_smul_l]
    simp only [Col.S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, ← this k, h2 k]; ring
  have h3 : (starRingEnd ℂ) (σ a) * Col.S K v =
      ∑ j, ∑ k, Col.z K k (actE a (Col.e K j)) * Col.z K k v * Col.z K j v := by
    have : ∀ j, Col.z K j (actE b v) = ∑ k, Col.z K k (actE a (Col.e K j)) * Col.z K k v := by
      intro j
      simp only [Col.z]
      rw [Hf_actE, hba]
      exact cab_Hf_K K hK v _ (hKa _ (Col.e_mem K j))
    have h2 : ∀ j, Col.z K j (actE b v) = (starRingEnd ℂ) (σ a) * Col.z K j v := by
      intro j; simp only [Col.z]; rw [cab_actE_inPart hv, Col.Hf_smul_l, hσb]
    simp only [Col.S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← this j, h2 j]; ring
  have h4 : σ a * Col.S K v = (starRingEnd ℂ) (σ a) * Col.S K v := by
    rw [h1, h3, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hent]; ring
  have hne : σ a - (starRingEnd ℂ) (σ a) ≠ 0 := by
    rw [sub_ne_zero]
    simpa [ComplexEmbedding.conjugate_coe_eq] using hα
  have h5 : (σ a - (starRingEnd ℂ) (σ a)) * Col.S K v = 0 := by rw [sub_mul, h4, sub_self]
  exact (mul_eq_zero.mp h5).resolve_left hne

end

end

section

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] {X : PT E}

def cabVP {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Submodule ℂ (Vsp dim) where
  carrier := {v | InPart σ v}
  add_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]

theorem cab_Hf_IR {I : Submodule ℤ (Vsp X.dim)} {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0) :
    ∀ a ∈ IR I, Hf ξ a = 0 := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact hξ x hx
  | zero => simp [Hf]
  | add x y _ _ hx hy => rw [Col.Hf_add_r, hx, hy, add_zero]
  | smul r x _ hx => rw [Col.Hf_rsmul_r, hx, mul_zero]

theorem cab_z_xi {I : Submodule ℤ (Vsp X.dim)} {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0)
    (k : Fin (Col.dK (IR I))) : Col.z (IR I) k ξ = 0 :=
  cab_Hf_IR hξ _ (Col.e_mem _ k)

theorem cab_Hf_wmap_xi {I : Submodule ℤ (Vsp X.dim)} (hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0)
    {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0) (x : Vsp X.dim) : Hf (Col.wmap (IR I) x) (Col.wmap (IR I) ξ) = Hf x ξ := by
  have hp1 : Col.p1 (IR I) ξ = 0 := by
    simp [Col.p1, cab_z_xi hξ]
  have hp2 : Col.p2 (IR I) ξ = ξ := by rw [Col.p2, hp1, sub_zero]
  rw [Col.Hf_wmap hK, hp2, Col.p2, Col.Hf_sub_l]
  have : Hf (Col.p1 (IR I) x) ξ = 0 := by
    simp only [Col.p1, Col.Hf_sum_l, Col.Hf_smul_l]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Col.Hf_swap, ← Col.z, cab_z_xi hξ, map_zero, mul_zero]
  rw [this, sub_zero]

theorem cab_norm_wmap_xi {I : Submodule ℤ (Vsp X.dim)} (hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0)
    {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0) :
    ‖Col.wmap (IR I) ξ‖ = ‖ξ‖ := by
  have hp1 : Col.p1 (IR I) ξ = 0 := by
    simp [Col.p1, cab_z_xi hξ]
  rw [Col.norm_wmap hK, Col.p2, hp1, sub_zero]

theorem cab_main {I : Submodule ℤ (Vsp X.dim)} (hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0)
    {c : ℕ} (σ : E →+* ℂ) {ξ : Vsp X.dim}
    (hξ : ∀ a ∈ I, Hf ξ a = 0) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ)
    (hβ : Differentiable ℂ β) {inst : DecidableEq (Fin (Col.gB (IR I)))}
    (hjet : ∀ α : Fin (Col.gB (IR I)) →₀ ℕ, α.degree ≤ c →
      polyDeriv (MvPolynomial.monomial α 1) (fun i => @EuclideanSpace.single _ ℂ _ inst i 1) β 0 =
        polyDeriv (MvPolynomial.monomial α 1) (fun i => @EuclideanSpace.single _ ℂ _ inst i 1)
          (fun t : EuclideanSpace ℂ (Fin (Col.gB (IR I))) =>
            MvPolynomial.eval (fun i => t i) (cabPoly (Col.wmap (IR I) ξ) c)) 0)
    (F0 : Vsp X.dim → ℂ) (hF0d : Differentiable ℂ F0)
    (hF0 : ∀ v, InPart σ v → F0 v = β (Col.wmap (IR I) v))
    (xs : Fin c → Vsp X.dim) (hxs : ∀ k, InPart σ (xs k)) :
    iteratedFDeriv ℂ c F0 0 xs = (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ := by
  set W := Col.wmap (IR I)
  set η := W ξ
  have hg : Differentiable ℂ (β ∘ W) := hβ.comp W.differentiable
  have h1 : iteratedFDeriv ℂ c F0 0 xs = iteratedFDeriv ℂ c (β ∘ W) 0 xs :=
    cab_restrict (cabVP σ) (contDiff_of_differentiable_fd hF0d c) (contDiff_of_differentiable_fd hg c)
      (fun v hv => hF0 v hv) xs hxs
  have hβc : ContDiff ℂ (⊤ : WithTop ℕ∞) β := cab_contDiff_top hβ
  have h2 : iteratedFDeriv ℂ c (β ∘ W) 0 xs = iteratedFDeriv ℂ c β 0 (fun k => W (xs k)) := by
    rw [W.iteratedFDeriv_comp_right (hβc.of_le le_top) 0 (by exact_mod_cast le_top)]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  let ℓ : EuclideanSpace ℂ (Fin (Col.gB (IR I))) →L[ℂ] ℂ := innerSL ℂ η
  have hℓ : ∀ t, ℓ t = Hf t η := by
    intro t; rw [Col.Hf_eq_inner]; rfl
  have hP : (fun t : EuclideanSpace ℂ (Fin (Col.gB (IR I))) =>
      MvPolynomial.eval (fun i => t i) (cabPoly η c)) = fun t => (ℓ t) ^ c := by
    funext t; rw [cabPoly_eval, hℓ]
  have hPd : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun t : EuclideanSpace ℂ (Fin (Col.gB (IR I))) =>
      MvPolynomial.eval (fun i => t i) (cabPoly η c)) := by
    rw [hP]; exact cab_contDiff_top (ℓ.differentiable.pow c)
  let _ := inst
  have h3 := cab_jet_eq hβc hPd hjet
  rw [h1, h2, h3, hP, cab_iter_pow]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hℓ]; exact cab_Hf_wmap_xi hK hξ (xs k)

end

end

section

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] {X : PT E}

theorem cab_IR_stable {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) :
    ∀ (α : 𝓞 E) a, a ∈ IR I → act α a ∈ IR I := by
  intro α a ha
  rw [act_eq_actE]
  exact actE_mem_of_span (α : E) (I : Set (Vsp X.dim)) (IR I)
    (fun v hv => Submodule.subset_span (hI.stable α v hv)) a ha

theorem cab_z_diff (K : Submodule ℝ (Vsp X.dim)) (k : Fin (Col.dK K)) :
    Differentiable ℂ (fun v => Col.z K k v) := by
  have : (fun v => Col.z K k v) = fun v => innerSL ℂ (Col.e K k) v := by
    funext v; simp only [Col.z]; rw [Col.Hf_eq_inner]; rfl
  rw [this]; exact (innerSL ℂ (Col.e K k)).differentiable

theorem differentiable_zeroModeLift (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ)
    (hβ : Differentiable ℂ β) : Differentiable ℂ (Col.F0 I q β) := by
  have hS : Differentiable ℂ (fun v => Col.S (IR I) v) := by
    have : (fun v => Col.S (IR I) v) = fun v => ∑ k, (Col.z (IR I) k v) ^ 2 := rfl
    rw [this]
    exact Differentiable.fun_sum fun k _ => (cab_z_diff _ k).pow 2
  have : Col.F0 I q β = fun v => cexp ((q * Real.pi / 2 : ℂ) * Col.S (IR I) v) * β (Col.wmap (IR I) v) := rfl
  rw [this]
  exact ((hS.const_mul _).cexp).mul (hβ.comp (Col.wmap (IR I)).differentiable)

theorem zeroModeLift_on_part [IsCMField E] {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I)
    (q : ℕ) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (σ : E →+* ℂ) (v : Vsp X.dim)
    (hv : InPart σ v) : Col.F0 I q β v = β (Col.wmap (IR I) v) := by
  have h0 := cab_S_zero (IR I) (Col.hK_of hI) (cab_IR_stable hI) σ v hv
  simp only [Col.F0, h0, mul_zero, Complex.exp_zero, one_mul]

end

end

end ReciprocityTheory.ChartRestriction.G.I2
