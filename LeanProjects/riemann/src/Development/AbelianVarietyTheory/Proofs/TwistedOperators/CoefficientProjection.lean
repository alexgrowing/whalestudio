import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.UnitaryMatrixFamily

variable {n : ℕ} {ε : Fin n → Bool}

theorem umat_mem (h : UJ ε) : umat h ∈ UJset ε := h.2

theorem umat_mul (a b : UJ ε) : umat (a * b) = umat a * umat b := rfl

theorem umat_one : umat (1 : UJ ε) = 1 := rfl

theorem continuous_umat : Continuous (umat : UJ ε → Matrix (Fin n) (Fin n) ℂ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem exists_umat {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : ∃ h : UJ ε, umat h = g := by
  have hJ := Jm_mul_self ε
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hL : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hJ]
  have hR : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.1 hL
  exact ⟨⟨⟨g, _, hR, hL⟩, hg⟩, rfl⟩

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem rep_one (hσ : IsURepOn (UJset ε) σ) : σ (umat (1 : UJ ε)) = 1 := by
  rw [umat_one]; exact hσ.1.1

theorem rep_one_apply (hσ : IsURepOn (UJset ε) σ) (x : H) : σ (umat (1 : UJ ε)) x = x := by
  rw [rep_one hσ]; rfl

theorem rep_mul (hσ : IsURepOn (UJset ε) σ) (a b : UJ ε) (x : H) :
    σ (umat (a * b)) x = σ (umat a) (σ (umat b) x) := by
  rw [umat_mul, hσ.1.2 _ (umat_mem a) _ (umat_mem b)]; rfl

theorem rep_norm (hσ : IsURepOn (UJset ε) σ) (a : UJ ε) (x : H) : ‖σ (umat a) x‖ = ‖x‖ :=
  hσ.2.1 _ (umat_mem a) x

theorem rep_inner (hσ : IsURepOn (UJset ε) σ) (a : UJ ε) (x y : H) :
    ⟪σ (umat a) x, σ (umat a) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ (umat a)).toLinearMap, hσ.2.1 _ (umat_mem a)⟩
  exact L.inner_map_map x y

theorem rep_inv_apply (hσ : IsURepOn (UJset ε) σ) (a : UJ ε) (x : H) :
    σ (umat a) (σ (umat a⁻¹) x) = x := by
  rw [← rep_mul hσ, mul_inv_cancel, rep_one_apply hσ]

theorem rep_inner_left (hσ : IsURepOn (UJset ε) σ) (a : UJ ε) (x y : H) :
    ⟪σ (umat a) x, y⟫_ℂ = ⟪x, σ (umat a⁻¹) y⟫_ℂ := by
  conv_lhs => rw [← rep_inv_apply hσ a y]
  exact rep_inner hσ a x _

theorem rep_continuous (hσ : IsURepOn (UJset ε) σ) (x : H) : Continuous fun h : UJ ε => σ (umat h) x :=
  (hσ.2.2 x).comp_continuous continuous_umat umat_mem

theorem coef_continuous (hσ : IsURepOn (UJset ε) σ) (x y : H) :
    Continuous fun h : UJ ε => ⟪y, σ (umat h) x⟫_ℂ :=
  continuous_const.inner (rep_continuous hσ x)

end Rep

end GlobalTheory.SepReal.UnitaryMatrixFamily

namespace GlobalTheory.SepReal.CoefProjProof

open GlobalTheory.SepReal.UnitaryMatrixFamily

variable {n : ℕ} {ε' : Fin n → Bool} {H' K : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem weak_exists (σ : Mat n → (H' →L[ℂ] H')) (ρ : Mat n → (K →L[ℂ] K)) (d : ℝ) (w : H')
    (hσ : IsURepOn (UJset ε') σ) (hρ : IsURepOn (UJset ε') ρ)
    (hi : Integrable (fun h => ⟪w, σ (umat h) w⟫_ℂ) (muG ε')) :
    ∃ Q : K →L[ℂ] K, ∀ x y, ⟪y, Q x⟫_ℂ =
      (d : ℂ) * ∫ h, star ⟪w, σ (umat h) w⟫_ℂ * ⟪y, ρ (umat h) x⟫_ℂ ∂muG ε' := by
  set m := fun h : UJ ε' => ⟪w, σ (umat h) w⟫_ℂ with hm
  have hint : ∀ x : K, Integrable (fun h => star (m h) • ρ (umat h) x) (muG ε') := by
    intro x
    refine Integrable.mono' (hi.norm.mul_const ‖x‖)
      ((continuous_star.comp (coef_continuous hσ w w)).smul (rep_continuous hρ x)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun h => ?_)
    rw [norm_smul, norm_star, rep_norm hρ]
  let L : K →ₗ[ℂ] K :=
    { toFun := fun x => (d : ℂ) • ∫ h, star (m h) • ρ (umat h) x ∂muG ε'
      map_add' := fun x y => by
        simp only [map_add, smul_add]
        rw [integral_add (hint x) (hint y), smul_add]
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply]
        rw [show (fun h => star (m h) • c • ρ (umat h) x) = fun h => c • (star (m h) • ρ (umat h) x) from
          funext fun h => smul_comm _ _ _, integral_smul, smul_comm] }
  refine ⟨L.mkContinuous (‖(d : ℂ)‖ * ∫ h, ‖m h‖ ∂muG ε') fun x => ?_, fun x y => ?_⟩
  · show ‖(d : ℂ) • ∫ h, star (m h) • ρ (umat h) x ∂muG ε'‖ ≤ _
    rw [norm_smul, mul_assoc]
    gcongr
    refine (norm_integral_le_of_norm_le (hi.norm.mul_const ‖x‖)
      (Filter.Eventually.of_forall fun h => ?_)).trans_eq (integral_mul_const _ _)
    rw [norm_smul, norm_star, rep_norm hρ]
  · show ⟪y, (d : ℂ) • ∫ h, star (m h) • ρ (umat h) x ∂muG ε'⟫_ℂ = _
    rw [inner_smul_right, ← integral_inner (hint x)]
    simp only [inner_smul_right, hm]

theorem fixes (σ : Mat n → (H' →L[ℂ] H')) (ρ : Mat n → (K →L[ℂ] K)) (d : ℝ) (w : H') (Q : K →L[ℂ] K)
    (hfd : IsFdeg (muG ε') σ d) (hw : ‖w‖ = 1)
    (hQ : ∀ x y, ⟪y, Q x⟫_ℂ = (d : ℂ) * ∫ h, star ⟪w, σ (umat h) w⟫_ℂ * ⟪y, ρ (umat h) x⟫_ℂ ∂muG ε')
    (j : H' →L[ℂ] K) (hj : ∀ h ∈ UJset ε', ∀ a, j (σ h a) = ρ h (j a)) : Q (j w) = j w := by
  refine ext_inner_left ℂ fun y => ?_
  rw [hQ]
  have h1 : ∀ h : UJ ε', star ⟪w, σ (umat h) w⟫_ℂ * ⟪y, ρ (umat h) (j w)⟫_ℂ =
      coefOn σ w (ContinuousLinearMap.adjoint j y) h * star (coefOn σ w w h) := by
    intro h
    rw [← hj _ (umat_mem h), ← ContinuousLinearMap.adjoint_inner_left j]
    simp only [coefOn]; ring
  simp_rw [h1]
  rw [(hfd.2 w _ w w).2, inner_self_eq_norm_sq_to_K, hw, ContinuousLinearMap.adjoint_inner_left]
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast hfd.1.ne'
  field_simp
  simp

end GlobalTheory.SepReal.CoefProjProof

namespace GlobalTheory.SepReal.CoefProjProof

open GlobalTheory.SepReal.UnitaryMatrixFamily

variable {n : ℕ} {ε' : Fin n → Bool} {H' K : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem dense_orbit (σ : Mat n → (H' →L[ℂ] H')) (hσ : IsURepOn (UJset ε') σ) (hirr : IsIrredOn (UJset ε') σ)
    (w : H') (hw : w ≠ 0) : DenseRange (Finsupp.linearCombination ℂ fun g : UJ ε' => σ (umat g) w) := by
  set A := Finsupp.linearCombination ℂ fun g : UJ ε' => σ (umat g) w with hA
  set S := (LinearMap.range A).topologicalClosure with hS
  have hSc : IsClosed (S : Set H') := (LinearMap.range A).isClosed_topologicalClosure
  have hstab : ∀ s ∈ UJset ε', ∀ v ∈ S, σ s v ∈ S := by
    intro s hs v hv
    obtain ⟨a, rfl⟩ := exists_umat hs
    have hmap : LinearMap.range A ≤ S.comap (σ (umat a)).toLinearMap := by
      rintro _ ⟨c, rfl⟩
      show σ (umat a) (A c) ∈ S
      apply Submodule.le_topologicalClosure
      refine ⟨c.mapDomain (a * ·), ?_⟩
      rw [hA, Finsupp.linearCombination_mapDomain, ← ContinuousLinearMap.coe_coe,
        Finsupp.apply_linearCombination]
      exact congrArg (fun f => Finsupp.linearCombination ℂ f c) (funext fun g => rep_mul hσ a g w)
    have hcl : IsClosed ((S.comap (σ (umat a)).toLinearMap : Submodule ℂ H') : Set H') :=
      hSc.preimage (σ (umat a)).continuous
    exact Submodule.topologicalClosure_minimal _ hmap hcl hv
  rcases hirr S hSc hstab with h | h
  · exfalso
    apply hw
    have : w ∈ S := Submodule.le_topologicalClosure _ ⟨Finsupp.single 1 1, by simp [hA, rep_one_apply hσ]⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · have : Dense ((LinearMap.range A : Submodule ℂ H') : Set H') :=
      (Submodule.dense_iff_topologicalClosure_eq_top).2 h
    rw [DenseRange, ← LinearMap.coe_range]; exact this

theorem extend (σ : Mat n → (H' →L[ℂ] H')) (ρ : Mat n → (K →L[ℂ] K)) (w : H') (ξ : K)
    (hσ : IsURepOn (UJset ε') σ) (hirr : IsIrredOn (UJset ε') σ) (hρ : IsURepOn (UJset ε') ρ) (hw : ‖w‖ = 1)
    (hξ : ∀ g : UJ ε', ⟪ξ, ρ (umat g) ξ⟫_ℂ = ⟪w, σ (umat g) w⟫_ℂ * ⟪ξ, ξ⟫_ℂ) :
    ∃ j : H' →L[ℂ] K, (∀ h ∈ UJset ε', ∀ a, j (σ h a) = ρ h (j a)) ∧ j w = ξ := by
  have hu : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
  set A := Finsupp.linearCombination ℂ fun g : UJ ε' => σ (umat g) w with hA
  set B := Finsupp.linearCombination ℂ fun g : UJ ε' => ρ (umat g) ξ with hB
  have hd : DenseRange A := dense_orbit σ hσ hirr w hu
  have hgram : ∀ g h : UJ ε', ⟪ρ (umat g) ξ, ρ (umat h) ξ⟫_ℂ =
      ⟪σ (umat g) w, σ (umat h) w⟫_ℂ * ⟪ξ, ξ⟫_ℂ := by
    intro g h
    rw [rep_inner_left hρ, rep_inner_left hσ, ← rep_mul hρ, ← rep_mul hσ, hξ]
  have hn : ∀ c, ‖B c‖ = ‖ξ‖ * ‖A c‖ := by
    intro c
    have h : ⟪B c, B c⟫_ℂ = ⟪A c, A c⟫_ℂ * ⟪ξ, ξ⟫_ℂ := by
      simp only [hA, hB, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right, hgram, Finset.sum_mul, mul_assoc]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖B c‖ ^ 2 = (‖ξ‖ * ‖A c‖) ^ 2 := by
      rw [mul_pow, mul_comm]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'
  have hT : ∀ c, B.extendOfNorm A (A c) = B c :=
    LinearMap.extendOfNorm_eq hd ⟨‖ξ‖, fun c => (hn c).le⟩
  have hg : ∀ g : UJ ε', B.extendOfNorm A (σ (umat g) w) = ρ (umat g) ξ := fun g => by
    simpa [hA, hB] using hT (Finsupp.single g 1)
  refine ⟨B.extendOfNorm A, fun s hs a => ?_, by simpa [rep_one_apply hσ, rep_one_apply hρ] using hg 1⟩
  obtain ⟨t, rfl⟩ := exists_umat hs
  have hlin : ((B.extendOfNorm A).comp (σ (umat t))).toLinearMap ∘ₗ A =
      ((ρ (umat t)).comp (B.extendOfNorm A)).toLinearMap ∘ₗ A := by
    apply Finsupp.lhom_ext
    intro g r
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp', Function.comp_apply,
      hA, Finsupp.linearCombination_single, map_smul]
    rw [← rep_mul hσ, hg, hg, rep_mul hρ]
  have hEq : (B.extendOfNorm A).comp (σ (umat t)) = (ρ (umat t)).comp (B.extendOfNorm A) := by
    apply DFunLike.coe_injective
    refine hd.equalizer ((B.extendOfNorm A).comp (σ (umat t))).continuous ((ρ (umat t)).comp (B.extendOfNorm A)).continuous ?_
    funext c
    exact LinearMap.congr_fun hlin c
  exact DFunLike.congr_fun hEq a

end GlobalTheory.SepReal.CoefProjProof

namespace GlobalTheory.SepReal.CoefProjProof

open GlobalTheory.SepReal.UnitaryMatrixFamily

variable {n : ℕ} {ε' : Fin n → Bool} {H' K : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem schur_conv (σ : Mat n → (H' →L[ℂ] H')) (d : ℝ) (w : H') (hσ : IsURepOn (UJset ε') σ)
    (hfd : IsFdeg (muG ε') σ d) (g k : UJ ε') :
    ∫ h, ⟪w, σ (umat h) w⟫_ℂ * star ⟪w, σ (umat (g⁻¹ * (h * k))) w⟫_ℂ ∂muG ε' =
      ⟪w, σ (umat g) w⟫_ℂ * star ⟪w, σ (umat k) w⟫_ℂ / d := by
  have e : ∀ h : UJ ε', ⟪w, σ (umat (g⁻¹ * (h * k))) w⟫_ℂ = ⟪σ (umat g) w, σ (umat h) (σ (umat k) w)⟫_ℂ := by
    intro h
    rw [rep_inner_left hσ, ← rep_mul hσ h k, ← rep_mul hσ]
  simp_rw [e]
  have h2 := (hfd.2 w w (σ (umat k) w) (σ (umat g) w)).2
  simp only [coefOn] at h2
  rw [h2, ← inner_conj_symm (σ (umat k) w) w]
  simp only [RCLike.star_def]
  ring

theorem coef_of_Q (σ : Mat n → (H' →L[ℂ] H')) (ρ : Mat n → (K →L[ℂ] K)) (d : ℝ) (w : H') (Q : K →L[ℂ] K)
    (hσ : IsURepOn (UJset ε') σ) (hfd : IsFdeg (muG ε') σ d) (hρ : IsURepOn (UJset ε') ρ)
    (hi : Integrable (fun h => ⟪w, σ (umat h) w⟫_ℂ) (muG ε'))
    (hQ : ∀ x y, ⟪y, Q x⟫_ℂ = (d : ℂ) * ∫ h, star ⟪w, σ (umat h) w⟫_ℂ * ⟪y, ρ (umat h) x⟫_ℂ ∂muG ε')
    (x : K) (g : UJ ε') : ⟪Q x, ρ (umat g) (Q x)⟫_ℂ = ⟪w, σ (umat g) w⟫_ℂ * ⟪x, Q x⟫_ℂ := by
  set m := fun h : UJ ε' => ⟪w, σ (umat h) w⟫_ℂ with hm
  set c := fun k : UJ ε' => ⟪x, ρ (umat k) x⟫_ℂ with hc
  have hmc : Continuous m := coef_continuous hσ w w
  have hcc : Continuous c := coef_continuous hρ x x
  have hleft : ∀ y, ⟪Q x, y⟫_ℂ = (d : ℂ) * ∫ h, m h * ⟪ρ (umat h) x, y⟫_ℂ ∂muG ε' := by
    intro y
    rw [← inner_conj_symm, hQ, map_mul, ← integral_conj]
    simp only [Complex.conj_ofReal, map_mul, hm, RCLike.star_def, RCLike.conj_conj, inner_conj_symm]
  have hmid : ∀ h, ⟪ρ (umat h) x, ρ (umat g) (Q x)⟫_ℂ =
      (d : ℂ) * ∫ k, star (m (g⁻¹ * (h * k))) * c k ∂muG ε' := by
    intro h
    have e1 := rep_inner_left hρ g⁻¹ (ρ (umat h) x) (Q x)
    rw [inv_inv] at e1
    rw [← e1, ← rep_mul hρ, hQ]
    congr 1
    refine (integral_mul_left_eq_self _ (g⁻¹ * h)).symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall fun k => ?_))
    simp only [hm, hc]
    rw [rep_mul hρ (g⁻¹ * h) k, rep_inner hρ, mul_assoc]
  set G := fun h k : UJ ε' => m h * star (m (g⁻¹ * (h * k))) * c k with hGdef
  have hP : Integrable (fun p : UJ ε' × UJ ε' => m p.1 * m (g⁻¹ * (p.1 * p.2))) ((muG ε').prod (muG ε')) :=
    (measurePreserving_prod_mul (muG ε') (muG ε')).integrable_comp_of_integrable
      (hi.mul_prod (hi.comp_mul_left g⁻¹))
  have hG : Integrable (Function.uncurry G) ((muG ε').prod (muG ε')) := by
    refine Integrable.mono' (hP.norm.mul_const (‖x‖ * ‖x‖)) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have : Continuous (Function.uncurry G) :=
        ((hmc.comp continuous_fst).mul ((continuous_star.comp hmc).comp
          (continuous_const.mul (continuous_fst.mul continuous_snd)))).mul (hcc.comp continuous_snd)
      exact this.aestronglyMeasurable
    · simp only [Function.uncurry, hGdef, norm_mul, norm_star]
      gcongr
      refine (norm_inner_le_norm _ _).trans ?_
      rw [rep_norm hρ]
  have hswap := integral_integral_swap hG
  rw [hleft]
  simp_rw [hmid]
  have e2 : ∀ h, m h * ((d : ℂ) * ∫ k, star (m (g⁻¹ * (h * k))) * c k ∂muG ε') = (d : ℂ) * ∫ k, G h k ∂muG ε' := by
    intro h
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hGdef]; ring
  simp_rw [e2]
  rw [integral_const_mul, hswap]
  have e3 : ∀ k, ∫ h, G h k ∂muG ε' = m g * star (m k) / d * c k := by
    intro k
    simp only [hGdef]
    rw [integral_mul_const]
    congr 1
    exact schur_conv σ d w hσ hfd g k
  simp_rw [e3]
  rw [hQ x x]
  have e4 : ∀ k, m g * star (m k) / d * c k = (m g / d) * (star (m k) * c k) := fun k => by ring
  simp_rw [e4]
  rw [integral_const_mul]
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast hfd.1.ne'
  simp only [hm, hc]
  field_simp

end GlobalTheory.SepReal.CoefProjProof
