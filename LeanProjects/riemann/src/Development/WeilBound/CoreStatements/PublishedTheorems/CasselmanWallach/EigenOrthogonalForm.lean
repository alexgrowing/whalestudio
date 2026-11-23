import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.CW

namespace BilinearFormCasimir

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def tr (k : KG ε) (v : kfin ε σ) : kfin ε σ :=
  ⟨σ (toMK k⁻¹) v, isKFin_translate (mem_kfin.1 v.2) (toMK_mem_K _)⟩

theorem tr_add (k : KG ε) (v v' : kfin ε σ) : tr k (v + v') = tr k v + tr k v' :=
  Subtype.ext (map_add (σ (toMK k⁻¹)) (v : H) v')

theorem tr_smul (k : KG ε) (c : ℂ) (v : kfin ε σ) : tr k (c • v) = c • tr k v :=
  Subtype.ext (map_smul (σ (toMK k⁻¹)) c (v : H))

theorem continuous_tr (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v : kfin ε σ) :
    Continuous fun k : KG ε => l (tr k v) := by
  obtain ⟨S, hSf, hvS, hSK⟩ := mem_kfin.1 v.2
  haveI := hSf
  have hSk : ∀ x ∈ S, x ∈ kfin ε σ := fun x hx => mem_kfin.2 ⟨S, hSf, hx, hSK⟩
  let ι : S →ₗ[ℂ] kfin ε σ :=
    { toFun := fun x => ⟨x, hSk x x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hc : Continuous (l ∘ₗ ι) := LinearMap.continuous_of_finiteDimensional _
  have hmem : ∀ k : KG ε, σ (toMK k⁻¹) v ∈ S := fun k => hSK _ (toMK_mem_K _) _ hvS
  have h1 : Continuous fun k : KG ε => σ (toMK k⁻¹) (v : H) :=
    (hU.2.2 v).comp_continuous ((continuous_toMK ε).comp continuous_inv) fun k => K_le_UJ (toMK_mem_K _)
  have h2 : Continuous fun k : KG ε => (⟨σ (toMK k⁻¹) v, hmem k⟩ : S) := h1.subtype_mk _
  exact (hc.comp h2).congr fun k => rfl

def fm (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) : ℂ := ∫ k, conj (l (tr k v)) * l (tr k y) ∂(muK ε)

theorem integrable_fm (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) :
    Integrable (fun k : KG ε => conj (l (tr k v)) * l (tr k y)) (muK ε) := by
  haveI : CompactSpace (KG ε) := instCompactKG n ε
  have hc : Continuous fun k : KG ε => conj (l (tr k v)) * l (tr k y) :=
    ((continuous_tr hU l v).star).mul (continuous_tr hU l y)
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

def bf (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fm l)
    (fun v v' y => by
      unfold fm
      rw [← integral_add (integrable_fm hU l v y) (integrable_fm hU l v' y)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_add, map_add, add_mul])
    (fun c v y => by
      unfold fm
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_smul, map_smul, smul_eq_mul, map_mul]
      ring)
    (fun v y y' => by
      unfold fm
      rw [← integral_add (integrable_fm hU l v y) (integrable_fm hU l v y')]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_add, map_add, mul_add])
    (fun c v y => by
      unfold fm
      rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_smul, map_smul, smul_eq_mul]
      ring)

theorem bf_apply (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) :
    bf hU l v y = fm l v y := rfl

end BilinearFormCasimir

open BilinearFormCasimir in
theorem e2b : E2b := by
  intro n ε H _ _ _ σ hU hI Q hQ v₀ hv₀
  have hv0 : v₀ ≠ 0 := fun h => hv₀ (by rw [h, map_zero])

  let f0 : (ℂ ∙ v₀) →ₗ[ℂ] ℂ := (LinearPMap.mkSpanSingleton v₀ ((Q v₀ : ℝ) : ℂ) hv0).toFun
  have hf0 : ∀ x : (ℂ ∙ v₀), ‖f0 x‖ ≤ Q x := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have e : f0 ⟨c • v₀, hx⟩ = c • ((Q v₀ : ℝ) : ℂ) :=
      LinearPMap.mkSpanSingleton'_apply v₀ ((Q v₀ : ℝ) : ℂ) _ c hx
    rw [e, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg Q v₀)]
    exact (map_smul_eq_mul Q c v₀).symm.le
  obtain ⟨l, hl, hlQ⟩ := Module.Dual.exists_extension_of_le_seminorm (ℂ ∙ v₀) f0 hf0
  have hlv : l v₀ = ((Q v₀ : ℝ) : ℂ) := by
    have h1 : v₀ ∈ (ℂ ∙ v₀) := Submodule.mem_span_singleton_self v₀
    have h1' : (1 : ℂ) • v₀ ∈ (ℂ ∙ v₀) := by rw [one_smul]; exact h1
    rw [hl ⟨v₀, h1⟩]
    have e : f0 ⟨(1 : ℂ) • v₀, h1'⟩ = (1 : ℂ) • ((Q v₀ : ℝ) : ℂ) :=
      LinearPMap.mkSpanSingleton'_apply v₀ ((Q v₀ : ℝ) : ℂ) _ 1 h1'
    have e' : (⟨v₀, h1⟩ : (ℂ ∙ v₀)) = ⟨(1 : ℂ) • v₀, h1'⟩ := Subtype.ext (one_smul ℂ v₀).symm
    rw [e', e, one_smul]
  have hQtr : ∀ (k : KG ε) (v : kfin ε σ), Q (tr k v) = Q v := fun k v => hQ _ (toMK_mem_K _) v _ rfl
  refine ⟨bf hU l, fun k hk v y v' y' hv' hy' => ?_, fun v y => ?_, ?_⟩
  ·
    obtain ⟨k0, rfl⟩ : ∃ k0 : KG ε, toMK k0 = k := by rw [← range_toMK ε] at hk; exact hk
    have htr : ∀ (k : KG ε) (w w' : kfin ε σ), (w' : H) = σ (toMK k0) w → tr k w' = tr (k0⁻¹ * k) w := by
      intro k w w' hw
      apply Subtype.ext
      show σ (toMK k⁻¹) (w' : H) = σ (toMK (k0⁻¹ * k)⁻¹) w
      rw [hw, ← sigma_mul hU (K_le_UJ (toMK_mem_K _)) (K_le_UJ (toMK_mem_K _))]
      congr 2
    rw [bf_apply, bf_apply, fm, fm]
    simp only [htr _ _ _ hv', htr _ _ _ hy']
    exact integral_mul_left_eq_self (fun k => conj (l (tr k v)) * l (tr k y)) k0⁻¹
  · rw [bf_apply, fm]
    have h := norm_integral_le_of_norm_le_const (μ := muK ε) (f := fun k => conj (l (tr k v)) * l (tr k y))
      (C := Q v * Q y) (Filter.Eventually.of_forall fun k => by
        rw [norm_mul, RCLike.norm_conj, ← hQtr k v, ← hQtr k y]
        exact mul_le_mul (hlQ _) (hlQ _) (norm_nonneg _) (apply_nonneg _ _))
    simpa [measure_univ] using h
  · rw [bf_apply, fm]
    haveI : CompactSpace (KG ε) := instCompactKG n ε
    have e : ∀ k : KG ε, conj (l (tr k v₀)) * l (tr k v₀) = ((‖l (tr k v₀)‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [mul_comm, Complex.mul_conj']
      push_cast
      ring
    simp only [e]
    rw [integral_complex_ofReal]
    have hpos : 0 < ∫ k, ‖l (tr k v₀)‖ ^ 2 ∂(muK ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        ((continuous_tr hU l v₀).norm.pow 2) (isClosed_tsupport _).isCompact (fun k => by positivity) ?_
      have h1 : tr (1 : KG ε) v₀ = v₀ := Subtype.ext (by
        show σ (toMK (1 : KG ε)⁻¹) (v₀ : H) = v₀
        rw [inv_one]
        exact sigma_one hU _)
      rw [h1, hlv, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg Q v₀)]
      exact pow_ne_zero 2 hv₀
    exact_mod_cast hpos.ne'

end PositivityTheory.CW

end
