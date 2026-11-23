import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EntirePeriodicEqZeroOfFourierCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependentThetaPrincipal

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaSpan

open Complex Matrix Filter Topology

variable {g : ℕ}

def hh (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ := z ⬝ᵥ Hm.mulVec (star w)

variable {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem hh_add_left (z z' w : Fin g → ℂ) : hh Hm (z + z') w = hh Hm z w + hh Hm z' w := by
  simp [hh, add_dotProduct]

theorem hh_smul_left (c : ℂ) (z w : Fin g → ℂ) : hh Hm (c • z) w = c * hh Hm z w := by
  simp [hh, smul_dotProduct]

theorem hh_add_right (z w w' : Fin g → ℂ) : hh Hm z (w + w') = hh Hm z w + hh Hm z w' := by
  simp [hh, star_add, mulVec_add, dotProduct_add]

theorem hh_smul_right (c : ℂ) (z w : Fin g → ℂ) : hh Hm z (c • w) = star c * hh Hm z w := by
  simp [hh, star_smul, mulVec_smul, dotProduct_smul]

theorem hh_sub_left (z z' w : Fin g → ℂ) : hh Hm (z - z') w = hh Hm z w - hh Hm z' w := by
  simp [hh, sub_dotProduct]

theorem hh_conj (hH : Hm.IsHermitian) (z w : Fin g → ℂ) : star (hh Hm z w) = hh Hm w z :=
  GlobalTheory.SiegelNormalForm.form_conj hH z w

theorem continuous_hh_diag : Continuous fun w : Fin g → ℂ => hh Hm w w := by
  have h : Continuous fun w : Fin g → ℂ => Hm.mulVec (star w) :=
    continuous_pi fun i => by
      simp only [mulVec, dotProduct, Pi.star_apply]
      exact continuous_finset_sum _ fun j _ =>
        continuous_const.mul ((continuous_apply j).star)
  simp only [hh, dotProduct]
  exact continuous_finset_sum _ fun j _ => (continuous_apply j).mul ((continuous_apply j).comp h)

theorem dense_torsion (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    Dense {w : Fin g → ℂ | ∃ N : ℕ, 1 ≤ N ∧ (N : ℂ) • w ∈ Λ} := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let b := (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  intro w
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((∑ i, ‖b i‖) / ε)
  have hC : 0 ≤ ∑ i, ‖b i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hN0 : 0 < (N : ℝ) := lt_of_le_of_lt (div_nonneg hC hε.le) hN
  have hN1 : 1 ≤ N := by exact_mod_cast hN0
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  set y : Fin g → ℂ := (ZSpan.floor b ((N : ℝ) • w) : Fin g → ℂ) with hy
  have hyΛ : y ∈ Λ := by
    have h : y ∈ Submodule.span ℤ (Set.range b) := (ZSpan.floor b ((N : ℝ) • w)).2
    rwa [show Submodule.span ℤ (Set.range b) = Λ from
      Module.Basis.ofZLatticeBasis_span ℝ Λ _] at h
  refine ⟨(N : ℂ)⁻¹ • y, ⟨N, hN1, ?_⟩, ?_⟩
  · rwa [smul_smul, mul_inv_cancel₀ hNc, one_smul]
  · have e1 : ZSpan.fract b ((N : ℝ) • w) = (N : ℝ) • w - y := rfl
    have e2 : w - (N : ℂ)⁻¹ • y = ((N : ℝ)⁻¹) • ZSpan.fract b ((N : ℝ) • w) := by
      rw [e1, smul_sub, smul_smul, inv_mul_cancel₀ hN0.ne', one_smul]
      congr 1
      ext i
      simp
    rw [dist_eq_norm, e2, norm_smul, norm_inv, Real.norm_of_nonneg hN0.le, inv_mul_lt_iff₀ hN0]
    refine lt_of_le_of_lt (ZSpan.norm_fract_le b _) ?_
    rwa [div_lt_iff₀ hε, ] at hN

theorem exists_eq_const_mul {f e : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (he : Differentiable ℂ e) (C : ℝ) (hC : 0 < C) (hn : ∀ w, ‖f w‖ = C * ‖e w‖) (h0 : e ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ f = c • e := by
  obtain ⟨w₀, hw₀⟩ : ∃ w, e w ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (funext h)
  have hnear : ∀ᶠ w in 𝓝 w₀, e w ≠ 0 := he.continuous.continuousAt.eventually_ne hw₀
  have hd : ∀ᶠ w in 𝓝 w₀, DifferentiableAt ℂ (fun w => f w / e w) w :=
    hnear.mono fun w hw => by
      simp only [div_eq_mul_inv]
      exact hf.differentiableAt.mul (he.differentiableAt.inv hw)
  have hmax : IsLocalMax (norm ∘ fun w => f w / e w) w₀ := by
    have hc : ∀ w, e w ≠ 0 → ‖f w / e w‖ = C := fun w hw => by
      rw [norm_div, hn, mul_div_assoc, div_self (norm_ne_zero_iff.2 hw), mul_one]
    filter_upwards [hnear] with w hw
    simp only [Function.comp, hc w hw, hc w₀ hw₀, le_refl]
  have hev := Complex.eventually_eq_of_isLocalMax_norm hd hmax
  set c := f w₀ / e w₀ with hcdef
  have hne : ∀ᶠ w in 𝓝 w₀, f w = c * e w := by
    filter_upwards [hev, hnear] with w h1 h2
    rw [← h1]
    field_simp
  have hc0 : c ≠ 0 := by
    intro h
    have := hn w₀
    have h1 : f w₀ = 0 := by
      have := hne.self_of_nhds
      rw [this, h, zero_mul]
    rw [h1, norm_zero] at this
    exact (mul_pos hC (norm_pos_iff.2 hw₀)).ne this
  refine ⟨c, hc0, funext fun w => ?_⟩

  let φ : ℂ → ℂ := fun t => f (w₀ + t • (w - w₀)) - c * e (w₀ + t • (w - w₀))
  have hl : Differentiable ℂ fun t : ℂ => w₀ + t • (w - w₀) := by fun_prop
  have hφ : Differentiable ℂ φ := (hf.comp hl).sub ((he.comp hl).const_mul c)
  have ha : AnalyticOnNhd ℂ φ Set.univ := fun t _ => hφ.analyticAt t
  have hz : φ =ᶠ[𝓝 0] 0 := by
    have hc : Tendsto (fun t : ℂ => w₀ + t • (w - w₀)) (𝓝 0) (𝓝 w₀) := by
      have := hl.continuous.tendsto 0
      simpa using this
    filter_upwards [hc.eventually hne] with t ht
    simp [φ, ht]
  have := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ (0 : ℂ)) hz (Set.mem_univ (1 : ℂ))
  simp only [φ, one_smul, add_sub_cancel, Pi.zero_apply] at this
  simpa using sub_eq_zero.1 this

end GlobalTheory.CompanionTheory.ThetaSpan

namespace GlobalTheory.CompanionTheory.ThetaSpan

open Complex Matrix Filter Topology

variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem exists_reps (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (m : ℕ) (hm : 1 ≤ m) {Ix : Type}
    (r : Ix → Fin g → ℂ) (hrep : ∀ w : Fin g → ℂ, (m : ℂ) • w ∈ Λ → ∃ i, w - r i ∈ Λ) :
    ∃ (J : Type) (_ : Fintype J) (s : J → Ix), Fintype.card J = (m ^ 2) ^ g ∧
      ∀ a b, r (s a) - r (s b) ∈ Λ → a = b := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  let b0 := Module.Free.chooseBasis ℤ Λ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = 2 * g := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  let v : (Module.Free.ChooseBasisIndex ℤ Λ → Fin m) → Λ := fun a => ∑ k, ((a k : ℕ) : ℤ) • b0 k
  have hv : ∀ a k, b0.repr (v a) k = ((a k : ℕ) : ℤ) := fun a k => by
    have := b0.repr_sum_self (fun k => ((a k : ℕ) : ℤ))
    exact congrFun this k
  have hmem : ∀ a, (m : ℂ) • ((m : ℂ)⁻¹ • (v a : Fin g → ℂ)) ∈ Λ := fun a => by
    rw [smul_smul, mul_inv_cancel₀ hmc, one_smul]
    exact (v a).2
  choose s hs' using fun a => hrep _ (hmem a)
  refine ⟨_, inferInstance, s, ?_, fun a b hab => ?_⟩
  · rw [Fintype.card_fun, Fintype.card_fin, hcard, pow_mul]
  · have h1 : (m : ℂ)⁻¹ • ((v a : Fin g → ℂ) - (v b : Fin g → ℂ)) ∈ Λ := by
      have := Λ.sub_mem (Λ.add_mem (hs' a) hab) (hs' b)
      convert this using 1
      rw [smul_sub]
      abel
    have h2 : v a - v b = (m : ℤ) • (⟨_, h1⟩ : Λ) := by
      apply Subtype.ext
      have e : ∀ y : Fin g → ℂ, (m : ℤ) • ((m : ℂ)⁻¹ • y) = y := fun y => by
        ext i
        simp [mul_inv_cancel_left₀ hmc]
      simp only [Submodule.coe_sub, Submodule.coe_smul]
      exact (e _).symm
    funext k
    have h3 := congrArg (fun y => b0.repr y k) h2
    simp only [map_sub, map_smul, Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_smul, Pi.smul_apply,
      hv, smul_eq_mul] at h3
    have h4 : ((a k : ℕ) : ℤ) - ((b k : ℕ) : ℤ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd ⟨_, h3⟩ ?_
      have := (a k).2
      have := (b k).2
      rw [abs_lt]
      omega
    exact Fin.ext (by omega)

theorem real_smul_eq (t : ℝ) (z : Fin g → ℂ) : t • z = (t : ℂ) • z := by
  ext i
  simp

theorem card_le_of_unimodular (Λ : Submodule ℤ (Fin g → ℂ)) [hd : DiscreteTopology Λ]
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (χ : Λ → ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    (hint : ∀ l l' : Λ, ∃ k : ℤ, (hh Hm l l').im = k)
    (huni : ∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hh Hm w l).im = k) → w ∈ Λ)
    (n : ℕ) (hn : 1 ≤ n) (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ)
    (hf : ∀ k, Differentiable ℂ (f k) ∧ ∀ (l : Λ) z, f k (z + l) =
      (χ l * cexp (Real.pi * hh Hm z l + Real.pi / 2 * hh Hm l l)) ^ n * f k z)
    (hli : LinearIndependent ℂ f) : N ≤ n ^ g := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ k
    (fun a b c => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, ← hk, ← hk, ← hk, Submodule.coe_add, hh_add_left, add_im]))
    (fun t a c => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, ← hk, ← hk, Submodule.coe_smul,
        show (t • (a : Fin g → ℂ)) = (t : ℂ) • (a : Fin g → ℂ) by ext i; simp, hh_smul_left]
      simp))
    (fun c a b => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, ← hk, ← hk, ← hk, Submodule.coe_add, hh_add_right, add_im]))
    (fun t c a => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, ← hk, ← hk, Submodule.coe_smul,
        show (t • (a : Fin g → ℂ)) = (t : ℂ) • (a : Fin g → ℂ) by ext i; simp, hh_smul_right]
      simp))
  have hE : ∀ l l' : Λ, (Ef l l' : ℝ) = (hh Hm l l').im := fun l l' => (hk l l').symm
  let Bf : (Fin g → ℂ) →ₗ[ℝ] Module.Dual ℝ (Fin g → ℂ) := LinearMap.mk₂ ℝ
    (fun z w => (hh Hm z w).im)
    (fun a b c => by rw [hh_add_left, add_im])
    (fun t a c => by rw [real_smul_eq, hh_smul_left]; simp)
    (fun c a b => by rw [hh_add_right, add_im])
    (fun t c a => by rw [real_smul_eq, hh_smul_right]; simp)
  have hBf : ∀ z w, Bf z w = (hh Hm z w).im := fun _ _ => rfl
  have hinj : Function.Injective Bf := by
    refine (injective_iff_map_eq_zero Bf).2 fun z hz => ?_
    by_contra hne
    have h1 := hpos z hne
    have h2 : Bf z (I • z) = 0 := by rw [hz]; rfl
    rw [hBf, hh_smul_right] at h2
    simp only [star_def, conj_I, neg_mul, neg_im, mul_im, I_re, I_im, zero_mul, one_mul,
      zero_add, neg_eq_zero] at h2
    exact h1.ne' h2
  have hsurj : Function.Surjective Bf :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := Fin g → ℂ)).symm).1 hinj
  have hbij : Function.Bijective Ef := by
    refine ⟨(injective_iff_map_eq_zero Ef).2 fun l hl => ?_, fun φ => ?_⟩
    · apply Subtype.ext
      apply hinj
      rw [ZeroMemClass.coe_zero, map_zero]
      have hall : ∀ l' : Λ, Bf l l' = 0 := fun l' => by
        rw [hBf, ← hE, hl]
        simp
      let b0 := Module.Free.chooseBasis ℤ Λ
      let b := b0.ofZLatticeBasis ℝ Λ
      refine b.ext fun i => ?_
      rw [show b i = (b0 i : Fin g → ℂ) from Module.Basis.ofZLatticeBasis_apply ℝ Λ b0 i]
      exact hall _
    · let b0 := Module.Free.chooseBasis ℤ Λ
      let b := b0.ofZLatticeBasis ℝ Λ
      let Φ : Module.Dual ℝ (Fin g → ℂ) := b.constr ℝ fun i => ((φ (b0 i) : ℤ) : ℝ)
      have hΦ : ∀ l : Λ, Φ l = (φ l : ℝ) := by
        have : ((Φ.restrictScalars ℤ) ∘ₗ Λ.subtype) = (Algebra.linearMap ℤ ℝ) ∘ₗ φ := by
          refine b0.ext fun i => ?_
          have e : (b0 i : Fin g → ℂ) = b i := (Module.Basis.ofZLatticeBasis_apply ℝ Λ b0 i).symm
          simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
            Algebra.linearMap_apply, e]
          simpa [Φ] using b.constr_basis ℝ (fun i => ((φ (b0 i) : ℤ) : ℝ)) i
        intro l
        simpa using LinearMap.congr_fun this l
      obtain ⟨w, hw⟩ := hsurj Φ
      have hwl : ∀ l : Λ, (hh Hm w l).im = (φ l : ℝ) := fun l => by
        rw [← hBf, hw, hΦ]
      refine ⟨⟨w, huni w fun l => ⟨_, hwl l⟩⟩, LinearMap.ext fun l => ?_⟩
      refine Int.cast_injective (α := ℝ) ?_
      rw [hE]
      exact hwl l
  exact GlobalTheory.card_le_pow_of_linearIndependent_theta_principal
    GlobalTheory.SiegelNormalForm.exists_normal_form
    (GlobalTheory.ClassicalTheta.card_le_pow_of_linearIndependent
      GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
      (GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero
        GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic))
    g Λ hd hs Hm χ Ef hH hpos hχ hE hbij n hn N f hf hli

def psi (Hm : Matrix (Fin g) (Fin g) ℂ) (Λ : Submodule ℤ (Fin g → ℂ)) (r : Fin g → ℂ) :
    Multiplicative Λ →* ℂ where
  toFun l := cexp (2 * Real.pi * I * (hh Hm r ((Multiplicative.toAdd l : Λ) : Fin g → ℂ)).im)
  map_one' := by
    have : hh Hm r 0 = 0 := by simp [hh]
    simp [this]
  map_mul' x y := by
    rw [← Complex.exp_add]
    congr 1
    simp only [toAdd_mul, Submodule.coe_add, hh_add_right, add_im]
    push_cast
    ring

theorem linearIndependent_of_law (Λ : Submodule ℤ (Fin g → ℂ))
    (huni : ∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hh Hm w l).im = k) → w ∈ Λ)
    {J : Type} [Fintype J] (ρ : J → Fin g → ℂ) (hρ : ∀ a b, ρ a - ρ b ∈ Λ → a = b)
    (e : J → (Fin g → ℂ) → ℂ) (he : ∀ a, e a ≠ 0) (T : Λ → Fin g → ℂ)
    (A : Λ → (Fin g → ℂ) → ℂ) (hA : ∀ l w, A l w ≠ 0)
    (hlaw : ∀ a l w, e a (w + T l) = A l w * psi Hm Λ (ρ a) (Multiplicative.ofAdd l) * e a w) :
    LinearIndependent ℂ e := by
  classical
  have hinj : Function.Injective fun a => psi Hm Λ (ρ a) := by
    intro a b hab
    refine hρ a b (huni _ fun l => ?_)
    have h1 := DFunLike.congr_fun hab (Multiplicative.ofAdd l)
    simp only [psi, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
    refine ⟨n, ?_⟩
    rw [hh_sub_left, sub_im]
    have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
    have h2 : (((hh Hm (ρ a) l).im - (hh Hm (ρ b) l).im : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      push_cast
      linear_combination hn
    exact_mod_cast h2
  have hind : LinearIndependent ℂ (fun a (l : Multiplicative Λ) => psi Hm Λ (ρ a) l) :=
    (linearIndependent_monoidHom (Multiplicative Λ) ℂ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro c hc a
  obtain ⟨w, hw⟩ : ∃ w, e a w ≠ 0 := by
    by_contra h
    push_neg at h
    exact he a (funext h)
  have key : ∀ w a, c a * e a w = 0 := by
    intro w
    apply hind (fun a => c a * e a w)
    funext l
    have h := congrFun hc (w + T (Multiplicative.toAdd l))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hlaw] at h ⊢
    apply mul_left_cancel₀ (hA (Multiplicative.toAdd l) w)
    rw [mul_zero, ← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [ofAdd_toAdd]
    ring
  exact (mul_eq_zero.1 (key w a)).resolve_right hw

end GlobalTheory.CompanionTheory.ThetaSpan

namespace GlobalTheory.CompanionTheory.ThetaSpan

open Complex Matrix Filter Topology

variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem differentiable_hh_left (v : Fin g → ℂ) : Differentiable ℂ fun w => hh Hm w v := by
  simp only [hh, dotProduct]
  fun_prop

theorem re_hh_expand (hH : Hm.IsHermitian) (r w : Fin g → ℂ) (t : ℕ) :
    (hh Hm (r + (t : ℂ) • w) (r + (t : ℂ) • w)).re =
      (hh Hm r r).re + 2 * t * (hh Hm w r).re + (t : ℝ) ^ 2 * (hh Hm w w).re := by
  have hc : (hh Hm r w).re = (hh Hm w r).re := by
    rw [← hh_conj hH w r]
    simp
  rw [hh_add_left, hh_add_right, hh_add_right, hh_smul_left, hh_smul_left, hh_smul_right,
    hh_smul_right]
  simp only [star_def, conj_natCast, add_re, mul_re, natCast_re, natCast_im, zero_mul, sub_zero,
    hc, mul_im, add_zero]
  ring

def tr (Hm : Matrix (Fin g) (Fin g) ℂ) (m : ℕ) (θ : (Fin g → ℂ) → ℂ) (r w : Fin g → ℂ) : ℂ :=
  θ (r + (m : ℂ) • w) * cexp (-(Real.pi * m * hh Hm w r))

theorem differentiable_tr (m : ℕ) {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ)
    (r : Fin g → ℂ) : Differentiable ℂ (tr Hm m θ r) := by
  have h1 : Differentiable ℂ fun w : Fin g → ℂ => r + (m : ℂ) • w := by fun_prop
  exact (hθ.comp h1).mul
    ((((differentiable_hh_left r).const_mul (Real.pi * (m : ℂ))).neg).cexp)

theorem tr_ne_zero {m : ℕ} (hm : 1 ≤ m) {θ : (Fin g → ℂ) → ℂ} (hθ : θ ≠ 0) (r : Fin g → ℂ) :
    tr Hm m θ r ≠ 0 := by
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  obtain ⟨x, hx⟩ : ∃ x, θ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hθ (funext h)
  intro h
  have h1 := congrFun h ((m : ℂ)⁻¹ • (x - r))
  simp only [tr, Pi.zero_apply] at h1
  rw [smul_smul, mul_inv_cancel₀ hmc, one_smul, add_sub_cancel] at h1
  exact (mul_ne_zero hx (Complex.exp_ne_zero _)) h1

theorem tr_translate (Λ : Submodule ℤ (Fin g → ℂ)) (hH : Hm.IsHermitian) {m : ℕ} (hm : 1 ≤ m)
    {θ : (Fin g → ℂ) → ℂ} (χ : Λ → ℂ)
    (hθ : ∀ (l : Λ) w, θ (w + l) =
      χ l * cexp (Real.pi * hh Hm w l + Real.pi / 2 * hh Hm l l) * θ w)
    (r w : Fin g → ℂ) (l : Λ) :
    tr Hm m θ r (w + (m : ℂ)⁻¹ • (l : Fin g → ℂ)) =
      (χ l * cexp (Real.pi * m * hh Hm w l + Real.pi / 2 * hh Hm l l)) *
        psi Hm Λ r (Multiplicative.ofAdd l) * tr Hm m θ r w := by
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have e1 : r + (m : ℂ) • (w + (m : ℂ)⁻¹ • (l : Fin g → ℂ)) = (r + (m : ℂ) • w) + l := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hmc, one_smul, add_assoc]
  have e2 : hh Hm r l - hh Hm l r = 2 * I * (hh Hm r l).im := by
    rw [← hh_conj hH r l, star_def, Complex.sub_conj]
    push_cast
    ring
  simp only [tr, psi, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [e1, hθ, hh_add_left, hh_add_left, hh_smul_left, hh_smul_left]
  have e3 : cexp (Real.pi * (hh Hm r l + m * hh Hm w l) + Real.pi / 2 * hh Hm l l) *
      cexp (-(Real.pi * m * (hh Hm w r + (m : ℂ)⁻¹ * hh Hm l r))) =
      cexp (Real.pi * m * hh Hm w l + Real.pi / 2 * hh Hm l l) *
        cexp (2 * Real.pi * I * (hh Hm r l).im) * cexp (-(Real.pi * m * hh Hm w r)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have e4 : (m : ℂ) * ((m : ℂ)⁻¹ * hh Hm l r) = hh Hm l r := mul_inv_cancel_left₀ hmc _
    linear_combination (Real.pi : ℂ) * e2 - (Real.pi : ℂ) * e4
  linear_combination (χ l * θ (r + (m : ℂ) • w)) * e3

theorem span_of_reps (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (χ : Λ → ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    (hint : ∀ l l' : Λ, ∃ k : ℤ, (hh Hm l l').im = k)
    (huni : ∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hh Hm w l).im = k) → w ∈ Λ)
    (m : ℕ) (hm : 1 ≤ m) (θ : (Fin g → ℂ) → ℂ) (hθd : Differentiable ℂ θ)
    (hθ : ∀ (l : Λ) w, θ (w + l) =
      χ l * cexp (Real.pi * hh Hm w l + Real.pi / 2 * hh Hm l l) * θ w) (hθ0 : θ ≠ 0)
    {Ix : Type} [Fintype Ix] (r : Ix → Fin g → ℂ) (f : Ix → (Fin g → ℂ) → ℂ)
    (hrep : ∀ w : Fin g → ℂ, (m : ℂ) • w ∈ Λ → ∃ i, w - r i ∈ Λ)
    (hfd : ∀ i, Differentiable ℂ (f i))
    (hnorm : ∀ i w, ‖f i w‖ * Real.exp (-(Real.pi * ((m ^ 2 : ℕ) : ℝ) / 2) * (hh Hm w w).re) =
      ‖θ (r i + (m : ℂ) • w)‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) *
        (hh Hm (r i + (m : ℂ) • w) (r i + (m : ℂ) • w)).re))
    (hfl : ∀ i (l : Λ) z, f i (z + l) =
      (χ l * cexp (Real.pi * hh Hm z l + Real.pi / 2 * hh Hm l l)) ^ (m ^ 2) * f i z)
    (F : (Fin g → ℂ) → ℂ) (hFd : Differentiable ℂ F)
    (hFl : ∀ (l : Λ) z, F (z + l) =
      (χ l * cexp (Real.pi * hh Hm z l + Real.pi / 2 * hh Hm l l)) ^ (m ^ 2) * F z) :
    ∃ c : Ix → ℂ, F = ∑ i, c i • f i := by
  have hprop : ∀ i, ∃ c : ℂ, c ≠ 0 ∧ f i = c • tr Hm m θ (r i) := fun i => by
    refine exists_eq_const_mul (hfd i) (differentiable_tr m hθd _)
      (Real.exp (-(Real.pi / 2) * (hh Hm (r i) (r i)).re)) (Real.exp_pos _) (fun w => ?_)
      (tr_ne_zero hm hθ0 _)
    have h := hnorm i w
    rw [re_hh_expand hH] at h
    have hX : ‖f i w‖ = ‖θ (r i + (m : ℂ) • w)‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) *
        ((hh Hm (r i) (r i)).re + 2 * m * (hh Hm w (r i)).re + (m : ℝ) ^ 2 * (hh Hm w w).re)) *
        Real.exp ((Real.pi * ((m ^ 2 : ℕ) : ℝ) / 2) * (hh Hm w w).re) := by
      rw [← h, mul_assoc, ← Real.exp_add]
      simp
    have hN : ‖tr Hm m θ (r i) w‖ = ‖θ (r i + (m : ℂ) • w)‖ *
        Real.exp (-(Real.pi * m * (hh Hm w (r i)).re)) := by
      simp only [tr]
      rw [norm_mul, Complex.norm_exp]
      congr 2
      simp
    rw [hX, hN, mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
    congr 2
    push_cast
    ring
  choose c hc0 hfe using hprop
  have hχ0 : ∀ l, χ l ≠ 0 := fun l h => by
    have := hχ l
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨J, _, s, hcard, hinj⟩ := exists_reps Λ hs m hm r hrep
  have hli : LinearIndependent ℂ (fun a => f (s a)) := by
    refine linearIndependent_of_law Λ huni (fun a => r (s a)) hinj _ (fun a => ?_)
      (fun l => (m : ℂ)⁻¹ • (l : Fin g → ℂ))
      (fun l w => χ l * cexp (Real.pi * m * hh Hm w l + Real.pi / 2 * hh Hm l l))
      (fun l w => mul_ne_zero (hχ0 l) (Complex.exp_ne_zero _)) (fun a l w => ?_)
    · rw [hfe]
      exact smul_ne_zero (hc0 _) (tr_ne_zero hm hθ0 _)
    · simp only [hfe, Pi.smul_apply, smul_eq_mul]
      rw [tr_translate Λ hH hm χ hθ]
      ring
  have hsp : F ∈ Submodule.span ℂ (Set.range fun a => f (s a)) := by
    by_contra hF
    let eqv := Fintype.equivFin J
    have h1 : LinearIndependent ℂ (fun k => f (s (eqv.symm k))) :=
      hli.comp _ eqv.symm.injective
    have h2 : F ∉ Submodule.span ℂ (Set.range fun k => f (s (eqv.symm k))) := by
      rwa [show (Set.range fun k => f (s (eqv.symm k))) = Set.range fun a => f (s a) from
        eqv.symm.surjective.range_comp fun a => f (s a)]
    have h3 := linearIndependent_fin_cons.2 ⟨h1, h2⟩
    have h4 := card_le_of_unimodular Λ hs hH hpos χ hχ hint huni (m ^ 2) (Nat.one_le_pow _ _ hm)
      (Fintype.card J + 1) _ (fun k => by
        refine Fin.cases ?_ (fun j => ?_) k
        · simp only [Fin.cons_zero]
          exact ⟨hFd, hFl⟩
        · simp only [Fin.cons_succ]
          exact ⟨hfd _, hfl _⟩) h3
    omega
  have hsp' : F ∈ Submodule.span ℂ (Set.range f) :=
    Submodule.span_mono (Set.range_comp_subset_range s f) hsp
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hsp'
  exact ⟨d, hd.symm⟩

end GlobalTheory.CompanionTheory.ThetaSpan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.ThetaSpan

section Frame

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}

theorem continuous_nrm (a : ArchFrame P z g) (n : ℕ) {θ : (Fin g → ℂ) → ℂ} (hθ : Continuous θ) :
    Continuous (a.nrm n θ) := by
  have h : Continuous fun w : Fin g → ℂ =>
      ‖θ w‖ * Real.exp (-(Real.pi * n / 2) * (hh a.Hm w w).re) :=
    hθ.norm.mul (Real.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_re.comp continuous_hh_diag)))
  exact h

end Frame

theorem theta_span : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g), (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → ∀ (m : ℕ) (θ : (Fin g → ℂ) → ℂ) (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ) (f : Ix → (Fin g → ℂ) → ℂ), 1 ≤ m → a.IsTheta 1 θ → θ ≠ 0 → (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ a.u.Λ → ∃ i, w - r i ∈ a.u.Λ) → (∀ i, (m : ℂ) • r i ∈ a.u.Λ) → (∀ i, a.IsTheta (m ^ 2) (f i)) → (∀ i (w : Fin g → ℂ) (N : ℕ), 1 ≤ N → (N : ℂ) • w ∈ a.u.Λ → a.nrm (m ^ 2) (f i) w = a.nrm 1 θ (r i + (m : ℂ) • w)) → (∀ i w, a.nrm (m ^ 2) (f i) w = a.nrm 1 θ (r i + (m : ℂ) • w)) ∧ ∀ F, a.IsTheta (m ^ 2) F → ∃ c : Ix → ℂ, F = ∑ i, c i • f i := by
  intro S G _ _ P z g a hint huni _ m θ Ix _ r f hm hθ hθ0 hrep _ hf hnorm
  obtain ⟨hH, hpos, hχ, -⟩ := a.ah
  haveI := a.u.discrete
  have hs := a.u.full
  have hall : ∀ i w, a.nrm (m ^ 2) (f i) w = a.nrm 1 θ (r i + (m : ℂ) • w) := by
    intro i
    have hl : Continuous fun w : Fin g → ℂ => r i + (m : ℂ) • w := by fun_prop
    have := Continuous.ext_on (dense_torsion a.u.Λ hs)
      (continuous_nrm a (m ^ 2) (hf i).1.continuous)
      ((continuous_nrm a 1 hθ.1.continuous).comp hl)
      (fun w hw => by
        obtain ⟨N, hN, hw⟩ := hw
        exact hnorm i w N hN hw)
    exact congrFun this
  refine ⟨hall, fun F hF => ?_⟩
  exact span_of_reps a.u.Λ hs hH hpos a.χ hχ hint huni m hm θ hθ.1
    (fun l w => by
      have := hθ.2 l w
      rwa [pow_one] at this)
    hθ0 r f hrep (fun i => (hf i).1) (fun i w => hall i w) (fun i => (hf i).2) F hF.1 hF.2

end GlobalTheory.CompanionTheory.ThetaSpan
