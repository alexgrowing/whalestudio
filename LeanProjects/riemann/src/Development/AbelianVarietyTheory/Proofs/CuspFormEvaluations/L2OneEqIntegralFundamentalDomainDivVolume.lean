import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2Norm
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThetaPT

open MeasureTheory

theorem Hf_add_smul_left {κ : Type} [Fintype κ] (c : ℂ) (v w u : EuclideanSpace ℂ κ) :
    I2.Hf (v + c • w) u = I2.Hf v u + c * I2.Hf w u := by
  unfold I2.Hf
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem Hf_neg_right {κ : Type} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    I2.Hf v (-w) = -I2.Hf v w := by
  unfold I2.Hf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem Hf_neg_left {κ : Type} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    I2.Hf (-v) w = -I2.Hf v w := by
  unfold I2.Hf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem cexp_pi_int (k : ℤ) : cexp (Real.pi * I * (k : ℂ)) = ((Real.cos (Real.pi * k) : ℝ) : ℂ) := by
  have h : (Real.pi : ℂ) * I * (k : ℂ) = ((Real.pi * k : ℝ) : ℂ) * I := by push_cast; ring
  have hs : Real.sin (Real.pi * k) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi k
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hs]
  simp

theorem l2_one_eq_integral_fundamentalDomain_div_volume {E : Type} [Field E] [NumberField E] {g : ℕ} (T : I2.PT E)
    (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (θ : (Fin g → ℂ) → ℂ)
    (hs : (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1)
    (A : AddSubgroup (Fin g → ℂ)) (hL : ∀ z, z ∈ A ↔ ψ z ∈ T.L) (Fd : Set (Fin g → ℂ))
    (hFd : IsAddFundamentalDomain A Fd volume) :
    T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) =
      (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re)) / (volume Fd).toReal := by
  classical

  have hper : ∀ (a : A) (z : Fin g → ℂ),
      ‖θ (a +ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ (a +ᵥ z)) (ψ (a +ᵥ z))).re) =
        ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re) := by
    intro a z
    have ha : ψ a ∈ T.L := (hL a).1 a.2
    obtain ⟨-, hq⟩ := hs
    have h := hq (fun _ => ψ a) (fun _ => ha) (fun _ => ψ z)
    simp only [Pi.add_apply, I2.HC, Fin.sum_univ_one, Fin.prod_univ_one, pow_one, Nat.cast_one,
      _root_.one_mul, map_add, LinearEquiv.symm_apply_apply] at h
    have hε : ‖((T.eps (ψ a) : ℤ) : ℂ)‖ = 1 := by
      rcases T.eps_pm _ ha with h1 | h1 <;> simp [h1]
    have hv : (a +ᵥ z : Fin g → ℂ) = z + a := by
      change (a : Fin g → ℂ) + z = z + a
      exact add_comm _ _
    have hre : ((Real.pi : ℂ) * I2.Hf (ψ z) (ψ a) + (Real.pi : ℂ) * I2.Hf (ψ a) (ψ a) / 2).re =
        Real.pi * (I2.Hf (ψ z) (ψ a)).re + Real.pi * (I2.Hf (ψ a) (ψ a)).re / 2 := by
      simp [Complex.add_re, Complex.div_ofNat_re]
    rw [hv, h, map_add, GlobalTheory.EtaAn.ThetaTorus.Hf_add_re, norm_mul, norm_mul, hε, _root_.one_mul,
      Complex.norm_exp, hre, mul_pow, sq (Real.exp _), ← Real.exp_add,
      mul_comm (Real.exp _) (‖θ z‖ ^ 2), _root_.mul_assoc, ← Real.exp_add]
    congr 2
    ring

  let ψR : (Fin g → ℂ) ≃L[ℝ] I2.Vsp T.dim := (ψ.restrictScalars ℝ).toContinuousLinearEquiv
  have hψR : ∀ z, ψR z = ψ z := fun z => rfl
  let eR : (Fin g → ℂ) ≃L[ℝ] (Fin 1 → I2.Vsp T.dim) :=
    ψR.trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (I2.Vsp T.dim)).symm
  have heR : ∀ z, eR z = fun _ => ψ z := fun z => rfl

  have hl2 : T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) =
      ⨍ z in ψ ⁻¹' ZSpan.fundamentalDomain T.b,
        ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re) := by
    have hset : eR ⁻¹' T.fd 1 = ψ ⁻¹' ZSpan.fundamentalDomain T.b := by
      ext z
      simp [I2.PT.fd, heR]
    unfold I2.PT.l2
    rw [GlobalTheory.EtaAn.ThetaTorus.setAverage_equiv volume volume eR, hset]
    congr 1
    funext z
    simp [I2.PT.ptN2, I2.HC, heR]

  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving ψR volume volume :=
    ⟨ψR.continuous.measurable, MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩

  have hfd0 : IsAddFundamentalDomain A (ψ ⁻¹' ZSpan.fundamentalDomain T.b) volume := by
    have h0 := ZSpan.isAddFundamentalDomain T.b (volume : Measure (I2.Vsp T.dim))
    refine h0.preimage_of_equiv hqmp
      (e := fun y => (⟨ψ.symm y, (hL _).2 (by simp only [LinearEquiv.apply_symm_apply]; exact y.2)⟩ : A)) ⟨?_, ?_⟩ ?_
    · intro y y' hyy
      have := congrArg Subtype.val hyy
      exact Subtype.ext (ψ.symm.injective this)
    · intro a
      refine ⟨⟨ψ a, (hL a).1 a.2⟩, ?_⟩
      ext1
      simp
    · intro y z
      change ψ (ψ.symm (y : I2.Vsp T.dim) + z) = (y : I2.Vsp T.dim) + ψ z
      simp
  have hcA : Countable A := by
    have : Countable (Submodule.span ℤ (Set.range T.b)) := inferInstance
    refine Function.Injective.countable
      (f := fun a : A => (⟨ψ a, (hL a).1 a.2⟩ : Submodule.span ℤ (Set.range T.b))) ?_
    intro a a' h
    exact Subtype.ext (ψ.injective (congrArg Subtype.val h))
  rw [hl2, MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def, hfd0.measure_eq hFd,
    hfd0.setIntegral_eq hFd hper, smul_eq_mul, div_eq_inv_mul]

theorem theta_on_torus :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (w : 𝓞 E) (L : Lt E r) (x : Frame X.Ψ r) (t : ℝ) (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (e : Fin g ≃ I2.Idx T.dim), IsSympl X bas → x ∈ X.dom → (w : E) + cc (w : E) = 1 → (T.r = r ∧ (∀ z z', I2.Hf (ψ z) (ψ z') = hx X bas idx x z z') ∧ (∀ ga, ga ∈ T.L ↔ ∃ u ∈ L, ga = ψ (pv X idx x u)) ∧ (∀ (a : 𝓞 E) u, ψ (pv X idx x ((a : E) • u)) = I2.act a (ψ (pv X idx x u))) ∧ (∀ ga ∈ T.L, (T.eps ga : ℝ) = Real.cos (Real.pi * (I2.Hf ga (I2.act w ga)).im)) ∧ (∀ j, (e j).1 = rowType X (idx j) ∧ ψ (Pi.single j 1) = ((Real.sqrt t : ℝ) : ℂ) • EuclideanSpace.single (e j) (1 : ℂ))) → (∀ θ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx (w : E) x L θ → (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1 ∧ (MeanOne X bas idx x L θ → T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) = 1)) ∧ (∀ (n k : ℕ) (th : Fin n → (Fin g → ℂ) → ℂ) (a z : Fin n → Fin g → ℂ), ∏ b, fock X bas idx x k (a b) (th b) (z b) = T.U k (fun b => -ψ (a b)) (fun v => ∏ b, th b (ψ.symm (v b))) (fun b => ψ (z b))) ∧ ∀ u ∈ L, eps1 X (w : E) u = (T.eps (ψ (pv X idx x u)) : ℂ) := by
  intro E _ _ _ r X g bas idx w L x t T ψ e hsy hxd hw hT
  obtain ⟨-, hH, hL, hact, heps, -⟩ := hT
  have hlaws := hx_laws E r X g bas idx 0 hsy ⟨0, rfl⟩ x hxd
  have hpvL : ∀ u ∈ L, ψ (pv X idx x u) ∈ T.L := fun u hu => (hL _).2 ⟨u, hu, rfl⟩

  have hsign : ∀ u ∈ L, eps1 X (w : E) u = (T.eps (ψ (pv X idx x u)) : ℂ) := by
    intro u hu
    have hmem := hpvL u hu
    obtain ⟨k, hk⟩ := T.integral _ _ hmem (T.stable w _ hmem)
    have him : (I2.Hf (ψ (pv X idx x u)) (I2.act w (ψ (pv X idx x u)))).im =
        (EF X u ((w : E) • u) : ℝ) := by
      rw [← hact, hH]
      exact hlaws.2.2.1 u _
    have hq : ((EF X u ((w : E) • u) : ℚ) : ℂ) = (k : ℂ) := by
      have h1 : ((EF X u ((w : E) • u) : ℚ) : ℝ) = (k : ℝ) := by rw [← him, hk]
      have h2 := congrArg (fun s : ℝ => (s : ℂ)) h1
      push_cast at h2
      exact h2
    have hs1 : ((T.eps (ψ (pv X idx x u)) : ℤ) : ℂ) = ((Real.cos (Real.pi * k) : ℝ) : ℂ) := by
      have h1 := heps _ hmem
      rw [hk] at h1
      rw [← h1]
      norm_cast
    unfold eps1
    rw [hq, cexp_pi_int, hs1]

  have hHadd : ∀ z a : Fin g → ℂ, hx X bas idx x (z + (1 / 2 : ℂ) • a) a =
      I2.Hf (ψ z) (ψ a) + I2.Hf (ψ a) (ψ a) / 2 := by
    intro z a
    rw [← hH, map_add, map_smul, Hf_add_smul_left]
    ring
  have hHadd' : ∀ z a : Fin g → ℂ, hx X bas idx x (z + (1 / 2 : ℂ) • a) a =
      hx X bas idx x z a + hx X bas idx x a a / 2 := by
    intro z a
    rw [hHadd, hH, hH]

  have hthper : ∀ θ, IsTheta1 X bas idx (w : E) x L θ → ∀ u ∈ L, ∀ z,
      θ (z + pv X idx x u) = (T.eps (ψ (pv X idx x u)) : ℂ) *
        cexp (Real.pi * I2.Hf (ψ z) (ψ (pv X idx x u)) +
          Real.pi * I2.Hf (ψ (pv X idx x u)) (ψ (pv X idx x u)) / 2) * θ z := by
    intro θ hθ u hu z
    obtain ⟨-, hθp⟩ := hθ
    have h := congrFun (hθp u hu) z
    simp only [Pi.smul_apply, smul_eq_mul, fock, hHadd, hsign u hu, Nat.cast_one, _root_.one_mul] at h
    set ε : ℂ := ((T.eps (ψ (pv X idx x u)) : ℤ) : ℂ) with hεdef
    set P := I2.Hf (ψ z) (ψ (pv X idx x u))
    set Q := I2.Hf (ψ (pv X idx x u)) (ψ (pv X idx x u))
    have hε : ε * ε = 1 := by
      rcases T.eps_pm _ (hpvL u hu) with h1 | h1 <;> simp [hεdef, h1]
    have hc : cexp (Real.pi * P + Real.pi * Q / 2) * cexp (-(Real.pi * (P + Q / 2))) = 1 := by
      rw [← Complex.exp_add, show (Real.pi : ℂ) * P + Real.pi * Q / 2 + -(Real.pi * (P + Q / 2)) = 0 by ring,
        Complex.exp_zero]
    rw [← h]
    linear_combination (-(cexp (Real.pi * P + Real.pi * Q / 2) * cexp (-(Real.pi * (P + Q / 2)))) *
      θ (z + pv X idx x u)) * hε - θ (z + pv X idx x u) * hc

  have hsec : ∀ θ, IsTheta1 X bas idx (w : E) x L θ →
      (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1 := by
    intro θ hθ
    show Differentiable ℂ (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∧ _
    refine ⟨?_, ?_⟩
    · have hd : Differentiable ℂ (fun y : I2.Vsp T.dim => ψ.symm y) := by
        simpa using (LinearMap.toContinuousLinearMap
          (ψ.symm : I2.Vsp T.dim →ₗ[ℂ] (Fin g → ℂ))).differentiable
      obtain ⟨hθd, -⟩ := hθ
      exact hθd.comp (hd.comp (differentiable_apply 0))
    · intro gam hgam v
      obtain ⟨u, hu, hgu⟩ := (hL (gam 0)).1 (hgam 0)
      have h := hthper θ hθ u hu (ψ.symm (v 0))
      simp only [Pi.add_apply, I2.HC, Fin.sum_univ_one, Fin.prod_univ_one, pow_one, Nat.cast_one,
        _root_.one_mul, map_add]
      rw [hgu, LinearEquiv.symm_apply_apply, h, LinearEquiv.apply_symm_apply]
  refine ⟨fun θ hθ => ⟨hsec θ hθ, fun hM => ?_⟩, ?_, hsign⟩
  · obtain ⟨A, Fd, hA, hFd, hmean⟩ := hM
    have hAL : ∀ z, z ∈ A ↔ ψ z ∈ T.L := by
      intro z
      rw [hA z, hL]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, hv, rfl⟩
      · rintro ⟨v, hv, h⟩
        exact ⟨v, hv, ψ.injective h⟩
    rw [l2_one_eq_integral_fundamentalDomain_div_volume T ψ θ (hsec θ hθ) A hAL Fd hFd]
    simpa only [hH] using hmean
  · intro n k th a z
    simp only [fock, I2.PT.U, Pi.sub_apply, sub_neg_eq_add, map_add, LinearEquiv.symm_apply_apply]
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    congr 1
    simp only [I2.HC, Hf_neg_right, Hf_neg_left, neg_neg, hH, hHadd']
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end GlobalTheory.Dict.ThetaPT
