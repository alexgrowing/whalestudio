import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem form_of_classSums {B X W I κ HV HW : Type} [MeasurableSpace B] [MeasurableSpace X] [Fintype I] [Fintype κ]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup HV] [InnerProductSpace ℂ HV] [FiniteDimensional ℂ HV]
    [NormedAddCommGroup HW] [InnerProductSpace ℂ HW] [FiniteDimensional ℂ HW]
    (ν : Measure B) (𝓕 : Set B) (μ : Measure X) (𝓖 : Set X) (k : B → X → W → ℂ) (s : I → B) (wt : I → ℂ) (ev : HV → I → W)
    (F : HW → X → ℂ) (N : ℝ) (th : HV →ₗ[ℂ] HW) (Ψ : HW → B → W) (b : OrthonormalBasis κ ℂ W)
    (hV : ∀ x x', inner ℂ x x' = ∑ j, wt j * inner ℂ (ev x j) (ev x' j))
    (hW : ∀ U U', inner ℂ U U' = (N : ℂ) * l2 μ 𝓖 (F U') (F U))
    (hth : ∀ x g, F (th x) g = ∑ j, wt j * k (s j) g (ev x j))
    (hint : ∀ U w h, IntegrableOn (fun g => k h g w * starRingEnd ℂ (F U g)) 𝓖 μ)
    (hΨ : ∀ U h w, inner ℂ (Ψ U h) w = l2 μ 𝓖 (fun g => k h g w) (F U))
    (hex : ∀ U, ∃ a, ∀ j, ev a j = (N : ℂ) • Ψ U (s j)) (U₁ U₂ : HW)
    (hsum : ∫ h in 𝓕, inner ℂ (Ψ U₁ h) (Ψ U₂ h) ∂ν = ∑ j, wt j * inner ℂ (Ψ U₁ (s j)) (Ψ U₂ (s j)))
    (hi : ∀ a, IntegrableOn (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁) *
      starRingEnd ℂ (l2 μ 𝓖 (fun g => k h g (b a)) (F U₂))) 𝓕 ν) :
    inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) = (N : ℂ) ^ 2 *
      ∑ a, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁)) (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₂)) := by
  have h1 : ∀ U j, ev (LinearMap.adjoint th U) j = (N : ℂ) • Ψ U (s j) := fun U => by
    obtain ⟨a, ha⟩ := hex U
    have : LinearMap.adjoint th U = a := by
      refine ext_inner_right ℂ fun x => ?_
      rw [LinearMap.adjoint_inner_left, hW, hV, l2_sum_eq_sum_norm_sq_of_orthogonal μ 𝓖 wt (fun j g => k (s j) g (ev x j)) _ _ (hth x) fun j => hint U _ _,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ha, inner_smul_left, Complex.conj_ofReal, hΨ, mul_left_comm]
    rwa [this]
  have e2 : ∑ a, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁)) (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₂)) =
      ∫ h in 𝓕, inner ℂ (Ψ U₁ h) (Ψ U₂ h) ∂ν := by
    refine (integral_finsetSum _ fun a _ => hi a).symm.trans ?_
    congr 1
    funext h
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hΨ, ← hΨ, inner_conj_symm]
  rw [e2, hsum, hV, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h1, h1, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

theorem inner_law {B W : Type} [Group B] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : B →* Module.End ℂ W)
    (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) {z : ℂ} (hz : ‖z‖ = 1) (k : B) (a b : W) :
    inner ℂ (z • ρ k a) (z • ρ k b) = inner ℂ a b := by
  rw [inner_smul_left, inner_smul_right, hρ, ← mul_assoc, Complex.conj_mul', hz]
  simp

section Adjoint

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (Datum.WO V W → ℂ)} (hω : Datum.IsWeilDatumO ψ V W χS χT ω)
  (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
  (φ : c.W →ₗ[ℂ] (Datum.WO V W → ℂ)) (hφ : ∀ w, Datum.IsThetaFunO ψ V W (φ w))
  (hinf : ∀ u ∈ GinfC V, ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w))
  (hlev : ∀ κ ∈ Lev.levA V (lev D.sp.cm V.gram β L), ∀ w, ω (κ, 1) (φ w) = (Lev.levChi V β L κ)⁻¹ • φ w)
  {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)} (HW : HMod (MMap M)) {N : ℝ}
  (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y))

include hW in
theorem pet_eq (y y' : HW.H) (v w : M.Vec) :
    l2 μ 𝓖 (HW.e y' w) (HW.e y v) = ipM M μ 𝓖 (HW.e y) (HW.e y') * ∏ τ, ⟪(v τ : M.H τ), (w τ : M.H τ)⟫_ℂ := by
  rw [← (isMultiplicityInner_of_model HW hW y y' v w).2, l2_eq_star]

include hW in
theorem inner_eq_pet (y y' : HW.H) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) :
    inner ℂ y y' = (N : ℂ) * l2 μ 𝓖 (HW.e y' v) (HW.e y v) := by
  rw [pet_eq HW hW, hW, Finset.prod_eq_one, mul_one]
  intro τ _
  rw [inner_self_eq_norm_sq_to_K, hv]
  simp

variable {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V (lev D.sp.cm V.gram β L) ν 𝓕)
  {I : Type} [Fintype I] {y : I → Bridge.Gf V} (hy : Bridge.IsReps (Bridge.ratF V) (grpOf V β L) y)
  (HV : HMod (Bridge.Gf V → c.W))
  (hV : HV.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L))
    (Bridge.adInner (Bridge.ratF V) (grpOf V β L) y))
  (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (th : HV.H →ₗ[ℂ] HW.H)
  (hth : ∀ x g, HW.e (th x) v g = ∫ h in 𝓕, Datum.thetaKO ω h g (φ (c.ext (HV.e x) h)) ∂ν)
  (hint : ∀ (U : HW.H) w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) * starRingEnd ℂ (HW.e U v g)) 𝓖 μ)

include hc in
theorem upVec_mem (Ψ : GA D V → c.W) (h2 : ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
      Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) :
    (fun u => Ψ (finLift V u)) ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L) :=
  mem_adForms (finHom V).rangeRestrict (GQ V) c.ρ (finLift V) (finLift_spec V) (fun u => hc.1 _ (finLift_mem V u)) Ψ
      fun γ hγ k hk x => h2 γ hγ k ((mem_grpOf V β L k).1 hk) x

include hω hc hφ hinf hlev hW hν hy hV hv hth hint in

theorem form_eq_sum (U₁ U₂ : HW.H) {κ : Type} [Fintype κ] (b : OrthonormalBasis κ ℂ c.W)
    (hi : ∀ k, IntegrableOn (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₁ v) *
      starRingEnd ℂ (l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₂ v))) 𝓕 ν) :
    inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) = (N : ℂ) ^ 2 *
      ∑ k, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₁ v))
        (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₂ v)) := by
  have h0 := fun U => exists_upVec hω c hc β L φ hφ hinf hlev μ 𝓖 (HW.e U v) (hint U)
  have h1 := fun U => (h0 U).choose_spec.1
  have h2 := fun U => (h0 U).choose_spec.2
  refine form_of_classSums ν 𝓕 μ 𝓖 (fun h g w => Datum.thetaKO ω h g (φ w)) (fun j => finLift V (y j))
    (fun j => ((Nat.card (Bridge.stab (Bridge.ratF V) (grpOf V β L) (y j)) : ℂ))⁻¹) (fun x j => HV.e x (y j))
    (fun U => HW.e U v) N th (fun U => (h0 U).choose) b hV.2.2 (fun U U' => inner_eq_pet HW hW U U' v hv)
    (fun x g => ?_) hint h1 (fun U => ?_) U₁ U₂ ?_ hi
  · exact (hth x g).trans (theta_classSum hω c hc β L φ hφ hinf hlev hν hy (HMod_mem hV x) g)
  · exact (HMod_onto hV (Submodule.smul_mem _ (N : ℂ) (upVec_mem c hc β L _ (h2 U)))).imp fun a ha j => congrFun ha (y j)
  · refine integral_eq_classSum V β L hν hy _ fun γ hγ k hk x => ?_
    exact (congrArg₂ (inner ℂ) (h2 U₁ γ hγ k hk x) (h2 U₂ γ hγ k hk x)).trans
      (inner_law c.ρ hc.2.1 (norm_levChi β L k) _ _ _)

end Adjoint

theorem numeric_bound {ι : Type} [Fintype ι] (f n r : ℕ) (hcard : Fintype.card ι = f) (L' dmax mass dim idx nrm E dO dS : ℝ)
    (H dk J deg : ι → ℝ) (h8 : 8 ≤ n) (h2 : 2 * r ≤ n) (h1 : 1 ≤ r) (hf : 1 ≤ f) (hL : (5.5 : ℝ) ≤ L') (hn : Real.log n ≤ L')
    (hd0 : 0 ≤ dmax) (hd : Real.log (dmax + 2) ≤ 2 * L') (hm : 1 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≤ mass) (hdim : 1 ≤ dim)
    (hidx : idx * nrm = dS⁻¹) (hE : Real.exp (-(r * (2 * f))) ≤ E) (hO : 0 < dO ∧ dO ≤ Real.exp (2 * (r * (2 * f))))
    (hS : 0 < dS ∧ dS ≤ Real.exp (2 * (r * (2 * f)))) (hH : ∀ ρ, 0 < H ρ) (hk : ∀ ρ, 1 ≤ dk ρ) (hJ : ∀ ρ, 0 < J ρ)
    (hdeg : ∀ ρ, 0 ≤ deg ρ ∧ deg ρ ≤ dmax)
    (hJb : ∀ ρ, Real.log (J ρ)⁻¹ ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (deg ρ + 2))) :
    0 < (∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E ∧
      ∑ ρ, Real.log (H ρ) - 8 * f * (n : ℝ) ^ 2 * L' ≤
        Real.log ((∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E) := by
  obtain ⟨e⟩ : Nonempty (Fin f ≃ ι) := ⟨(Fintype.equivFinOfCardEq hcard).symm⟩
  have hm0 : 0 < mass := lt_of_lt_of_le (by positivity) hm
  have hE0 : 0 < E := lt_of_lt_of_le (Real.exp_pos _) hE
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast h1
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast h8
  have hrn : 2 * (r : ℝ) ≤ n := by exact_mod_cast h2
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hs : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have key := GlobalTheory.lamLow_numerical_end f n r L' dmax (mass * dim) 1 _ (fun a => H (e a)) (fun _ => 1) (fun a => dk (e a))
    (fun a => (J (e a))⁻¹) h8 h2 h1 hf hL hn hd0 hd (hm.trans (le_mul_of_one_le_right hm0.le hdim)) one_pos
    (by rw [Real.log_one, abs_zero]; positivity)
    (fun a => ⟨hH _, le_rfl, hk _, inv_pos.2 (hJ _), (hJb _).trans (by
      have := (hdeg (e a)).1
      have := (hdeg (e a)).2
      gcongr
      linarith)⟩) rfl
  rw [e.sum_comp fun ρ => Real.log (H ρ), e.prod_comp fun ρ => H ρ * 1 * dk ρ / (J ρ)⁻¹] at key
  have hP : 0 < mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹ := by
    refine mul_pos (by positivity) (Finset.prod_pos fun ρ _ => ?_)
    have := hH ρ; have := hk ρ; have := hJ ρ
    positivity
  have e1 : (∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E =
      (mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹) * (E / (dO * dS)) := by
    simp only [div_inv_eq_mul, mul_one, Finset.prod_mul_distrib]
    have : idx * nrm * dS = 1 := by rw [hidx, inv_mul_cancel₀ hS.1.ne']
    have h3 := hO.1.ne'
    have h4 := hS.1.ne'
    field_simp
    linear_combination ((∏ ρ, dk ρ) * (∏ ρ, H ρ) * (∏ ρ, J ρ)) * this
  have hq : 0 < E / (dO * dS) := div_pos hE0 (mul_pos hO.1 hS.1)
  rw [e1]
  refine ⟨mul_pos hP hq, ?_⟩
  rw [Real.log_mul hP.ne' hq.ne', Real.log_div hE0.ne' (mul_pos hO.1 hS.1).ne', Real.log_mul hO.1.ne' hS.1.ne']
  have a1 := (Real.le_log_iff_exp_le hE0).2 hE
  have a2 := (Real.log_le_iff_le_exp hO.1).2 hO.2
  have a3 := (Real.log_le_iff_le_exp hS.1).2 hS.2
  have a4 : 10 * ((r : ℝ) * f) ≤ 6 * (f * (n : ℝ) ^ 2 * L') := by
    have b1 : (r : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have b2 : (r : ℝ) * f ≤ f * (n : ℝ) ^ 2 := by nlinarith
    have b3 : 0 ≤ f * (n : ℝ) ^ 2 := by positivity
    nlinarith
  linarith

theorem tsum_eval {Y : Type} (Z kf p : Y → ℂ) (C s : ℂ) (h1 : ∀ y, Z y = C * kf y * starRingEnd ℂ (p y))
    (h2 : HasSum (fun y => kf y * starRingEnd ℂ (p y)) s) : ∑' y, Z y = C * s := by
  simp only [h1, mul_assoc]
  exact (h2.mul_left C).tsum_eq

theorem integral_pi_eval {ι : Type} [Fintype ι] {X : ι → Type} [∀ ρ, MeasurableSpace (X ρ)] (m : ∀ ρ, Measure (X ρ))
    [∀ ρ, SigmaFinite (m ρ)] (a : ∀ ρ, X ρ → ℂ) (Φ : (∀ ρ, X ρ) → ℂ) (c0 z q : ℂ)
    (h : ∀ b, Φ b = c0 * (∏ ρ, a ρ (b ρ)) * 1 * (z * starRingEnd ℂ (q * ∏ ρ, a ρ (b ρ)))) :
    ∫ b, Φ b ∂(Measure.pi m) = c0 * z * starRingEnd ℂ q * ((∏ ρ, ∫ x, ‖a ρ x‖ ^ 2 ∂(m ρ) : ℝ) : ℂ) := by
  have e : ∀ b, Φ b = c0 * z * starRingEnd ℂ q * ((∏ ρ, ‖a ρ (b ρ)‖ ^ 2 : ℝ) : ℂ) := fun b => by
    have : ((∏ ρ, ‖a ρ (b ρ)‖ ^ 2 : ℝ) : ℂ) = (∏ ρ, a ρ (b ρ)) * starRingEnd ℂ (∏ ρ, a ρ (b ρ)) := by
      rw [Complex.mul_conj', norm_prod]
      push_cast
      rw [Finset.prod_pow]
    rw [h, this, map_mul]
    ring
  simp only [e]
  rw [integral_const_mul, integral_complex_ofReal, integral_fintype_prod_eq_prod fun ρ x => ‖a ρ x‖ ^ 2]

theorem realMat_mem (i : Fin D.R.m) {Fr : Frames (Wc D i)} (hFr : IsFrames (Wc D i) Fr) (ρ : D.what₂.Tau) (b : Upq (Wc D i) ρ) :
    realMat (Wc D i) Fr ρ b ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ) := by
  refine GlobalTheory.AdelicScalar.conjFrame_mem_UH _ _ _ ((sig_add i ρ).trans (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).symm) _ _ (hFr ρ) ?_ b
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact ((map_ne_zero _).2 (GlobalTheory.DefiniteQuotient.gram_hermND (Wc D i)).2).isUnit

theorem rTr_mul (W : HSp D) (a b : GA D W) (F : GA D W → ℂ) : rTr W (a * b) F = rTr W a (rTr W b F) := by
  funext h
  simp only [rTr, mul_assoc]

theorem coef_translate {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)}
    (HW : HMod (MMap M)) {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y)) (θ : Datum.InfFam D)
    {J : Set (GA D W)} {χ : GA D W → ℂ} (U₁ U₂ : HW.H) (hU : HW.e U₁ ∈ Mult θ M J χ)
    (g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (hg : ∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ)) (v : M.Vec) :
    ∃ w : M.Vec, rTr W (realElt θ W g) (HW.e U₁ v) = HW.e U₁ w ∧
      l2 μ 𝓖 (HW.e U₁ w) (HW.e U₂ v) =
        ipM M μ 𝓖 (HW.e U₂) (HW.e U₁) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (g τ) (v τ : M.H τ)⟫_ℂ :=
  ⟨fun ρ => ⟨_, rep_mem_sm M ρ (g ρ) (hg ρ) _ (v ρ).2⟩,
    (GlobalTheory.RealEquiv.mult_realElt D W S θ M J χ _ hU g hg v _ fun _ => rfl).symm, pet_eq HW hW U₂ U₁ v _⟩

theorem eq_of_value {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)}
    (HW : HMod (MMap M)) {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y)) (U₁ U₂ : HW.H) :
    inner ℂ U₁ U₂ = (N : ℂ) * starRingEnd ℂ (ipM M μ 𝓖 (HW.e U₂) (HW.e U₁)) := by
  rw [← inner_conj_symm, hW, map_mul, Complex.conj_ofReal]

end GlobalTheory.AdelicScalar

end
