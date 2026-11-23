import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Psi

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem psi_norm (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ‖ψ a‖ = 1 := hψ.1.2.1 a

theorem psi_ne (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have h1 := psi_norm hψ a
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem psi_conj (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : conj (ψ a) = ψ (-a) := by
  have h1 : ψ a * conj (ψ a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, psi_norm hψ a]
    simp
  have h2 : ψ a * ψ (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  exact mul_left_cancel₀ (psi_ne hψ a) (h1.trans h2.symm)

theorem psi_rat (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (ratW T S a) (ratW T S b)) = 1 := by
  obtain ⟨q, hq⟩ := symplO_rat (S := S) (T := T) a b
  rw [hq]
  exact hψ.1.2.2.1 q

theorem psi_cont (hψ : IsStdChar D ψ (-1)) : Continuous ψ := hψ.1.1

end Psi

section Cont

variable (S T : HSp D)

theorem cont_trace : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
  IsModuleTopology.continuous_of_linearMap _

def cAlin (D : D7) : AE D →ₗ[AF D.host.F] AE D where
  toFun := cA D
  map_add' := map_add _
  map_smul' := Formalism.IndefR.PHeisTh.cA_smul

theorem cont_cA : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap (cAlin D)

theorem cont_hO : Continuous fun p : MO S T × MO S T => hO S T p.1 p.2 := by
  have hcA : Continuous (cA D) := cont_cA
  delta hO
  fun_prop

theorem cont_symplO : Continuous fun p : MO S T × MO S T => symplO S T p.1 p.2 := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := cont_trace
  have hh := cont_hO S T
  delta symplO
  first
    | exact ht.comp (continuous_const.mul hh)
    | fun_prop

theorem cont_hO_left (w : MO S T) : Continuous fun z : MO S T => hO S T z w := by
  have h : Continuous (Function.uncurry (hO S T)) := cont_hO S T
  exact h.uncurry_right w

theorem cont_symplO_left (w : MO S T) : Continuous fun z : MO S T => symplO S T z w := by
  have h : Continuous (Function.uncurry (symplO S T)) := cont_symplO S T
  exact h.uncurry_right w

theorem cont_symplOH_left (w : MO S T) : Continuous fun z : MO S T => symplOH S T z w := by
  delta symplOH
  exact continuous_const.mul (cont_symplO_left S T w)

end Cont

section Per

variable (S T : HSp D)

theorem exists_rat_shift (z : MO S T) : ∃ a : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
    ratW T S a + z ∈ Formalism.IndefR.PHeisFC.FD T S := by
  classical
  have hq : ∀ i j k, ∃ q : D.host.F, algebraMap D.host.F (AF D.host.F) q +
      Formalism.IndefR.PHeisFC.Phi T S z i j k ∈ Formalism.IndefR.PHeisFC.F0 D.host.F :=
    fun i j k => (Formalism.IndefR.PHeisFC.ad_exU (F := D.host.F) _).exists
  choose q hq using hq
  have hc : ∀ (e : D.host.E) (k : Fin (Module.finrank D.host.F D.host.E)),
      Formalism.IndefR.PHeisFC.cE D.host.F D.host.E (incA D e) k =
        algebraMap D.host.F (AF D.host.F) ((Module.finBasis D.host.F D.host.E).repr e k) := by
    intro e k
    show (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).repr ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) k = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp
  refine ⟨fun i j => ∑ k, q i j k • Module.finBasis D.host.F D.host.E k, ?_⟩
  intro i j k
  show Formalism.IndefR.PHeisFC.cE D.host.F D.host.E
    (incA D (∑ k', q i j k' • Module.finBasis D.host.F D.host.E k') + z i j) k ∈ _
  rw [map_add, Pi.add_apply, hc, Module.Basis.repr_sum_self]
  exact hq i j k

theorem bdd_of_periodic {E' : Type*} [NormedAddCommGroup E'] (g : MO S T → E') (hg : Continuous g)
    (hp : ∀ a z, ‖g (ratW T S a + z)‖ = ‖g z‖) : ∃ C, ∀ z, ‖g z‖ ≤ C := by
  obtain ⟨K, hK, hFK⟩ := Formalism.IndefR.PHeisFC.FD_sub_compact T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun z => ?_⟩
  obtain ⟨a, ha⟩ := exists_rat_shift S T z
  rw [← hp a z]
  exact hC _ (hFK ha)

theorem measure_FD_lt_top (μ : Measure (MO S T)) (𝓕 : Set (MO S T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) : μ 𝓕 < ⊤ := by
  exact (Formalism.IndefR.PHeisFC.finCovol T S).2 μ 𝓕 hμ h𝓕

theorem integrableOn_of_periodic {E' : Type*} [NormedAddCommGroup E'] [SecondCountableTopology E'] (g : MO S T → E') (hg : Continuous g)
    (hp : ∀ a z, ‖g (ratW T S a + z)‖ = ‖g z‖) (μ : Measure (MO S T)) (𝓕 : Set (MO S T))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) : IntegrableOn g 𝓕 μ := by
  obtain ⟨C, hC⟩ := bdd_of_periodic S T g hg hp
  exact Measure.integrableOn_of_bounded (measure_FD_lt_top S T μ 𝓕 hμ h𝓕).ne
    hg.aestronglyMeasurable (ae_of_all _ hC)

end Per

section Theta

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

theorem norm_theta_shift (hψ : IsStdChar D ψ (-1)) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : MO S T) : ‖f (ratW T S a + z)‖ = ‖f z‖ := by
  rw [hf.1 a z, norm_mul, psi_norm hψ, one_mul]

theorem norm_heis_shift (hψ : IsStdChar D ψ (-1)) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (v : MO S T)
    (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : MO S T) :
    ‖heisO ψ S T v f (ratW T S a + z)‖ = ‖heisO ψ S T v f z‖ := by
  show ‖ψ (symplOH S T (ratW T S a + z) v) * f (ratW T S a + z + v)‖ = ‖ψ (symplOH S T z v) * f (z + v)‖
  rw [norm_mul, norm_mul, psi_norm hψ, psi_norm hψ, one_mul, one_mul, add_assoc,
    norm_theta_shift S T hψ hf a (z + v)]

theorem cont_heis (hψ : IsStdChar D ψ (-1)) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (v : MO S T) :
    Continuous (heisO ψ S T v f) := by
  delta heisO
  exact ((psi_cont hψ).comp (cont_symplOH_left S T v)).mul (hf.3.comp (continuous_add_right v))

theorem integrableOn_coef (hψ : IsStdChar D ψ (-1)) {f f' : MO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hf' : IsThetaFunO ψ S T f') (v : MO S T) (μ : Measure (MO S T)) (𝓕 : Set (MO S T))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) :
    IntegrableOn (fun x => heisO ψ S T v f x * conj (f' x)) 𝓕 μ := by
  refine integrableOn_of_periodic S T _
    ((cont_heis S T hψ hf v).mul (Complex.continuous_conj.comp hf'.3)) (fun a z => ?_) μ 𝓕 hμ h𝓕
  show ‖heisO ψ S T v f (ratW T S a + z) * conj (f' (ratW T S a + z))‖ =
    ‖heisO ψ S T v f z * conj (f' z)‖
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, norm_heis_shift S T hψ hf v a z,
    norm_theta_shift S T hψ hf' a z]

theorem heis_shift_rat (hψ : IsStdChar D ψ (-1)) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w z : MO S T)
    (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplOH S T (ratW T S a) w) * heisO ψ S T (w + ratW T S a) f z =
      ψ (symplOH S T z w) * ψ (symplO S T z (ratW T S a)) * f (z + w) := by
  have key : symplOH S T (ratW T S a) w + symplOH S T z (w + ratW T S a) +
      -symplOH S T (ratW T S a) (z + w) = symplOH S T z w + symplO S T z (ratW T S a) := by
    rw [symplOH_add_right, symplOH_add_right, symplOH_swap S T z (ratW T S a), ← symplOH_two]
    ring
  calc ψ (symplOH S T (ratW T S a) w) * heisO ψ S T (w + ratW T S a) f z
      = ψ (symplOH S T (ratW T S a) w) * (ψ (symplOH S T z (w + ratW T S a)) *
          (ψ (-symplOH S T (ratW T S a) (z + w)) * f (z + w))) := by
        show _ * (ψ _ * f (z + (w + ratW T S a))) = _
        rw [show z + (w + ratW T S a) = ratW T S a + (z + w) by abel, hf.1 a (z + w)]
    _ = ψ (symplOH S T (ratW T S a) w + symplOH S T z (w + ratW T S a) +
          -symplOH S T (ratW T S a) (z + w)) * f (z + w) := by
        rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
        ring
    _ = _ := by rw [key, AddChar.map_add_eq_mul]

theorem theta_zero : IsThetaFunO ψ S T 0 := by
  exact ⟨fun γ w => by simp, ⟨⊤, by simp, fun u _ _ => by funext z; simp [heisO]⟩, continuous_zero,
    fun k L _ _ _ => contDiff_const⟩

theorem theta_add {f g : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by
  obtain ⟨hq1, ⟨U1, hU1, hl1⟩, hc1, hs1⟩ := hf
  obtain ⟨hq2, ⟨U2, hU2, hl2⟩, hc2, hs2⟩ := hg
  refine ⟨fun γ w => ?_, ⟨U1 ⊓ U2, ?_, fun u hu h0 => ?_⟩, hc1.add hc2,
    fun k L hL h0 w => (hs1 k L hL h0 w).add (hs2 k L hL h0 w)⟩
  · simp only [Pi.add_apply, hq1 γ w, hq2 γ w, mul_add]
  · rw [AddSubgroup.coe_inf]
    exact hU1.inter hU2
  · have e1 := hl1 u hu.1 h0
    have e2 := hl2 u hu.2 h0
    funext z
    have z1 := congrFun e1 z
    have z2 := congrFun e2 z
    simp only [heisO, Pi.add_apply, Pi.zero_apply] at z1 z2 ⊢
    rw [mul_add, z1, z2]

theorem theta_smul (c : ℂ) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
  obtain ⟨hq1, ⟨U1, hU1, hl1⟩, hc1, hs1⟩ := hf
  refine ⟨fun γ w => ?_, ⟨U1, hU1, fun u hu h0 => ?_⟩, hc1.const_smul c,
    fun k L hL h0 w => (hs1 k L hL h0 w).const_smul c⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hq1 γ w]
    ring
  · have e1 := hl1 u hu h0
    funext z
    have z1 := congrFun e1 z
    simp only [heisO, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at z1 ⊢
    rw [mul_left_comm, z1]

end Theta

theorem kernelId_of (hC : CharComplete D) : KernelId D := by
  intro ψ hψ S T μ 𝓕 hμ h𝓕 f₁ f₁' f₂ f₂' h1 h1' h2 h2' hcoef x y
  obtain ⟨v, hv⟩ : ∃ v : WO S T, v = y - x := ⟨_, rfl⟩
  let φ : WO S T → ℂ := fun z => ψ (symplOH S T z v) *
    (f₁ (z + v) * conj (f₁' z) - f₂ (z + v) * conj (f₂' z))
  have hφc : Continuous φ := by
    have hs : Continuous fun z : WO S T => ψ (symplOH S T z v) :=
      (psi_cont hψ).comp (cont_symplOH_left S T v)
    exact hs.mul (((h1.3.comp (continuous_add_right v)).mul (Complex.continuous_conj.comp h1'.3)).sub
      ((h2.3.comp (continuous_add_right v)).mul (Complex.continuous_conj.comp h2'.3)))
  have hφp : ∀ γ w, φ (ratW T S γ + w) = φ w := by
    intro γ w
    have key : symplOH S T (ratW T S γ + w) v + -symplOH S T (ratW T S γ) (w + v) +
        symplOH S T (ratW T S γ) w = symplOH S T w v := by
      rw [symplOH_add_left, symplOH_add_right]
      ring
    have hconj : ∀ b : AF D.host.F, conj (ψ (-b)) = ψ b := fun b => by rw [psi_conj hψ, neg_neg]
    show ψ (symplOH S T (ratW T S γ + w) v) * (f₁ (ratW T S γ + w + v) * conj (f₁' (ratW T S γ + w)) -
        f₂ (ratW T S γ + w + v) * conj (f₂' (ratW T S γ + w))) =
      ψ (symplOH S T w v) * (f₁ (w + v) * conj (f₁' w) - f₂ (w + v) * conj (f₂' w))
    rw [add_assoc, h1.1 γ (w + v), h2.1 γ (w + v), h1'.1 γ w, h2'.1 γ w, map_mul, map_mul, hconj,
      ← key, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring
  have hφf : ∀ γ, ∫ z in 𝓕, φ z * ψ (symplO S T z (ratW T S γ)) ∂μ = 0 := by
    intro γ
    have hpt : ∀ z, φ z * ψ (symplO S T z (ratW T S γ)) = ψ (symplOH S T (ratW T S γ) v) *
        (heisO ψ S T (v + ratW T S γ) f₁ z * conj (f₁' z) -
          heisO ψ S T (v + ratW T S γ) f₂ z * conj (f₂' z)) := by
      intro z
      have e1 := heis_shift_rat S T hψ h1 v z γ
      have e2 := heis_shift_rat S T hψ h2 v z γ
      show ψ (symplOH S T z v) * (f₁ (z + v) * conj (f₁' z) - f₂ (z + v) * conj (f₂' z)) *
        ψ (symplO S T z (ratW T S γ)) = _
      linear_combination (-(conj (f₁' z))) * e1 + (conj (f₂' z)) * e2
    simp_rw [hpt]
    rw [integral_const_mul, integral_sub (integrableOn_coef S T hψ h1 h1' _ μ 𝓕 hμ h𝓕)
      (integrableOn_coef S T hψ h2 h2' _ μ 𝓕 hμ h𝓕)]
    have hc := hcoef (v + ratW T S γ)
    unfold coefO at hc
    rw [hc, sub_self, mul_zero]
  have hφ0 := (hC ψ hψ S T).2 μ 𝓕 hμ h𝓕 φ hφc hφp hφf
  have hx := congrFun hφ0 x
  have hx' : ψ (symplOH S T x v) * (f₁ (x + v) * conj (f₁' x) - f₂ (x + v) * conj (f₂' x)) = 0 := hx
  have h0 := (mul_eq_zero.mp hx').resolve_left (psi_ne hψ _)
  rw [hv, add_sub_cancel] at h0
  exact sub_eq_zero.mp h0

theorem polar_pt (u v : ℂ) : u * conj v = (1 / 4) * ((((‖u + v‖ ^ 2 : ℝ) : ℂ) - ((‖u - v‖ ^ 2 : ℝ) : ℂ)) +
    Complex.I * ((‖u + Complex.I * v‖ ^ 2 : ℝ) : ℂ) - Complex.I * ((‖u - Complex.I * v‖ ^ 2 : ℝ) : ℂ)) := by
  have key : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [key, key, key, key]
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * (u * conj v - v * conj u) * Complex.I_sq

section Svn

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

theorem norm_sq_integral_eq (hψ : IsStdChar D ψ (-1)) {g g' : MO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (hg' : IsThetaFunO ψ S T g') (μ : Measure (MO S T)) (𝓕 : Set (MO S T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ)
    (h : ∫⁻ w in 𝓕, ‖g w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖g' w‖ₑ ^ 2 ∂μ) :
    ∫ w in 𝓕, ‖g w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖g' w‖ ^ 2 ∂μ := by
  have key : ∀ k : MO S T → ℂ, Continuous k →
      ∫ w in 𝓕, ‖k w‖ ^ 2 ∂μ = (∫⁻ w in 𝓕, ‖k w‖ₑ ^ 2 ∂μ).toReal := by
    intro k hk
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun w => sq_nonneg _))
      (hk.norm.pow 2).aestronglyMeasurable]
    congr 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [key g hg.3, key g' hg'.3, h]

theorem svnSchurO_of (hK : KernelId D)
    (hH : ∀ (w : MO S T) (f : MO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f))
    (hψ : IsStdChar D ψ (-1)) : SvNSchurO ψ S T := by
  intro A hAθ hAc hAn
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕⟩, -⟩ := Formalism.IndefR.PHeisFC.finCovol T S
  have hint : ∀ h : WO S T → ℂ, IsThetaFunO ψ S T h →
      MeasureTheory.Integrable (fun x => ((‖h x‖ ^ 2 : ℝ) : ℂ)) (μ.restrict 𝓕) := by
    intro h hh
    refine integrableOn_of_periodic S T _ (Complex.continuous_ofReal.comp (hh.3.norm.pow 2))
      (fun a z => ?_) μ 𝓕 hμ h𝓕
    show ‖(((‖h (ratW T S a + z)‖ ^ 2 : ℝ)) : ℂ)‖ = ‖(((‖h z‖ ^ 2 : ℝ)) : ℂ)‖
    rw [norm_theta_shift S T hψ hh a z]
  have hsq : ∀ h : WO S T → ℂ, IsThetaFunO ψ S T h →
      ∫ x in 𝓕, ((‖A h x‖ ^ 2 : ℝ) : ℂ) ∂μ = ∫ x in 𝓕, ((‖h x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
    intro h hh
    rw [integral_complex_ofReal, integral_complex_ofReal,
      norm_sq_integral_eq S T hψ (hAθ h hh) hh μ 𝓕 hμ h𝓕 (hAn μ 𝓕 hμ h𝓕 h hh)]
  have hthsub : ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (f - g) := by
    intro f g hf hg
    have h1 := theta_add S T hf (theta_smul S T (-1) hg)
    rwa [neg_one_smul, ← sub_eq_add_neg] at h1
  have hpol : ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      ∫ x in 𝓕, f x * conj (g x) ∂μ = (1 / 4) *
        ((∫ x in 𝓕, ((‖(f + g) x‖ ^ 2 : ℝ) : ℂ) ∂μ - ∫ x in 𝓕, ((‖(f - g) x‖ ^ 2 : ℝ) : ℂ) ∂μ) +
          Complex.I * ∫ x in 𝓕, ((‖(f + Complex.I • g) x‖ ^ 2 : ℝ) : ℂ) ∂μ -
          Complex.I * ∫ x in 𝓕, ((‖(f - Complex.I • g) x‖ ^ 2 : ℝ) : ℂ) ∂μ) := by
    intro f g hf hg
    have i1 := hint _ (theta_add S T hf hg)
    have i2 := hint _ (hthsub f g hf hg)
    have i3 := hint _ (theta_add S T hf (theta_smul S T Complex.I hg))
    have i4 := hint _ (hthsub f _ hf (theta_smul S T Complex.I hg))
    have e : ∀ x, f x * conj (g x) = (1 / 4) * ((((‖(f + g) x‖ ^ 2 : ℝ) : ℂ) -
        ((‖(f - g) x‖ ^ 2 : ℝ) : ℂ)) + Complex.I * ((‖(f + Complex.I • g) x‖ ^ 2 : ℝ) : ℂ) -
        Complex.I * ((‖(f - Complex.I • g) x‖ ^ 2 : ℝ) : ℂ)) := fun x => polar_pt (f x) (g x)
    simp_rw [e]
    rw [integral_const_mul, integral_sub, integral_add, integral_sub, integral_const_mul,
      integral_const_mul]
    all_goals first
      | exact (i1.sub i2).add (i3.const_mul _)
      | exact i4.const_mul _
      | exact i1.sub i2
      | exact i3.const_mul _
      | exact i1
      | exact i2
  have hinner : ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      ∫ x in 𝓕, A f x * conj (A g x) ∂μ = ∫ x in 𝓕, f x * conj (g x) ∂μ := by
    intro f g hf hg
    rw [hpol (A f) (A g) (hAθ f hf) (hAθ g hg), hpol f g hf hg, ← map_add A f g, ← map_sub A f g,
      ← map_smul A Complex.I g, ← map_add A f (Complex.I • g), ← map_sub A f (Complex.I • g),
      hsq _ (theta_add S T hf hg), hsq _ (hthsub f g hf hg),
      hsq _ (theta_add S T hf (theta_smul S T Complex.I hg)),
      hsq _ (hthsub f _ hf (theta_smul S T Complex.I hg))]
  have hcoefA : ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      ∀ w, coefO ψ S T μ 𝓕 (A f) (A g) w = coefO ψ S T μ 𝓕 f g w := by
    intro f g hf hg w
    unfold coefO
    rw [← hAc w f hf]
    exact hinner _ _ (hH w f hf) hg
  have hker : ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ∀ x y,
      A f y * conj (A g x) = f y * conj (g x) := fun f g hf hg =>
    hK ψ hψ S T μ 𝓕 hμ h𝓕 (A f) (A g) f g (hAθ f hf) (hAθ g hg) hf hg (hcoefA f g hf hg)
  by_cases hall : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ x, f x = 0
  · refine ⟨1, norm_one, fun f hf => ?_⟩
    funext y
    have hk := hker f f hf hf y y
    rw [Complex.mul_conj, Complex.mul_conj, hall f hf y, map_zero] at hk
    have hz : A f y = 0 := by
      have h0 : Complex.normSq (A f y) = 0 := by exact_mod_cast hk
      exact Complex.normSq_eq_zero.mp h0
    rw [one_smul, hz, hall f hf y]
  · push_neg at hall
    obtain ⟨f0, hf0, x0, hx0⟩ := hall
    have hk0 := hker f0 f0 hf0 hf0 x0 x0
    rw [Complex.mul_conj, Complex.mul_conj] at hk0
    have hn : Complex.normSq (A f0 x0) = Complex.normSq (f0 x0) := by exact_mod_cast hk0
    have hA0 : A f0 x0 ≠ 0 := by
      intro h
      rw [h, map_zero, eq_comm, Complex.normSq_eq_zero] at hn
      exact hx0 hn
    have hnorm : ‖A f0 x0‖ = ‖f0 x0‖ := by
      have h2 : ‖A f0 x0‖ ^ 2 = ‖f0 x0‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hn]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
    refine ⟨conj (f0 x0) / conj (A f0 x0), ?_, fun f hf => ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_conj, hnorm, div_self (norm_ne_zero_iff.mpr hx0)]
    · funext y
      have hk := hker f f0 hf hf0 x0 y
      have hc0 : conj (A f0 x0) ≠ 0 := (map_ne_zero _).mpr hA0
      rw [Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination hk

theorem svnSchurO_all_of (hK : KernelId D)
    (hH : ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (w : WO S T) (f : WO S T → ℂ),
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f)) : SvNSchurOAll D := by
  intro ψ hψ S T
  exact svnSchurO_of S T hK (hH ψ hψ S T) hψ

end Svn

end Formalism.IndefR.Fin

end
