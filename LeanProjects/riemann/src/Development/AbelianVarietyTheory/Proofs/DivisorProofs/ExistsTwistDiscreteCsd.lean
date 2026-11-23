import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TwistDisc

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem pow_val_apply (χ : HChar E) (k : ℕ) (x : _) : (χ ^ k).1 x = χ.1 x ^ k := rfl

theorem chiInf_pow (χ : HChar E) (k : ℕ) (z : (Cinf E)ˣ) : chiInf (χ ^ k) z = chiInf χ z ^ k := rfl

theorem dchi_pow (χ : HChar E) (k : ℕ) : dchi (χ ^ k) = (k : ℝ) • dchi χ := by
  obtain ⟨L, hL⟩ := exists_lin _ (continuous_chiInf χ)
  have h1 : dchi χ = L := fderiv_extZero (continuous_chiInf χ) hL
  have h2 : dchi (χ ^ k) = (k : ℝ) • L := fderiv_extZero (continuous_chiInf (χ ^ k)) fun z => by
    rw [chiInf_pow, Units.val_pow_eq_pow_val, hL, ← Complex.exp_nat_mul]
    simp
  rw [h1, h2]

theorem expo_pow (χ : HChar E) (k : ℕ) (τ : E →+* ℂ) : expo (χ ^ k) τ = k * expo χ τ := by
  simp only [expo, dchi_pow, ContinuousLinearMap.smul_apply, Complex.real_smul, Complex.ofReal_natCast]
  ring

theorem chiDet_splitCentre {μ : HChar E} {e : InfinitePlace E → ℤ}
    (h : ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v) (t : ℝ) :
    chiDet a μ (splitCentre E a t) = 1 := by
  unfold splitCentre
  rw [chiDet, MonoidHom.comp_apply, det_infGL]
  change chiInf μ _ = 1
  apply Units.ext
  rw [h, Units.val_one]
  refine Finset.prod_eq_one fun v _ => ?_
  have hz : ((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => (t : ℂ))) : (Cinf E)ˣ) : Cinf E) v = ((Real.exp t ^ a : ℝ) : ℂ) := by
    simp [Matrix.scalar_apply, Matrix.det_diagonal, expU, Complex.ofReal_exp]
  rw [hz, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_self (by exact_mod_cast (by positivity : Real.exp t ^ a ≠ 0)), _root_.one_zpow]

theorem isSqInt_mulChi {χ : HChar E} (hu : χ.IsUnitary) (hs : ∀ t, chiDet a χ (splitCentre E a t) = 1) {φ : Sm E a}
    (h : IsSqInt φ.1) : IsSqInt (mulChi a χ φ).1 := by
  obtain ⟨h1, μ, 𝓕, hμ, hF, hI⟩ := h
  refine ⟨fun t g => ?_, μ, 𝓕, hμ, hF, ?_⟩
  · simp only [mulChi_apply, map_mul, hs, one_mul, h1]
  · have e : ∀ g, ‖(mulChi a χ φ).1 g‖ₑ = ‖φ.1 g‖ₑ := fun g => by
      have h2 : ‖((chiDet a χ g : ℂˣ) : ℂ)‖ₑ = 1 := by
        rw [← ofReal_norm_eq_enorm, show ‖((chiDet a χ g : ℂˣ) : ℂ)‖ = 1 from hu _, ENNReal.ofReal_one]
      rw [mulChi_apply, enorm_mul, h2, mul_one]
    simp only [e]
    exact hI

theorem isDiscrete_map {χ : HChar E} (hu : χ.IsUnitary) (hs : ∀ t, chiDet a χ (splitCentre E a t) = 1)
    {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) : IsDiscrete (V.map (mulChi a χ).toLinearMap) where
  aut := by rintro _ ⟨φ, hφ, rfl⟩; exact (hV.aut φ hφ).mulChi χ
  sqInt := by rintro _ ⟨φ, hφ, rfl⟩; exact isSqInt_mulChi hu hs (hV.sqInt φ hφ)
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, add_mem (V.smul_mem _ (hV.stable o φ hφ)) (V.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩
  ne_bot h := hV.ne_bot ((Submodule.map_eq_bot_iff (e := mulChi a χ)).1 h)
  irred W hW hW' := by
    have h := hV.irred (W.comap (mulChi a χ).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (mulChi a χ).injective h2]) fun o φ hφ => by
      have h1 : _ ∈ W.comap (mulChi a χ).toLinearMap := (act_mulChi χ o φ) ▸ hW' o _ hφ
      exact (Submodule.smul_mem_iff _ (Units.ne_zero (opMul χ o))).1
        ((Submodule.add_mem_iff_left _ (Submodule.smul_mem _ _ hφ)).1 h1)
    have e := Submodule.map_comap_eq_of_surjective (f := (mulChi a χ).toLinearMap) (mulChi a χ).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem isLocCompGL_map (χ : HChar E) {V : Submodule ℂ (Sm E a)} {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (h : IsLocCompGL V w σ) :
    IsLocCompGL (V.map (mulChi a χ).toLinearMap) w
      (σ.twist (CuspSub.locDet a χ w) (CuspSub.isOpen_ker_locDet χ w)) := by
  obtain ⟨f, h0, hV, hf⟩ := h
  refine ⟨(mulChi a χ).toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun v => (mulChi a χ).injective ?_),
    fun v => ⟨f v, hV v, rfl⟩, fun g v => ?_⟩
  · rw [LinearMap.zero_apply, map_zero]; exact LinearMap.congr_fun h v
  · change mulChi a χ (f (((CuspSub.locDet a χ w g : ℂˣ) : ℂ) • σ.ρ g v)) =
      rt E a (finGL E a (locGL E a w g)) (mulChi a χ (f v))
    rw [map_smul f, hf g v, rt_mulChi, CuspSub.chiDet_locGL]
    simp only [map_smul]
    rfl

theorem hasInfCharGL_map {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ} (h : HasInfCharGL V τ m)
    (χ : HChar E) : HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map, h.1], ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 3
  funext z
  simp only [Function.comp_apply]; ring

end GlobalTheory.BCT.TwistDisc
