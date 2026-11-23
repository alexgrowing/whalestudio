import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.BiadditiveFirstVariable

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF Gser IsLawOfLog cob at1 in3 d1 swap2 DivAB BetaHyp UnrOK)

attribute [local instance] Formalism.InvariantFactorPaths.G7.WModel.nf sx_charZero

variable {p : ℕ} [hp : Fact p.Prime]

theorem sx_pair_hasSubst {τ : Type} {u v : MvPowerSeries τ (K0 p)} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) : MvPowerSeries.HasSubst ![u, v] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (sx_two (τ := τ) hu hv)

theorem sx_subst_pair {τ τ' : Type} {b : τ → MvPowerSeries τ' (K0 p)} (hb : MvPowerSeries.HasSubst b)
    {u v : MvPowerSeries τ (K0 p)} (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0)
    (H : MvPowerSeries (Fin 2) (K0 p)) :
    MvPowerSeries.subst b (MvPowerSeries.subst ![u, v] H) =
      MvPowerSeries.subst ![MvPowerSeries.subst b u, MvPowerSeries.subst b v] H := by
  rw [MvPowerSeries.subst_comp_subst_apply (sx_pair_hasSubst hu hv) hb]
  congr 1
  funext s
  fin_cases s <;> rfl

theorem sx_subst_swap {τ : Type} {u v : MvPowerSeries τ (K0 p)} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) (H : MvPowerSeries (Fin 2) (K0 p)) :
    MvPowerSeries.subst ![u, v] (swap2 H) = MvPowerSeries.subst ![v, u] H := by
  unfold swap2
  rw [sx_subst_pair (sx_pair_hasSubst hu hv) (sx_cX 1) (sx_cX 0), MvPowerSeries.subst_X (sx_pair_hasSubst hu hv),
    MvPowerSeries.subst_X (sx_pair_hasSubst hu hv)]
  rfl

theorem biadditive_second_variable {F be : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) (h : BeProp p be) :
    Formalism.InvariantFactorPaths.G7.Simeq (d1 F (swap2 (inParam p be))) 0 := by
  have h1 := integralExp_param_of_equiv_zero p h.add2
  rw [th_inParam_sub, th_inParam_sub,
    param_substitution_pair be _ _ (MvPowerSeries.X 0) (MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 2] F) (sx_cX 0)
      (by rw [map_add, sx_cX, sx_cX, add_zero]) (sx_cX 0) (sx_law_const hF _ _ (sx_cX 1) (sx_cX 2)) (sx_eX 0)
      (by rw [sx_log_law hF _ _ (sx_cX 1) (sx_cX 2), sx_inParam_add, sx_eX, sx_eX]),
    param_substitution_pair be _ _ (MvPowerSeries.X 0) (MvPowerSeries.X 1) (sx_cX 0) (sx_cX 1) (sx_cX 0) (sx_cX 1) (sx_eX 0) (sx_eX 1),
    param_substitution_pair be _ _ (MvPowerSeries.X 0) (MvPowerSeries.X 2) (sx_cX 0) (sx_cX 2) (sx_cX 0) (sx_cX 2) (sx_eX 0) (sx_eX 2)]
    at h1
  have h2 := integralExp_rename p (![2, 0, 1] : Fin 3 → Fin 3) h1
  have hb : MvPowerSeries.HasSubst (fun k : Fin 3 =>
      (MvPowerSeries.X ((![2, 0, 1] : Fin 3 → Fin 3) k) : MvPowerSeries (Fin 3) (K0 p))) := th_ren_hasSubst _
  rw [th_ren_sub, th_ren_sub] at h2
  unfold ren at h2
  rw [sx_subst_pair hb (sx_cX 0) (sx_law_const hF _ _ (sx_cX 1) (sx_cX 2)),
    sx_subst_pair hb (sx_cX 1) (sx_cX 2), sx_subst_pair hb (sx_cX 0) (sx_cX 1), sx_subst_pair hb (sx_cX 0) (sx_cX 2),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at h2
  refine equiv_zero_of_integralExp p ?_
  unfold d1 in3
  rw [sx_subst_swap (sx_law_const hF _ _ (sx_cX 0) (sx_cX 1)) (sx_cX 2), sx_subst_swap (sx_cX 0) (sx_cX 2),
    sx_subst_swap (sx_cX 1) (sx_cX 2)]
  exact h2

theorem sx_root (ζ : K0 p) (hζ : ζ ^ (p ^ 2 - 1) = 1) :
    ∃ w : WW p, wK p w = ζ ∧ (sigW p)^[2] w = w ∧ wK p (sigW p w) = ζ ^ p := by
  have hN : 0 < p ^ 2 - 1 := by
    have := hp.out.two_le
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  have := Formalism.FG.WittVectorsCharZero.neZero_cast p 2 (by norm_num)
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (kb p) (p ^ 2 - 1)
  have hinj : Function.Injective (WittVector.teichmuller p : kb p →* WW p) := by
    intro a b h
    have := congrArg (fun x => WittVector.coeff x 0) h
    simpa [WittVector.teichmuller_coeff_zero] using this
  have h0 : IsPrimitiveRoot (wK p (WittVector.teichmuller p ξ)) (p ^ 2 - 1) :=
    (hξ.map_of_injective hinj).map_of_injective (IsFractionRing.injective (WW p) (K0 p))
  have : NeZero (p ^ 2 - 1) := ⟨hN.ne'⟩
  obtain ⟨k, _, hk⟩ := h0.eq_pow_of_pow_eq_one hζ
  have hfr : ∀ x : kb p, sigW p (WittVector.teichmuller p x) = (WittVector.teichmuller p x) ^ p := by
    intro x
    unfold sigW
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  have hx : (ξ ^ k) ^ (p ^ 2 - 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  refine ⟨WittVector.teichmuller p (ξ ^ k), ?_, ?_, ?_⟩
  · rw [map_pow]
    show algebraMap (WW p) (K0 p) ((WittVector.teichmuller p ξ) ^ k) = ζ
    rw [map_pow]; exact hk
  · show sigW p (sigW p _) = _
    rw [hfr, map_pow, hfr, ← pow_mul, ← map_pow, ← sq]
    congr 1
    have e : p ^ 2 = (p ^ 2 - 1) + 1 := by omega
    rw [e, pow_succ, hx, one_mul]
  · rw [hfr, map_pow]
    show algebraMap (WW p) (K0 p) (((WittVector.teichmuller p ξ) ^ k) ^ p) = ζ ^ p
    rw [map_pow, map_pow, ← hk]

def sx_j : Fin 2 → ℕ := ![0, 1]

def sx_rho (p : ℕ) [Fact p.Prime] : ℕ → MvPowerSeries (Fin 2) (K0 p) :=
  fun k => if k = 0 then MvPowerSeries.X 0 else if k = 1 then MvPowerSeries.X 1 else 0

theorem sx_conj {be : MvPowerSeries (Fin 2) (K0 p)} (h : BeProp p be) (ζ : K0 p) (hζ : ζ ^ (p ^ 2 - 1) = 1) :
    Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.subst ![MvPowerSeries.C ζ * (MvPowerSeries.X 0 :
                MvPowerSeries (Fin 2) (K0 p)), MvPowerSeries.X 1] (inParam p be))
              (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 p)),
                MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1] (inParam p be)) := by
  obtain ⟨w, hw, hw2, hwp⟩ := sx_root ζ hζ
  have hζp : (ζ ^ p) ^ (p ^ 2 - 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hc : ∀ (z : K0 p) (i : Fin 2), MvPowerSeries.constantCoeff
      (MvPowerSeries.C z * (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p))) = 0 := by
    intro z i; rw [map_mul, sx_cX, mul_zero]
  have hl : ∀ (z : K0 p) (i : Fin 2), z ^ (p ^ 2 - 1) = 1 →
      PowerSeries.subst (MvPowerSeries.C z * (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p))) (logF p) =
        inParam p (MvPowerSeries.C z * MvPowerSeries.X i) := by
    intro z i hz
    rw [sx_inParam_C_mul, sx_inParam_X, sx_logF_eq,
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.lgF_subst_C_mul hz hp.out.two_le _ (sx_cX i)]
    unfold sx_lX
    rw [sx_logF_eq]
  have h0 := h.conj w hw2
  have h1 : Simeq p (sub2 p be (MvPowerSeries.C ζ * MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) (K0 p))
      (sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1)) := by
    rw [← hwp, ← hw]
    exact h0
  have h2 := sx_simeq_of p h1
  rw [param_substitution_pair be _ _ (MvPowerSeries.C ζ * MvPowerSeries.X 0) (MvPowerSeries.X 1) (hc ζ 0) (sx_cX 1) (hc ζ 0) (sx_cX 1)
      (hl ζ 0 hζ) (sx_eX 1),
    param_substitution_pair be _ _ (MvPowerSeries.X 0) (MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1) (sx_cX 0) (hc _ 1) (sx_cX 0) (hc _ 1)
      (sx_eX 0) (hl _ 1 hζp)] at h2
  exact h2

theorem sx_betaHyp {F be : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) (h : BeProp p be) :
    BetaHyp p F (inParam p be) :=
  ⟨sx_divAB p h, biadditive_first_variable hF h, biadditive_second_variable hF h, fun ζ hζ => sx_conj h ζ hζ⟩

theorem sx_unrOK (h2 : 2 < p) : UnrOK (K0 p) p (sigK p).toRingHom :=
  ⟨hp.out, h2, sx_norm_p p, Formalism.InvariantFactorPaths.G7.WModel.abv_value p, sx_sig_frob p⟩

theorem restBeta (p : ℕ) [hp : Fact p.Prime] : RestBeta p := by
  intro h5 _ be hbe
  have := sx_ultra p
  have := Formalism.InvariantFactorPaths.G7.WModel.complete p
  obtain ⟨F, hF⟩ := (Formalism.InvariantFactorPaths.G7.Top.lawExists (K0 p) p hp.out (sx_norm_p p)).1
  obtain ⟨ζ0, hζ0⟩ := Formalism.FG.witt_teichmuller_root p 2 (by norm_num)
  obtain ⟨c, hc, hcc, hS⟩ := Formalism.InvariantFactorPaths.G7.Top.betaIsG (K0 p) p (sigK p).toRingHom (sx_unrOK (by omega))
    ⟨wK p ζ0, hζ0.map_of_injective (IsFractionRing.injective (WW p) (K0 p))⟩ F hF (inParam p be) (sx_betaHyp hF hbe)
  obtain ⟨w, rfl⟩ := (sx_norm_le_one_iff p c).1 hc
  have hs : ∀ x : WW p, (sigK p).toRingHom (algebraMap (WW p) (K0 p) x) = algebraMap (WW p) (K0 p) (sigW p x) := by
    intro x
    rw [sx_sigK_eq, Formalism.InvariantFactorPaths.G7.WModel.sig_coe]
    rfl
  rw [hs] at hS hcc
  rw [hs] at hcc
  refine ⟨w, IsFractionRing.injective (WW p) (K0 p) hcc, ?_⟩
  exact integralExp_of_equiv p hS

end Formalism.MainNotions.FormalGroupSystem.Pf
