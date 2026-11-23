import Mathlib
import GroundTheory.PAdicHodge.BdRAlg
import GroundTheory.PAdicHodge.BdRGalois
set_option maxSynthPendingDepth 1

noncomputable section

open IsLocalRing

namespace GroundTheory.PAdicHodge

section AlgCl

variable (p : ℕ) [Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔪" => maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)

instance isAdicComplete_maximalIdeal_bDeRhamPlus_padicComplex :
    IsAdicComplete (maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p))
      (BDeRhamPlus (normInteger ℂ_[p]) p) :=
  IsPerfectoidField.isAdicComplete_maximalIdeal_bDeRhamPlus (K := ℂ_[p]) (p := p)

instance : Algebra.FormallyEtale ℚ_[p] (PadicAlgCl p) :=
  Algebra.FormallyEtale.of_isSeparable _ _

theorem thetaAlgHom_eq_zero_of_mem_pow {n : ℕ} {a : 𝔹} (ha : a ∈ 𝔪 ^ (n + 1)) :
    thetaAlgHom p a = 0 := by
  have h : a ∈ 𝔪 := Ideal.pow_le_self (Nat.succ_ne_zero n) ha
  rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker] at h
  exact h

def thetaQuot (n : ℕ) : 𝔹 ⧸ 𝔪 ^ (n + 1) →ₐ[ℚ_[p]] ℂ_[p] :=
  Ideal.Quotient.liftₐ _ (thetaAlgHom p) fun _ ha => thetaAlgHom_eq_zero_of_mem_pow p ha

theorem thetaQuot_mk (n : ℕ) (x : 𝔹) :
    thetaQuot p n (Ideal.Quotient.mk _ x) = thetaAlgHom p x := rfl

theorem surjective_thetaQuot (n : ℕ) : Function.Surjective (thetaQuot p n) := by
  intro y
  obtain ⟨x, hx⟩ := IsPerfectoidField.surjective_thetaBDeRhamPlusField (K := ℂ_[p]) p y
  exact ⟨Ideal.Quotient.mk _ x, hx⟩

theorem isNilpotent_ker_thetaQuot (n : ℕ) :
    IsNilpotent (RingHom.ker (thetaQuot p n : 𝔹 ⧸ 𝔪 ^ (n + 1) →+* ℂ_[p])) := by
  have hle : RingHom.ker (thetaQuot p n : 𝔹 ⧸ 𝔪 ^ (n + 1) →+* ℂ_[p]) ≤
      Ideal.map (Ideal.Quotient.mk (𝔪 ^ (n + 1))) 𝔪 := by
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine Ideal.mem_map_of_mem _ ?_
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker]
    exact hy
  refine ⟨n + 1, le_bot_iff.1 ((Ideal.pow_right_mono hle (n + 1)).trans ?_)⟩
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

def algClToQuot (n : ℕ) : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹 ⧸ 𝔪 ^ (n + 1) :=
  Algebra.FormallySmooth.liftOfSurjective (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p])
    (thetaQuot p n) (surjective_thetaQuot p n) (isNilpotent_ker_thetaQuot p n)

theorem thetaQuot_algClToQuot (n : ℕ) (x : PadicAlgCl p) :
    thetaQuot p n (algClToQuot p n x) = (x : ℂ_[p]) :=
  Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ x

theorem eq_algClToQuot (n : ℕ) (g : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹 ⧸ 𝔪 ^ (n + 1))
    (hg : ∀ x, thetaQuot p n (g x) = (x : ℂ_[p])) : g = algClToQuot p n :=
  Algebra.FormallyUnramified.lift_unique' (thetaQuot p n) (isNilpotent_ker_thetaQuot p n) g _
    (AlgHom.ext fun x => by
      simp only [AlgHom.comp_apply]
      rw [hg, thetaQuot_algClToQuot])

theorem thetaQuot_factorₐ {k n : ℕ} (hle : k ≤ n) (y : 𝔹 ⧸ 𝔪 ^ (n + 1)) :
    thetaQuot p k (Ideal.Quotient.factorₐ ℚ_[p] (Ideal.pow_le_pow_right (Nat.succ_le_succ hle)) y) =
      thetaQuot p n y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

theorem factorₐ_comp_factorₐ {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (Ideal.Quotient.factorₐ ℚ_[p] (Ideal.pow_le_pow_right hab) : 𝔹 ⧸ 𝔪 ^ b →ₐ[ℚ_[p]] 𝔹 ⧸ 𝔪 ^ a).comp
      (Ideal.Quotient.factorₐ ℚ_[p] (Ideal.pow_le_pow_right hbc)) =
      Ideal.Quotient.factorₐ ℚ_[p] (Ideal.pow_le_pow_right (hab.trans hbc)) := by
  ext y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

theorem factorₐ_comp_algClToQuot {k n : ℕ} (hle : k ≤ n) :
    (Ideal.Quotient.factorₐ ℚ_[p] (Ideal.pow_le_pow_right (Nat.succ_le_succ hle))).comp
      (algClToQuot p n) = algClToQuot p k :=
  eq_algClToQuot p k _ fun x => by
    rw [AlgHom.comp_apply, thetaQuot_factorₐ p hle, thetaQuot_algClToQuot]

def algClToQuot' (n : ℕ) : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹 ⧸ 𝔪 ^ n :=
  (Ideal.Quotient.factorₐ ℚ_[p] (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (algClToQuot p n)

theorem factorₐ_comp_algClToQuot' {k n : ℕ} (hle : k ≤ n) :
    (Ideal.Quotient.factorₐ ℚ_[p] (Ideal.pow_le_pow_right hle)).comp (algClToQuot' p n) =
      algClToQuot' p k := by
  ext x
  simp only [algClToQuot', AlgHom.comp_apply]
  rw [← factorₐ_comp_algClToQuot p hle, AlgHom.comp_apply]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (algClToQuot p n x)
  rw [← hy]
  rfl

def algClToBdR : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹 :=
  IsAdicComplete.liftAlgHom 𝔪 (algClToQuot' p) fun hle => factorₐ_comp_algClToQuot' p hle

theorem mk_algClToBdR (n : ℕ) (x : PadicAlgCl p) :
    Ideal.Quotient.mk (𝔪 ^ n) (algClToBdR p x) = algClToQuot' p n x :=
  IsAdicComplete.mk_liftAlgHom _ _ _ n x

theorem mk_succ_algClToBdR (n : ℕ) (x : PadicAlgCl p) :
    Ideal.Quotient.mk (𝔪 ^ (n + 1)) (algClToBdR p x) = algClToQuot p n x := by
  rw [mk_algClToBdR, algClToQuot', ← factorₐ_comp_algClToQuot p (Nat.le_succ n)]

theorem thetaAlgHom_algClToBdR (x : PadicAlgCl p) : thetaAlgHom p (algClToBdR p x) = (x : ℂ_[p]) := by
  rw [← thetaQuot_mk p 0, mk_succ_algClToBdR, thetaQuot_algClToQuot]

theorem eq_algClToBdR (g : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹) (hg : ∀ x, thetaAlgHom p (g x) = (x : ℂ_[p])) :
    g = algClToBdR p := by
  have h1 : ∀ n, (Ideal.Quotient.mkₐ ℚ_[p] (𝔪 ^ (n + 1))).comp g = algClToQuot p n := fun n =>
    eq_algClToQuot p n _ fun x => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, thetaQuot_mk, hg]
  refine IsAdicComplete.algHom_ext 𝔪 fun n => AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [mk_algClToBdR, algClToQuot', ← h1 n]
  rfl

theorem injective_algClToBdR : Function.Injective (algClToBdR p) :=
  (algClToBdR p).toRingHom.injective

end AlgCl

section Galois

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p

theorem gal_smul_padicIntToWitt (σ : Gal(PadicAlgCl p/K)) (x : ℤ_[p]) :
    σ • IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p x =
      IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p x := by
  ext n
  rw [AInf.gal_smul_coeff]
  simp only [IsPerfectoidField.padicIntToWitt, RingHom.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod
    ((preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)).comp
      (ZMod.castHom (dvd_refl p) _)) (ZMod.castHom (dvd_refl p) _)) _

theorem gal_smul_algebraMap_bdR (σ : Gal(PadicAlgCl p/K)) (q : ℚ_[p]) :
    σ • algebraMap ℚ_[p] 𝔹 q = algebraMap ℚ_[p] 𝔹 q := by
  have h : (galBdR σ : 𝔹 →+* 𝔹).comp (algebraMap ℚ_[p] 𝔹) = algebraMap ℚ_[p] 𝔹 := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe, galBdR_apply]
    have hx : algebraMap ℤ_[p] ℚ_[p] x = (x : ℚ_[p]) := rfl
    rw [hx, IsPerfectoidField.algebraMap_padic_coe, gal_smul_wittToBDeRhamPlus,
      gal_smul_padicIntToWitt]
  have := RingHom.congr_fun h q
  simpa only [RingHom.comp_apply, RingHom.coe_coe, galBdR_apply] using this

theorem gal_smul_algClToBdR (σ : Gal(PadicAlgCl p/K)) (x : PadicAlgCl p) :
    σ • algClToBdR p x = algClToBdR p (σ x) := by
  let g : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹 :=
    { toRingHom := ((galBdR σ⁻¹ : 𝔹 ≃+* 𝔹) : 𝔹 →+* 𝔹).comp
        (((algClToBdR p : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹) : PadicAlgCl p →+* 𝔹).comp
          (σ : PadicAlgCl p →+* PadicAlgCl p))
      commutes' := fun q => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, galBdR_apply]
        rw [IsScalarTower.algebraMap_apply ℚ_[p] K (PadicAlgCl p), AlgEquiv.commutes,
          ← IsScalarTower.algebraMap_apply, AlgHom.commutes, gal_smul_algebraMap_bdR] }
  have hg : g = algClToBdR p := eq_algClToBdR p g fun y => by
    change thetaAlgHom p (σ⁻¹ • algClToBdR p (σ y)) = (y : ℂ_[p])
    rw [thetaAlgHom_apply, thetaBDeRhamPlusField_gal_smul, ← thetaAlgHom_apply,
      thetaAlgHom_algClToBdR, gal_smul_coe]
    congr 1
    change (σ⁻¹ * σ) y = y
    rw [inv_mul_cancel]
    rfl
  have h2 : σ⁻¹ • algClToBdR p (σ x) = algClToBdR p x := AlgHom.congr_fun hg x
  rw [← h2, smul_inv_smul]

end Galois

end GroundTheory.PAdicHodge
