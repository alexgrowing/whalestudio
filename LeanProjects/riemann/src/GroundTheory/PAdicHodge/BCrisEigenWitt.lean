import Mathlib
import GroundTheory.PAdicHodge.AInfGalois
import GroundTheory.PAdicHodge.TiltAlgClosed
import GroundTheory.PAdicHodge.TiltField
import GroundTheory.PAdicHodge.BdRAlg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace EigenWitt

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "C♭" => Tilt ℂ_[p] NormedField.valuation (normInteger ℂ_[p]) normInteger_integers p

variable (p) in

abbrev Fpbar : Type := AlgebraicClosure (ZMod p)

theorem exists_pow_eq_self_fpbar (a : Fpbar p) : ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a := by
  have hint : IsIntegral (ZMod p) a := Algebra.IsIntegral.isIntegral a
  let F := IntermediateField.adjoin (ZMod p) {a}
  have : FiniteDimensional (ZMod p) F := IntermediateField.adjoin.finiteDimensional hint
  have : Finite F := Module.finite_of_finite (ZMod p)
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hpn, hcard⟩ := FiniteField.card F p
  refine ⟨n, n.pos, ?_⟩
  have h := FiniteField.pow_card (⟨a, IntermediateField.mem_adjoin_simple_self (ZMod p) a⟩ : F)
  rw [hcard] at h
  exact congrArg Subtype.val h

abbrev zmodAlgebraTilt : Algebra (ZMod p) C♭ := (ZMod.castHom (dvd_refl p) C♭).toAlgebra

def fpbarToTilt : Fpbar p →+* C♭ :=
  letI := zmodAlgebraTilt (p := p)
  (IsAlgClosed.lift (R := ZMod p) (S := Fpbar p) (M := C♭)).toRingHom

theorem norm_le_one_of_pow_eq_self {x : C♭} {n : ℕ} (hn : 0 < n) (hx : x ^ p ^ n = x) :
    ‖x‖ ≤ 1 := by
  by_contra h
  push Not at h
  have h1 : ‖x‖ ^ p ^ n = ‖x‖ := by rw [← norm_pow, hx]
  have hpn : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.out.one_lt
  have h2 : ‖x‖ ^ 1 < ‖x‖ ^ p ^ n := pow_lt_pow_right₀ h hpn
  rw [pow_one, h1] at h2
  exact lt_irrefl _ h2

theorem exists_algebraMap_eq_fpbarToTilt (a : Fpbar p) :
    ∃ b : 𝒪♭, algebraMap 𝒪♭ C♭ b = fpbarToTilt a := by
  obtain ⟨n, hn, ha⟩ := exists_pow_eq_self_fpbar a
  refine norm_le_one_iff_exists_algebraMap.1 (norm_le_one_of_pow_eq_self hn ?_)
  rw [← map_pow, ha]

theorem algebraMap_preTilt_injective : Function.Injective (algebraMap 𝒪♭ C♭) :=
  IsFractionRing.injective 𝒪♭ C♭

def fpbarToRange : Fpbar p →+* (algebraMap 𝒪♭ C♭).range :=
  fpbarToTilt.codRestrict (algebraMap 𝒪♭ C♭).range fun a => by
    obtain ⟨b, hb⟩ := exists_algebraMap_eq_fpbarToTilt a
    exact ⟨b, hb⟩

def preTiltRangeEquiv : 𝒪♭ ≃+* (algebraMap 𝒪♭ C♭).range :=
  RingEquiv.ofBijective (algebraMap 𝒪♭ C♭).rangeRestrict
    ⟨fun _ _ h => algebraMap_preTilt_injective (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

def fpbarToPreTilt : Fpbar p →+* 𝒪♭ :=
  (preTiltRangeEquiv (p := p)).symm.toRingHom.comp fpbarToRange

theorem algebraMap_fpbarToPreTilt (a : Fpbar p) :
    algebraMap 𝒪♭ C♭ (fpbarToPreTilt a) = fpbarToTilt a :=
  congrArg Subtype.val ((preTiltRangeEquiv (p := p)).apply_symm_apply (fpbarToRange a))

theorem fpbarToPreTilt_injective : Function.Injective (fpbarToPreTilt (p := p)) :=
  fpbarToPreTilt.injective

theorem exists_fpbarToPreTilt_eq {x : 𝒪♭} {n : ℕ} (hn : 0 < n) (hx : x ^ p ^ n = x) :
    ∃ a : Fpbar p, fpbarToPreTilt a = x := by
  classical
  set P : (Fpbar p)[X] := X ^ p ^ n - X with hP
  have hpn : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.out.one_lt
  have hdeg : (X ^ p ^ n - X : (𝒪♭)[X]).natDegree = p ^ n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hpn]
  have hne : (X ^ p ^ n - X : (𝒪♭)[X]) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hmap : P.map fpbarToPreTilt = X ^ p ^ n - X := by simp [hP]
  have hroots := (IsAlgClosed.splits P).roots_map_of_injective (fpbarToPreTilt_injective (p := p))
  have hmem : x ∈ (P.map fpbarToPreTilt).roots := by
    rw [hmap, mem_roots hne]
    simp [hx]
  rw [hroots, Multiset.mem_map] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  exact ⟨a, ha⟩

theorem fpbarToPreTilt_pow_eq_self (a : Fpbar p) : ∃ n : ℕ, 0 < n ∧
    fpbarToPreTilt a ^ p ^ n = fpbarToPreTilt a := by
  obtain ⟨n, hn, ha⟩ := exists_pow_eq_self_fpbar a
  exact ⟨n, hn, by rw [← map_pow, ha]⟩

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

abbrev galFlat (σ : Gal(PadicAlgCl p/K)) : 𝒪♭ →+* 𝒪♭ :=
  preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)

theorem galFlat_mem_range (σ : Gal(PadicAlgCl p/K)) (a : Fpbar p) :
    galFlat σ (fpbarToPreTilt a) ∈ (fpbarToPreTilt (p := p)).range := by
  obtain ⟨n, hn, h⟩ := fpbarToPreTilt_pow_eq_self a
  exact exists_fpbarToPreTilt_eq hn (by rw [← map_pow, h])

def fpbarRangeEquiv : Fpbar p ≃+* (fpbarToPreTilt (p := p)).range :=
  RingEquiv.ofBijective (fpbarToPreTilt (p := p)).rangeRestrict
    ⟨fun _ _ h => fpbarToPreTilt_injective (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

def galFpbar (σ : Gal(PadicAlgCl p/K)) : Fpbar p →+* Fpbar p :=
  (fpbarRangeEquiv (p := p)).symm.toRingHom.comp
    (((galFlat σ).comp fpbarToPreTilt).codRestrict _ (galFlat_mem_range σ))

theorem fpbarToPreTilt_galFpbar (σ : Gal(PadicAlgCl p/K)) (a : Fpbar p) :
    fpbarToPreTilt (galFpbar σ a) = galFlat σ (fpbarToPreTilt a) :=
  congrArg Subtype.val ((fpbarRangeEquiv (p := p)).apply_symm_apply
    ((((galFlat σ).comp fpbarToPreTilt).codRestrict _ (galFlat_mem_range σ)) a))

def wittToAInf : WittVector p (Fpbar p) →+* AInf ℂ_[p] p := WittVector.map fpbarToPreTilt

theorem wittToAInf_injective : Function.Injective (wittToAInf (p := p)) :=
  WittVector.map_injective _ fpbarToPreTilt_injective

theorem gal_smul_wittToAInf (σ : Gal(PadicAlgCl p/K)) (x : WittVector p (Fpbar p)) :
    σ • wittToAInf x = wittToAInf (WittVector.map (galFpbar σ) x) := by
  ext n
  rw [AInf.gal_smul_coeff, wittToAInf, WittVector.map_coeff, WittVector.map_coeff,
    WittVector.map_coeff, fpbarToPreTilt_galFpbar]

def padicIntToWittFpbar : ℤ_[p] →+* WittVector p (Fpbar p) :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (Fpbar p))).comp (WittVector.equiv p).symm.toRingHom

theorem wittToAInf_padicIntToWittFpbar (z : ℤ_[p]) :
    wittToAInf (padicIntToWittFpbar z) = IsPerfectoidField.padicIntToWitt p z := by
  ext n
  simp only [wittToAInf, padicIntToWittFpbar, IsPerfectoidField.padicIntToWitt, RingHom.comp_apply,
    WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod (fpbarToPreTilt.comp (ZMod.castHom (dvd_refl p) (Fpbar p)))
    (ZMod.castHom (dvd_refl p) 𝒪♭)) _

theorem map_padicIntToWittFpbar (τ : Fpbar p →+* Fpbar p) (z : ℤ_[p]) :
    WittVector.map τ (padicIntToWittFpbar z) = padicIntToWittFpbar z := by
  ext n
  simp only [padicIntToWittFpbar, RingHom.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod (τ.comp (ZMod.castHom (dvd_refl p) (Fpbar p)))
    (ZMod.castHom (dvd_refl p) (Fpbar p))) _

theorem map_frobenius_comm {R S : Type*} [CommRing R] [CommRing S] [CharP R p] [CharP S p]
    (f : R →+* S) (x : WittVector p R) :
    WittVector.map f (WittVector.frobenius x) = WittVector.frobenius (WittVector.map f x) := by
  ext n
  rw [WittVector.map_coeff, WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP,
    WittVector.map_coeff, map_pow]

theorem frobenius_padicIntToWittFpbar (z : ℤ_[p]) :
    WittVector.frobenius (padicIntToWittFpbar z) = padicIntToWittFpbar z := by
  simp only [padicIntToWittFpbar, RingHom.comp_apply]
  rw [← map_frobenius_comm, WittVector.frobenius_zmodp]

theorem exists_zmod_of_pow_eq_self {a : Fpbar p} (ha : a ^ p = a) :
    ∃ b : ZMod p, ZMod.castHom (dvd_refl p) (Fpbar p) b = a := by
  classical
  set P : (ZMod p)[X] := X ^ p - X with hP
  have hdeg : P.natDegree = p := by
    rw [hP, natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hp.out.one_lt]
  have hroots : P.roots = Finset.univ.val := by
    have h := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rwa [ZMod.card] at h
  have hcard : Multiset.card P.roots = P.natDegree := by
    rw [hroots, hdeg, Finset.card_val, Finset.card_univ, ZMod.card]
  have hmap := roots_map_of_injective_of_card_eq_natDegree
    (ZMod.castHom (dvd_refl p) (Fpbar p)).injective hcard
  have hne : (X ^ p - X : (Fpbar p)[X]) ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simp [hp.out.one_lt]), natDegree_X_pow,
      natDegree_zero] at this
    exact hp.out.ne_zero this
  have hmem : a ∈ (P.map (ZMod.castHom (dvd_refl p) (Fpbar p))).roots := by
    rw [show P.map (ZMod.castHom (dvd_refl p) (Fpbar p)) = X ^ p - X by simp [hP], mem_roots hne]
    simp [ha]
  rw [← hmap, Multiset.mem_map] at hmem
  obtain ⟨b, -, hb⟩ := hmem
  exact ⟨b, hb⟩

theorem exists_padicInt_of_frobenius_eq {y : WittVector p (Fpbar p)}
    (hy : WittVector.frobenius y = y) : ∃ z : ℤ_[p], padicIntToWittFpbar z = y := by
  have hc : ∀ n, ∃ b : ZMod p, ZMod.castHom (dvd_refl p) (Fpbar p) b = y.coeff n := fun n =>
    exists_zmod_of_pow_eq_self (by rw [← WittVector.coeff_frobenius_charP, hy])
  choose b hb using hc
  refine ⟨WittVector.equiv p (WittVector.mk p b), ?_⟩
  ext n
  simp only [padicIntToWittFpbar, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, WittVector.map_coeff]
  exact hb n

theorem exists_frobenius_eq_mul (w : ℤ_[p]ˣ) :
    ∃ b : (WittVector p (Fpbar p))ˣ,
      WittVector.frobenius (b : WittVector p (Fpbar p)) = (b : WittVector p (Fpbar p)) * padicIntToWittFpbar (w : ℤ_[p]) := by
  set a₂ := padicIntToWittFpbar (p := p) w
  have ha₂u : IsUnit a₂ := (w.isUnit).map _
  have ha₁ : (1 : WittVector p (Fpbar p)).coeff 0 ≠ 0 := by simp
  have ha₂ : a₂.coeff 0 ≠ 0 := by
    have := ha₂u.map (WittVector.constantCoeff (p := p) (R := Fpbar p))
    exact this.ne_zero
  have hrot := WittVector.frobenius_frobeniusRotation p ha₁ ha₂
  have hne := WittVector.frobeniusRotation_nonzero p ha₁ ha₂
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' _ hne
  refine ⟨u, ?_⟩
  rw [mul_one, hu, map_mul, map_pow, map_natCast, mul_assoc] at hrot
  exact mul_left_cancel₀ (pow_ne_zero _ (WittVector.irreducible p).ne_zero) hrot

theorem exists_map_eq_mul {w : ℤ_[p]ˣ} {b : (WittVector p (Fpbar p))ˣ}
    (hb : WittVector.frobenius (b : WittVector p (Fpbar p)) = (b : WittVector p (Fpbar p)) * padicIntToWittFpbar (w : ℤ_[p]))
    (τ : Fpbar p →+* Fpbar p) :
    ∃ z : ℤ_[p], WittVector.map τ (b : WittVector p (Fpbar p)) = padicIntToWittFpbar z * b := by
  set W := padicIntToWittFpbar (p := p)
  have hWu : IsUnit (W w) := (w.isUnit).map _
  set y := WittVector.map τ (b : WittVector p (Fpbar p)) * ((b⁻¹ : (WittVector p (Fpbar p))ˣ) :
    WittVector p (Fpbar p)) with hy
  have hfb : WittVector.frobenius ((b⁻¹ : (WittVector p (Fpbar p))ˣ) : WittVector p (Fpbar p)) *
      (b * W w) = 1 := by
    rw [← hb, ← map_mul, Units.inv_mul, map_one]
  have hfy : WittVector.frobenius y = y := by
    rw [hy, map_mul, ← map_frobenius_comm, hb, map_mul, map_padicIntToWittFpbar]
    have e : WittVector.frobenius ((b⁻¹ : (WittVector p (Fpbar p))ˣ) : WittVector p (Fpbar p)) =
        ((b⁻¹ : (WittVector p (Fpbar p))ˣ) : WittVector p (Fpbar p)) * hWu.unit⁻¹ := by
      have h1 : (b : WittVector p (Fpbar p)) * W w * (((b⁻¹ : (WittVector p (Fpbar p))ˣ) :
          WittVector p (Fpbar p)) * hWu.unit⁻¹) = 1 := by
        calc (b : WittVector p (Fpbar p)) * W w * (((b⁻¹ : (WittVector p (Fpbar p))ˣ) :
              WittVector p (Fpbar p)) * hWu.unit⁻¹)
            = ((b : WittVector p (Fpbar p)) * ((b⁻¹ : (WittVector p (Fpbar p))ˣ) :
              WittVector p (Fpbar p))) * (W w * hWu.unit⁻¹) := by ring
          _ = 1 := by rw [Units.mul_inv, IsUnit.mul_val_inv, one_mul]
      calc WittVector.frobenius ((b⁻¹ : (WittVector p (Fpbar p))ˣ) : WittVector p (Fpbar p))
          = WittVector.frobenius ((b⁻¹ : (WittVector p (Fpbar p))ˣ) : WittVector p (Fpbar p)) *
              ((b * W w) * (((b⁻¹ : (WittVector p (Fpbar p))ˣ) : WittVector p (Fpbar p)) *
                hWu.unit⁻¹)) := by rw [h1, mul_one]
        _ = _ := by rw [← mul_assoc, hfb, one_mul]
    rw [e]
    calc WittVector.map τ (b : WittVector p (Fpbar p)) * W w *
          (((b⁻¹ : (WittVector p (Fpbar p))ˣ) : WittVector p (Fpbar p)) * hWu.unit⁻¹)
        = WittVector.map τ (b : WittVector p (Fpbar p)) *
            ((b⁻¹ : (WittVector p (Fpbar p))ˣ) : WittVector p (Fpbar p)) * (W w * hWu.unit⁻¹) := by
          ring
      _ = y := by rw [IsUnit.mul_val_inv, mul_one]
  obtain ⟨z, hz⟩ := exists_padicInt_of_frobenius_eq hfy
  refine ⟨z, ?_⟩
  rw [hz, hy, mul_assoc, Units.inv_mul, mul_one]

theorem exists_unit_aInf_eigen (w : ℤ_[p]ˣ) :
    ∃ b : (WittVector p (Fpbar p))ˣ,
      WittVector.frobenius (b : WittVector p (Fpbar p)) = (b : WittVector p (Fpbar p)) * padicIntToWittFpbar (w : ℤ_[p]) ∧
      ∀ σ : Gal(PadicAlgCl p/K), ∃ z : ℤ_[p],
        σ • wittToAInf (b : WittVector p (Fpbar p)) =
          IsPerfectoidField.padicIntToWitt p z * wittToAInf (b : WittVector p (Fpbar p)) := by
  obtain ⟨b, hb⟩ := exists_frobenius_eq_mul w
  refine ⟨b, hb, fun σ => ?_⟩
  obtain ⟨z, hz⟩ := exists_map_eq_mul hb (galFpbar σ)
  refine ⟨z, ?_⟩
  rw [gal_smul_wittToAInf, hz, map_mul, wittToAInf_padicIntToWittFpbar]

end EigenWitt

end GroundTheory.PAdicHodge
