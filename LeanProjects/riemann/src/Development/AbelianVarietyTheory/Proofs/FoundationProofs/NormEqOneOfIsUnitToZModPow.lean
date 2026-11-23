import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftSLMapMulInvMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VanishOrdOfKatoUse
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

noncomputable section

namespace GlobalTheory.K4.TwistClauses

variable {l : ℕ} [hl : Fact l.Prime]

theorem mem_O_of_pow_eq_one (c : Coef l) (z : Qbar l) (hz : z ^ (l - 1) = 1) : z ∈ c.O := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have ho : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  haveI : NeZero (l - 1) := ⟨by have := hl.out.two_le; omega⟩
  have h1 : IsPrimitiveRoot g (l - 1) := ho ▸ IsPrimitiveRoot.orderOf g
  have h2 : IsPrimitiveRoot (g : ZMod l) (l - 1) :=
    h1.map_of_injective (f := Units.coeHom (ZMod l)) Units.val_injective
  have hinj : Function.Injective (WittVector.teichmuller l (R := ZMod l)) := fun a b h => by
    simpa [WittVector.teichmuller_coeff_zero] using congrArg (fun x => x.coeff 0) h
  obtain ⟨ω, hω⟩ : ∃ ω : ℤ_[l], IsPrimitiveRoot ω (l - 1) :=
    ⟨_, (h2.map_of_injective hinj).map_of_injective (f := WittVector.equiv l) (WittVector.equiv l).injective⟩
  have hf : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := fun a b h =>
    PadicInt.ext ((algebraMap ℚ_[l] (Qbar l)).injective h)
  obtain ⟨i, -, hi⟩ := (hω.map_of_injective hf).eq_pow_of_pow_eq_one hz
  rw [← hi]
  exact pow_mem (c.O.algebraMap_mem ω) i

theorem norm_algebraMap_padicInt (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) z‖ = ‖z‖ :=
  norm_algebraMap' (Qbar l) (z : ℚ_[l])

theorem norm_eq_one_of_pow {z : Qbar l} (hz : z ^ (l - 1) = 1) : ‖z‖ = 1 := by
  have h : ‖z‖ ^ (l - 1) = 1 := by rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by have := hl.out.two_le; omega)).1 h

theorem norm_eq_one_of_isUnit_toZModPow {r : ℕ} (hr : r ≠ 0) {a : ℤ_[l]} (ha : IsUnit (PadicInt.toZModPow r a)) : ‖a‖ = 1 := by
  by_contra h
  obtain ⟨k, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd a).1 (lt_of_le_of_ne a.norm_le_one h)
  rw [map_mul, map_natCast] at ha
  have h2 := (ZMod.isUnit_iff_coprime l (l ^ r)).1 (isUnit_of_mul_isUnit_left ha)
  exact hl.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h2 (dvd_pow_self l hr))

theorem norm_inv_pow_sub_le {r : ℕ} (hr : r ≠ 0) (e : ℕ) {a b : ℤ_[l]} (ha : IsUnit (PadicInt.toZModPow r a))
    (hab : PadicInt.toZModPow r a = PadicInt.toZModPow r b) :
    ‖(algebraMap ℤ_[l] (Qbar l) a ^ e)⁻¹ - (algebraMap ℤ_[l] (Qbar l) b ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have na : ‖algebraMap ℤ_[l] (Qbar l) a ^ e‖ = 1 := by
    rw [norm_pow, norm_algebraMap_padicInt, norm_eq_one_of_isUnit_toZModPow hr ha, one_pow]
  have nb : ‖algebraMap ℤ_[l] (Qbar l) b ^ e‖ = 1 := by
    rw [norm_pow, norm_algebraMap_padicInt, norm_eq_one_of_isUnit_toZModPow hr (hab ▸ ha), one_pow]
  have hk : b ^ e - a ^ e ∈ RingHom.ker (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)) := by
    rw [RingHom.mem_ker, map_sub, map_pow, map_pow, hab, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  obtain ⟨k, hk⟩ := hk
  have hk' := congrArg (algebraMap ℤ_[l] (Qbar l)) hk
  rw [map_sub, map_pow, map_pow, map_mul, map_pow, map_natCast] at hk'
  rw [inv_sub_inv (norm_ne_zero_iff.1 (by rw [na]; exact one_ne_zero)) (norm_ne_zero_iff.1 (by rw [nb]; exact one_ne_zero)),
    norm_div, norm_mul, na, nb, mul_one, div_one, hk', norm_mul, norm_algebraMap_padicInt]
  exact mul_le_of_le_one_right (norm_nonneg _) k.norm_le_one

theorem val_cast_eq {r : ℕ} (hr : r ≠ 0) (z : ZMod (l ^ r)) :
    ((z.val : ℕ) : ZMod l) = ZMod.castHom (dvd_pow_self l hr) (ZMod l) z := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  rw [ZMod.natCast_val]; rfl

theorem val_cast_ne_zero {r : ℕ} (hr : r ≠ 0) (x : (ZMod (l ^ r))ˣ) : (((x : ZMod (l ^ r)).val : ℕ) : ZMod l) ≠ 0 := by
  rw [val_cast_eq hr]
  exact (x.isUnit.map _).ne_zero

theorem val_level_zero (z : ZMod (l ^ 0)) : z.val = 0 := by
  haveI : NeZero (l ^ 0) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have := ZMod.val_lt z
  simp only [pow_zero] at this
  omega

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

variable (Ω l) in

def cycRes : G ℚ Ω →* ZMod l :=
  (ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)).toMonoidHom.comp ((Units.coeHom (ZMod (l ^ 1))).comp (cycMod ℚ Ω l 1))

theorem cycRes_eq_val (s : G ℚ Ω) : (((cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val : ℕ) : ZMod l) = cycRes l Ω s :=
  val_cast_eq one_ne_zero _

theorem cycRes_eq_cast {r : ℕ} (hr : r ≠ 0) (s : G ℚ Ω) :
    ZMod.castHom (dvd_pow_self l hr) (ZMod l) (cycMod ℚ Ω l r s : ZMod (l ^ r)) = cycRes l Ω s := by
  have h1r : 1 ≤ r := Nat.one_le_iff_ne_zero.2 hr
  show ZMod.castHom (dvd_pow_self l hr) (ZMod l) (PadicInt.toZModPow r (cycZ ℚ Ω l s : ℤ_[l])) =
    ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l) (PadicInt.toZModPow 1 (cycZ ℚ Ω l s : ℤ_[l]))
  rw [← PadicInt.zmod_cast_comp_toZModPow 1 r h1r, RingHom.comp_apply, ← RingHom.comp_apply _ (ZMod.castHom _ (ZMod (l ^ 1))),
    RingHom.ext_zmod (RingHom.comp _ _) (ZMod.castHom (dvd_pow_self l hr) (ZMod l))]

theorem cycRes_ne_zero (s : G ℚ Ω) : cycRes l Ω s ≠ 0 := by
  rw [← cycRes_eq_val]; exact val_cast_ne_zero one_ne_zero _

theorem exists_cycRes_eq [IsAlgClosure ℚ Ω] {r : ℕ} (hr : r ≠ 0) (x : (ZMod (l ^ r))ˣ) :
    ∃ t : G ℚ Ω, cycRes l Ω t = (((x : ZMod (l ^ r)).val : ℕ) : ZMod l) := by
  obtain ⟨t, rfl⟩ := cycMod_surjective Ω l r x
  exact ⟨t, by rw [val_cast_eq hr, cycRes_eq_cast hr]⟩

theorem continuous_cycBar' : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

theorem cycBar_val (s : G ℚ Ω) : (cycBar ℚ Ω l s : Qbar l) = algebraMap ℤ_[l] (Qbar l) (cycZ ℚ Ω l s : ℤ_[l]) := rfl

theorem cycZ_inertia [IsAlgClosure ℚ Ω] {q : Pl} (hq : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal) {B : ValuationSubring Ω}
    (hB : IsPlaceOver B q) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) : cycZ ℚ Ω l s = 1 :=
  Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
    rw [ReciprocityTheory.Gal.cycZ_toZModPow_eq hq hB (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
    simp)

theorem chiK_update {r : ℕ} (hr : r ≠ 0) (ψ : ZMod l → Qbar l) (x : (ZMod (l ^ r))ˣ) :
    chiK l (Function.update ψ 0 0) r x = chiK l ψ r x :=
  Function.update_of_ne (val_cast_ne_zero hr x) _ _

theorem chiK_update_zero (ψ : ZMod l → Qbar l) (x : (ZMod (l ^ 0))ˣ) : chiK l (Function.update ψ 0 0) 0 x = 0 := by
  rw [chiK, val_level_zero, Nat.cast_zero, Function.update_self]

section Chi

variable {ψ : ZMod l → Qbar l} {χ : G ℚ Ω →* (Qbar l)ˣ}

theorem chi_eq_one (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) {s : G ℚ Ω} (hs : cycRes l Ω s = 1) : χ s = 1 := by
  apply Units.ext
  rw [hχ, hs, ← map_one (cycRes l Ω), ← hχ, map_one]

theorem chi_pow (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) (s : G ℚ Ω) : (χ s : Qbar l) ^ (l - 1) = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← map_pow,
    chi_eq_one hχ (by rw [map_pow]; exact ZMod.pow_card_sub_one_eq_one (cycRes_ne_zero s)), Units.val_one]

theorem chiK_pow [IsAlgClosure ℚ Ω] (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) {r : ℕ} (hr : r ≠ 0)
    (x : (ZMod (l ^ r))ˣ) : chiK l ψ r x ^ (l - 1) = 1 := by
  obtain ⟨t, ht⟩ := exists_cycRes_eq (Ω := Ω) hr x
  rw [chiK, ← ht, ← hχ]
  exact chi_pow hχ t

theorem chiK_mul_cycMod [IsAlgClosure ℚ Ω] (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) {r : ℕ} (hr : r ≠ 0)
    (x : (ZMod (l ^ r))ˣ) (s : G ℚ Ω) : chiK l ψ r (x * cycMod ℚ Ω l r s) = chiK l ψ r x * χ s := by
  obtain ⟨t, ht⟩ := exists_cycRes_eq (Ω := Ω) hr x
  rw [chiK, chiK, val_cast_eq hr, Units.val_mul, map_mul, ← val_cast_eq hr, ← ht, cycRes_eq_cast hr, ← map_mul, ← hχ, ← hχ,
    map_mul, Units.val_mul]

omit hl in
theorem chiK_succ [Fact l.Prime] (ψ : ZMod l → Qbar l) {r : ℕ} (hr : r ≠ 0) (x : (ZMod (l ^ (r + 1)))ˣ) :
    chiK l ψ (r + 1) x =
      chiK l ψ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x) := by
  rw [chiK, chiK, val_cast_eq hr, val_cast_eq (Nat.succ_ne_zero r)]
  congr 1
  exact (RingHom.congr_fun (RingHom.ext_zmod ((ZMod.castHom (dvd_pow_self l hr) (ZMod l)).comp
    (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)))) (ZMod.castHom (dvd_pow_self l (Nat.succ_ne_zero r)) (ZMod l)))
    (x : ZMod (l ^ (r + 1)))).symm

theorem eta_shift [IsAlgClosure ℚ Ω] (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) (e : ℕ) {r : ℕ} (hr : r ≠ 0)
    (s : G ℚ Ω) (x : (ZMod (l ^ r))ˣ) :
    ‖(((((x * cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r (x * cycMod ℚ Ω l r s) -
      ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x * ((eps l s ^ e)⁻¹ * (χ s : Qbar l))‖ ≤
      ‖((l : ℕ) : Qbar l) ^ r‖ := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have h := norm_inv_pow_sub_le (l := l) hr e
    (a := ((((x * cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : ℤ_[l]))
    (b := (((x : ZMod (l ^ r)).val : ℕ) : ℤ_[l]) * (cycZ ℚ Ω l s : ℤ_[l]))
    (by rw [map_natCast, ZMod.natCast_zmod_val]; exact Units.isUnit _)
    (by rw [map_mul, map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; rfl)
  rw [map_mul, map_natCast, map_natCast, ← cycBar_val, mul_pow, mul_inv] at h
  rw [chiK_mul_cycMod hχ hr, show ∀ a b c u v : Qbar l, a * (u * v) - b * u * (c * v) = u * v * (a - b * c) from
    fun _ _ _ _ _ => by ring, norm_mul, norm_mul, norm_eq_one_of_pow (chiK_pow hχ hr x), norm_eq_one_of_pow (chi_pow hχ s),
    one_mul, one_mul]
  exact h

end Chi

end GlobalTheory.K4.TwistClauses

namespace GlobalTheory.K4

open TwistClauses in

theorem twist_clauses : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
  (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
  (ψ : ZMod l → Qbar l) (cf : Coef l) (S : Finset Pl),
  Nf e S A W → l ≠ 2 → (∃ x, cw x ≠ 0) → AdmWn ι e gN A W X pr N cw c d gm ψ cf →
  ∃ θ : G ℚ Ω →* (Qbar l)ˣ, Continuous θ ∧ (∀ s, mat W s = (θ s : Qbar l) • rhoK W e ψ s) ∧
    (∀ c' : Coef l, (∀ s i j, mat W s i j ∈ c'.O) → ∀ s i j, rhoK W e ψ s i j ∈ c'.O) ∧
    (∀ c' : Coef l, ∀ r x, chiK l (Function.update ψ 0 0) r x ∈ c'.O) ∧
    (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖chiK l (Function.update ψ 0 0) (r + 1) x - chiK l (Function.update ψ 0 0) r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
    (∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l (Function.update ψ 0 0) r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l (Function.update ψ 0 0) r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
    (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∀ s ∈ Ine (F := ℚ) B, θ s = 1) ∧
    (∀ s ∈ Dec (F := ℚ) A, rhoK W e ψ s 1 0 = 0 ∧ rhoK W e ψ s 1 1 = (nuD W e ψ s : Qbar l)) ∧
    (∀ r, (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l (Function.update ψ 0 0) r x) = (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x)) := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ cw c d gm ψ cf S hNf _ hx hadm
  obtain ⟨x₀, hx₀⟩ := hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, χ, hkill, -, hχ'⟩ := hadm.1 x₀ hx₀
  have hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s) := fun s => by rw [hχ', cycRes_eq_val]
  set θ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (-(e : ℤ)) * χ with hθdef
  have hθu : ∀ s, θ s = cycBar ℚ Ω l s ^ (-(e : ℤ)) * χ s := fun s => rfl
  have hθ : ∀ s, (θ s : Qbar l) = (eps l s ^ e)⁻¹ * χ s := fun s => by
    rw [hθu, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_neg, zpow_natCast]
  have hth : ∀ s, thK l e ψ s = θ s := fun s => by rw [hθ, hχ', thK]
  have hρ : ∀ s i j, rhoK W e ψ s i j = (θ s : Qbar l)⁻¹ * mat W s i j := fun s i j => by
    rw [rhoK, hth, Matrix.smul_apply, smul_eq_mul]
  refine ⟨θ, ?_, fun s => ?_, fun c' hW s i j => ?_, fun c' r x => ?_, fun r x => ?_, fun r s x => ?_,
    fun q hq B hB s hs => ?_, fun s hs => ?_, fun r => funext fun x => ?_⟩
  · exact (continuous_cycBar'.zpow (-(e : ℤ))).mul (GlobalTheory.Ord2.VanishKato.cont_kills l hl.out.one_le χ hkill)
  · rw [rhoK, hth, smul_smul, mul_inv_cancel₀ (θ s).ne_zero, one_smul]
  · rw [hρ, hθ, mul_inv, inv_inv]
    refine mul_mem (mul_mem (pow_mem (c'.O.algebraMap_mem (cycZ ℚ Ω l s : ℤ_[l])) e) ?_) (hW s i j)
    exact mem_O_of_pow_eq_one c' _ (by rw [inv_pow, chi_pow hχ, inv_one])
  · rcases eq_or_ne r 0 with rfl | hr
    · rw [chiK_update_zero]; exact zero_mem _
    · rw [chiK_update hr]; exact mem_O_of_pow_eq_one c' _ (chiK_pow hχ hr x)
  · rcases eq_or_ne r 0 with rfl | hr
    · rw [chiK_update_zero, chiK_update (Nat.succ_ne_zero 0), sub_zero,
        norm_eq_one_of_pow (chiK_pow hχ (Nat.succ_ne_zero 0) x), pow_zero, norm_one]
    · rw [← chiK_succ _ hr, sub_self, norm_zero]; exact norm_nonneg _
  · rcases eq_or_ne r 0 with rfl | hr
    · simp only [chiK_update_zero, mul_zero, zero_mul, sub_self, norm_zero]; exact norm_nonneg _
    · simp only [chiK_update hr, hθ]
      exact eta_shift hχ e hr s x
  · have hz := cycZ_inertia hq hB hs
    have h1 : cycBar ℚ Ω l s = 1 := by rw [cycBar, MonoidHom.comp_apply, hz, map_one]
    have h2 : cycRes l Ω s = 1 := by
      rw [cycRes, MonoidHom.comp_apply, MonoidHom.comp_apply, cycMod, MonoidHom.comp_apply, hz, map_one, map_one, map_one]
    rw [hθu, h1, chi_eq_one hχ h2, one_zpow, one_mul]
  · have h10 := hNf.upper s hs
    have hdet : (mat W s).det ≠ 0 := (Matrix.GeneralLinearGroup.det (W s)).ne_zero
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    have h11 : rhoK W e ψ s 1 1 ≠ 0 := by
      rw [hρ]; exact mul_ne_zero (inv_ne_zero (θ s).ne_zero) (right_ne_zero_of_mul hdet)
    refine ⟨by rw [hρ, h10, mul_zero], ?_⟩
    rw [nuD, dif_pos h11, Units.val_mk0]
  · rcases eq_or_ne r 0 with rfl | hr
    · rw [val_level_zero, Nat.cast_zero, zero_pow (Nat.one_le_iff_ne_zero.1 hNf.e_pos), inv_zero, zero_mul, zero_mul]
    · rw [chiK_update hr]

end GlobalTheory.K4

end
