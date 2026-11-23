import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MeasurablePinv
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBR

noncomputable section

open MeasureTheory NumberField NumberField.mixedEmbedding Formalism.BasicNotions
open scoped ENNReal Classical

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX
open Formalism.L2.SG.NGCut.LeadingMinorIntegrality (dI mem_inv_coe dI_ne_bot star_mem_inv)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

local notation "FIE" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E
local notation "FIF" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  first
    | exact Formalism.HC.HostRaw.conj_conj _ x
    | exact Formalism.HC.HostRaw.conj_conj x
    | exact D.host.conj_conj x

theorem ddS_eq : ddS D = ((dI D : Ideal (𝓞 D.host.E)) : FIE) := rfl

theorem ddS_ne : ddS D ≠ 0 := by
  rw [ddS_eq, Ne, FractionalIdeal.coeIdeal_eq_zero]
  simpa using dI_ne_bot (D := D) 1

theorem aa_sq (a : Fin D.R.rS) :
    aaD D a * aaD D a = (((dI D ^ (2 * (D.R.rS - (a : ℕ))) : Ideal (𝓞 D.host.E)) : FIE))⁻¹ := by
  have h : ddS D ≠ 0 := ddS_ne
  have hle : (a : ℕ) ≤ D.R.rS := a.isLt.le
  show ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) * ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) = _
  rw [← zpow_add₀ h, ddS_eq, FractionalIdeal.coeIdeal_pow, ← zpow_natCast, ← zpow_neg]
  congr 1
  push_cast [Nat.cast_sub hle]
  ring

theorem mem_inv_coeF {J : Ideal (𝓞 D.host.F)} (hJ : J ≠ ⊥) (x : D.host.F) :
    x ∈ ((J : FIF))⁻¹ ↔ ∀ y ∈ J, ∃ o : 𝓞 D.host.F, (o : D.host.F) = x * (y : D.host.F) := by
  have hJ' : (J : FIF) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hJ
  rw [FractionalIdeal.mem_inv_iff hJ']
  simp only [FractionalIdeal.mem_one_iff, FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  first
    | done
    | exact Iff.rfl
    | rfl

theorem dF_ne (n : ℕ) : differentIdeal ℤ (𝓞 D.host.F) ^ n ≠ ⊥ := by
  first
    | exact pow_ne_zero n (by simpa [← Ideal.zero_eq_bot] using
        (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 D.host.F)))
    | (intro h
       apply dI_ne_bot (D := D) n
       show Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ^ n = ⊥
       rw [← Ideal.map_pow, h, Ideal.map_bot])

theorem coe_algO (z : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) z : 𝓞 D.host.E) : D.host.E) = (((z : D.host.F)) : D.host.E) := rfl

theorem contr (n : ℕ) (y : D.host.F) :
    (y : D.host.E) ∈ (((dI D ^ n : Ideal (𝓞 D.host.E)) : FIE))⁻¹ ↔
      y ∈ (((differentIdeal ℤ (𝓞 D.host.F) ^ n : Ideal (𝓞 D.host.F)) : FIF))⁻¹ := by
  constructor
  · intro hy
    rw [mem_inv_coeF (dF_ne n) y]
    rw [mem_inv_coe (dI_ne_bot (D := D) n)] at hy
    intro w hw
    have hw' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) w ∈ dI D ^ n := by
      show _ ∈ (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ n
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hw
    obtain ⟨o, ho⟩ := hy _ hw'
    rw [coe_algO] at ho
    have hint : IsIntegral ℤ (((y * w : D.host.F) : D.host.E)) := by
      rw [Subfield.coe_mul, ← ho]
      exact NumberField.RingOfIntegers.isIntegral_coe o
    have hint' : IsIntegral ℤ (y * w : D.host.F) := by
      first
        | exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp hint
        | exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) (RingHom.injective _)).mp hint
    exact ⟨⟨y * w, hint'⟩, rfl⟩
  · intro hy
    rw [mem_inv_coeF (dF_ne n) y] at hy
    rw [mem_inv_coe (dI_ne_bot (D := D) n)]
    intro z hz
    have hz' : z ∈ Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F) ^ n) := by
      rw [Ideal.map_pow]
      exact hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz'
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨o', ho'⟩ := hy w hw
      refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) o', ?_⟩
      rw [coe_algO, coe_algO, ho', Subfield.coe_mul]
    · first
        | exact ⟨0, by simp⟩
        | exact ⟨0, (mul_zero _).symm⟩
    · rintro a b _ _ ⟨oa, ha⟩ ⟨ob, hb⟩
      refine ⟨oa + ob, ?_⟩
      show (oa : D.host.E) + ob = _ * ((a : D.host.E) + b)
      rw [ha, hb]
      ring
    · rintro r a _ ⟨oa, ha⟩
      refine ⟨r * oa, ?_⟩
      show (r : D.host.E) * oa = _ * ((r : D.host.E) * a)
      rw [ha]
      ring

def omg (D : D7) : D.host.E := (1 + D.host.sqrtMinusD) / 2

private theorem conj_sqrtMinusD' : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  first
    | exact D.host.conj_sqd
    | exact Formalism.HC.HostRaw.conj_sqd _
    | exact Formalism.HC.HostRaw.conj_sqd

theorem omg_add_conj : omg D + D.host.conj (omg D) = 1 := by
  show (1 + D.host.sqrtMinusD) / 2 + D.host.conj ((1 + D.host.sqrtMinusD) / 2) = 1
  rw [map_div₀, map_add, map_one, conj_sqrtMinusD', map_ofNat]
  ring

theorem omg_int : IsIntegral ℤ (omg D) := by
  have hd : D.host.d % 8 = 7 := by
    first
      | exact D.host.d_mod_eight
      | exact Formalism.HC.HostRaw.d_mod_eight _
      | exact Formalism.HC.HostRaw.d_mod_eight
  have h2 : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hk : (D.host.d + 1) / 4 * 4 = D.host.d + 1 := Nat.div_mul_cancel (by omega)
  have hk' : ((((D.host.d + 1) / 4 : ℕ) : ℤ) : D.host.E) * 4 = (D.host.d : D.host.E) + 1 := by
    exact_mod_cast hk
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((D.host.d + 1) / 4 : ℕ) : ℤ), ?_, ?_⟩
  · first
      | monicity!
      | monicity
  · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    show ((1 + D.host.sqrtMinusD) / 2) ^ 2 - (1 + D.host.sqrtMinusD) / 2 +
      (algebraMap ℤ D.host.E) (((D.host.d + 1) / 4 : ℕ) : ℤ) = 0
    rw [algebraMap_int_eq, eq_intCast]
    linear_combination (1 / 4 : D.host.E) * h2 + (1 / 4 : D.host.E) * hk'

private theorem embS_conj' (τ : D.what₂.Tau) (x : D.host.E) :
    embS D τ (D.host.conj x) = (starRingEnd ℂ) (embS D τ x) := by
  haveI := D.host.isCMField_hostE
  rw [← Formalism.MainNotions.S.Inh.tie_star]
  first
    | exact (NumberField.IsCMField.isConj_complexConj D.host.E (embS D τ)).eq x
    | exact NumberField.ComplexEmbedding.IsConj.eq (NumberField.IsCMField.isConj_complexConj D.host.E (embS D τ)) x

theorem embS_add_conj (τ : D.what₂.Tau) (x : D.host.E) :
    embS D τ (x + D.host.conj x) = ((2 * (embS D τ x).re : ℝ) : ℂ) := by
  rw [map_add, embS_conj', Complex.add_conj]

theorem sqrtMinusD_int : IsIntegral ℤ (D.host.sqrtMinusD) := by
  have h : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (D.host.d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  simp [h]

theorem sqrtMinusD_ne : D.host.sqrtMinusD ≠ 0 := by
  intro h0
  have h : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h
  have h2 := D.host.qd_big.2
  first
    | (rw [h] at h2; exact Nat.not_lt_zero _ h2)
    | omega

variable (X : HidaSetting D)

abbrev nIm (a : Fin D.R.rS) : ℕ := 2 * (D.R.rS - (a : ℕ))

abbrev IIm (a : Fin D.R.rS) : FIE := ((dI D ^ nIm a : Ideal (𝓞 D.host.E)) : FIE)⁻¹

theorem IIm_mul_int (a : Fin D.R.rS) {t : D.host.E} (ht : t ∈ IIm a) (o : 𝓞 D.host.E) : (o : D.host.E) * t ∈ IIm a := by
  have h := (IIm a : Submodule (𝓞 D.host.E) D.host.E).smul_mem o ht
  rw [Algebra.smul_def] at h
  exact h

theorem int_mem_IIm (a : Fin D.R.rS) (o : 𝓞 D.host.E) : (o : D.host.E) ∈ IIm a := by
  refine (mem_inv_coe (dI_ne_bot (D := D) (nIm a)) _).2 ?_
  intro y _
  exact ⟨o * y, by first | rfl | push_cast; rfl | simp⟩

theorem conj_mem_IIm (a : Fin D.R.rS) {t : D.host.E} (ht : t ∈ IIm a) : D.host.conj t ∈ IIm a := by
  have h := star_mem_inv (D := D) (nIm a) ht
  rwa [Formalism.MainNotions.S.Inh.tie_star] at h

abbrev JF (a : Fin D.R.rS) : FIF := ((differentIdeal ℤ (𝓞 D.host.F) ^ nIm a : Ideal (𝓞 D.host.F)) : FIF)⁻¹

theorem mem_JF (a : Fin D.R.rS) (y : D.host.F) : y ∈ JF a ↔ (y : D.host.E) ∈ IIm a := (contr (nIm a) y).symm

def Ahalf (a : Fin D.R.rS) : FIF := FractionalIdeal.spanSingleton _ (2⁻¹ : D.host.F) * JF a

theorem mem_Ahalf (a : Fin D.R.rS) (y : D.host.F) : y ∈ Ahalf a ↔ (((2 : D.host.F) * y : D.host.F) : D.host.E) ∈ IIm a := by
  show y ∈ FractionalIdeal.spanSingleton _ (2⁻¹ : D.host.F) * JF a ↔ _
  rw [FractionalIdeal.mem_singleton_mul, ← mem_JF]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
  · intro h
    exact ⟨2 * y, h, by rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]⟩

def reImHom : (InfinitePlace X.B.I.F → ℂ) →+ (InfinitePlace X.B.I.F → ℝ) × (InfinitePlace X.B.I.F → ℝ) where
  toFun z := (fun v => (z v).re, fun v => (z v).im)
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

def ΓIm (a : Fin D.R.rS) : AddSubgroup ((InfinitePlace X.B.I.F → ℝ) × (InfinitePlace X.B.I.F → ℝ)) :=
  ((IIm a : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup).map ((reImHom X).comp (embVHom X))

theorem mem_ΓIm (a : Fin D.R.rS) (g) : g ∈ ΓIm X a ↔ ∃ t ∈ IIm a, reImHom X (embVHom X t) = g := by
  first
    | exact AddSubgroup.mem_map
    | exact Iff.rfl
    | simp [ΓIm]

def sF (t : D.host.E) : D.host.F := ⟨t + D.host.conj t, (mem_F_iff _).2 (by rw [map_add, conj_conj, add_comm])⟩

theorem coeF_two : ((2 : D.host.F) : D.host.E) = 2 := by
  first
    | rfl
    | norm_num
    | simp

private theorem embS_coe_F_im_eq_zero (τ : D.what₂.Tau) (w : D.host.F) : (embS D τ (w : D.host.E)).im = 0 := by
  have hw : D.host.conj (w : D.host.E) = w := (mem_F_iff (w : D.host.E)).1 w.2
  have h := congrArg Complex.im (embS_add_conj τ (w : D.host.E))
  rw [hw, map_add, Complex.add_im, Complex.ofReal_im] at h
  linarith

private theorem embS_coe_F_eq_ofReal_re (τ : D.what₂.Tau) (w : D.host.F) :
    embS D τ (w : D.host.E) = ((embS D τ (w : D.host.E)).re : ℂ) :=
  Complex.ext (by simp) (by simp [embS_coe_F_im_eq_zero])

theorem re_half (t : D.host.E) (v : InfinitePlace X.B.I.F) :
    reVHom X ((2⁻¹ : D.host.F) * sF t) v = (embS D (X.pl v) t).re := by
  have h1 : (((2⁻¹ : D.host.F) * sF t : D.host.F) : D.host.E) = 2⁻¹ * (t + D.host.conj t) := by
    rw [Subfield.coe_mul, Subfield.coe_inv, coeF_two]; rfl
  show (embS D (X.pl v) (((2⁻¹ : D.host.F) * sF t : D.host.F) : D.host.E)).re = _
  rw [h1, map_mul, embS_add_conj, map_inv₀, map_ofNat]
  have h2 : (2 : ℂ)⁻¹ * (((2 * (embS D (X.pl v) t).re : ℝ)) : ℂ) = ((embS D (X.pl v) t).re : ℂ) := by
    push_cast
    first
      | ring
      | field_simp
  rw [h2, Complex.ofReal_re]

private theorem embS_sqrtMinusD_re_eq_zero (τ : D.what₂.Tau) : (embS D τ D.host.sqrtMinusD).re = 0 := by
  have h := congrArg Complex.re (embS_add_conj τ D.host.sqrtMinusD)
  rw [conj_sqrtMinusD', add_neg_cancel, map_zero, Complex.zero_re, Complex.ofReal_re] at h
  linarith

theorem embS_omg_re (τ : D.what₂.Tau) : (embS D τ (omg D)).re = 2⁻¹ := by
  have h := embS_sqrtMinusD_re_eq_zero τ
  show (embS D τ ((1 + D.host.sqrtMinusD) / 2)).re = 2⁻¹
  rw [map_div₀, map_add, map_one, map_ofNat]
  first
    | (rw [Complex.div_ofNat_re, Complex.add_re, Complex.one_re, h]; norm_num)
    | (simp [Complex.div_re, h]; norm_num)

theorem hA1 (a : Fin D.R.rS) (x : InfinitePlace X.B.I.F → ℝ) :
    x ∈ reLat X (Ahalf a) ↔ ∃ y, (x, y) ∈ ΓIm X a := by
  show x ∈ ((Ahalf a : Submodule (𝓞 D.host.F) D.host.F).toAddSubgroup).map (reVHom X) ↔ _
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (((2 : D.host.F) * z : D.host.F) : D.host.E) ∈ IIm a := (mem_Ahalf a z).1 hz
    refine ⟨fun v => (embS D (X.pl v) ((((2 : D.host.F) * z : D.host.F) : D.host.E) * omg D)).im, ?_⟩
    rw [mem_ΓIm]
    refine ⟨(((2 : D.host.F) * z : D.host.F) : D.host.E) * omg D, ?_, ?_⟩
    · have h := IIm_mul_int a hz' ⟨omg D, omg_int⟩
      rw [mul_comm] at h
      exact h
    · refine Prod.ext ?_ rfl
      funext v
      show (embS D (X.pl v) ((((2 : D.host.F) * z : D.host.F) : D.host.E) * omg D)).re =
        (embS D (X.pl v) (z : D.host.E)).re
      rw [map_mul, embS_coe_F_eq_ofReal_re (X.pl v) ((2 : D.host.F) * z), Complex.re_ofReal_mul, embS_omg_re,
        Subfield.coe_mul, coeF_two, map_mul, map_ofNat]
      first
        | (rw [Complex.re_ofNat_mul]; ring)
        | (simp; ring)
  · rintro ⟨y, hy⟩
    rw [mem_ΓIm] at hy
    obtain ⟨t, ht, hteq⟩ := hy
    refine ⟨(2⁻¹ : D.host.F) * sF t, ?_, ?_⟩
    · show (2⁻¹ : D.host.F) * sF t ∈ Ahalf a
      rw [mem_Ahalf, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
      exact (IIm a : Submodule (𝓞 D.host.E) D.host.E).add_mem ht (conj_mem_IIm a ht)
    · funext v
      rw [re_half]
      exact congrFun (congrArg Prod.fst hteq) v

theorem re_zero_iff (t : D.host.E) :
    (∀ v : InfinitePlace X.B.I.F, (embS D (X.pl v) t).re = 0) ↔ D.host.conj t = -t := by
  constructor
  · intro h
    have hy : ∀ v, reVHom X (sF t) v = 0 := by
      intro v
      show (embS D (X.pl v) (t + D.host.conj t)).re = 0
      rw [embS_add_conj, Complex.ofReal_re, h v, mul_zero]
    have hz : mixedEmbedding D.host.F (sF t) = 0 := by
      refine Prod.ext (funext fun w => ?_) (funext fun w => isEmptyElim w)
      have hw : (⟨psiP X ((psiP X).symm w.1), IsTotallyReal.isReal _⟩ :
          {w : InfinitePlace D.host.F // w.IsReal}) = w := Subtype.ext (Equiv.apply_symm_apply _ _)
      rw [← hw, mixed_re, hy]
      rfl
    have h0 : sF t = 0 := mixedEmbedding_injective D.host.F (hz.trans (map_zero _).symm)
    have h1 : t + D.host.conj t = 0 := congrArg Subtype.val h0
    linear_combination h1
  · intro hc v
    have h := congrArg Complex.re (embS_add_conj (X.pl v) t)
    rw [hc, add_neg_cancel, map_zero, Complex.zero_re, Complex.ofReal_re] at h
    linarith

def Ssub (a : Fin D.R.rS) : AddSubgroup D.host.E where
  carrier := {t | t ∈ IIm a ∧ D.host.conj t = -t}
  zero_mem' := ⟨(IIm a : Submodule (𝓞 D.host.E) D.host.E).zero_mem, by simp⟩
  add_mem' ha hb := ⟨(IIm a : Submodule (𝓞 D.host.E) D.host.E).add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, neg_add]⟩
  neg_mem' ha := ⟨(IIm a : Submodule (𝓞 D.host.E) D.host.E).neg_mem ha.1, by rw [map_neg, ha.2]⟩

def imVHom : D.host.E →+ (InfinitePlace X.B.I.F → ℝ) where
  toFun t := fun v => (embS D (X.pl v) t).im
  map_zero' := by funext v; simp
  map_add' a b := by funext v; simp

theorem mem_cLatIm (u : D.what₂.Word) (a : Fin D.R.rS) (y : InfinitePlace X.B.I.F → ℝ) :
    y ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ ∃ t ∈ Ssub a, imVHom X t = y := by
  have key : cLat X u (Sum.inr (Sum.inr a)) = (Ssub a).map (imVHom X) := by
    have hset : {t | t ∈ ((aaD D a * aaD D a : FIE) : Set D.host.E) ∧ D.host.conj t = -t} =
        ((Ssub a : AddSubgroup D.host.E) : Set D.host.E) := by
      ext t
      rw [Set.mem_setOf_eq, aa_sq]
      exact Iff.rfl
    show AddSubgroup.closure ((fun t v => (embS D (X.pl v) t).im) ''
      {t | t ∈ ((aaD D a * aaD D a : FIE) : Set D.host.E) ∧ D.host.conj t = -t}) = _
    rw [hset]
    show AddSubgroup.closure (⇑(imVHom X) '' ((Ssub a : AddSubgroup D.host.E) : Set D.host.E)) = _
    rw [← AddMonoidHom.map_closure, AddSubgroup.closure_eq]
  rw [key]
  exact AddSubgroup.mem_map

theorem hA2 (u : D.what₂.Word) (a : Fin D.R.rS) (y : InfinitePlace X.B.I.F → ℝ) :
    y ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ ((0 : InfinitePlace X.B.I.F → ℝ), y) ∈ ΓIm X a := by
  rw [mem_cLatIm, mem_ΓIm]
  constructor
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    refine ⟨t, ht, Prod.ext ?_ rfl⟩
    funext v
    exact (re_zero_iff X t).2 hc v
  · rintro ⟨t, ht, h⟩
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact ⟨t, ⟨ht, (re_zero_iff X t).1 (fun v => congrFun h1 v)⟩, h2⟩

def bbSub (a : Fin D.R.rS) : Submodule (𝓞 D.host.F) D.host.F where
  carrier := {y | D.host.sqrtMinusD * (y : D.host.E) ∈ IIm a}
  add_mem' {y z} hy hz := by
    show D.host.sqrtMinusD * ((y + z : D.host.F) : D.host.E) ∈ IIm a
    rw [Subfield.coe_add, mul_add]; exact (IIm a : Submodule (𝓞 D.host.E) D.host.E).add_mem hy hz
  zero_mem' := by
    show D.host.sqrtMinusD * ((0 : D.host.F) : D.host.E) ∈ IIm a
    rw [Subfield.coe_zero, mul_zero]; exact (IIm a : Submodule (𝓞 D.host.E) D.host.E).zero_mem
  smul_mem' c y hy := by
    show D.host.sqrtMinusD * ((c • y : D.host.F) : D.host.E) ∈ IIm a
    have : ((c • y : D.host.F) : D.host.E) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) * (y : D.host.E) := by
      rw [coe_algO, Algebra.smul_def, Subfield.coe_mul]
    rw [this, mul_left_comm]; exact IIm_mul_int a hy _

theorem coeF_nat (n : ℕ) : ((n : D.host.F) : D.host.E) = (n : D.host.E) := by
  first
    | simp
    | norm_cast
    | exact map_natCast D.host.F.subtype n

theorem bb_le (a : Fin D.R.rS) :
    bbSub a ≤ ((FractionalIdeal.spanSingleton _ ((D.host.d : D.host.F))⁻¹ * JF a : FIF) : Submodule (𝓞 D.host.F) D.host.F) := by
  intro y hy
  have hy' : D.host.sqrtMinusD * (y : D.host.E) ∈ IIm a := hy
  have hd : (D.host.d : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.mpr ((Nat.zero_le _).trans_lt D.host.qd_big.2).ne'
  have h2 : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hm : -(D.host.sqrtMinusD * (D.host.sqrtMinusD * (y : D.host.E))) ∈ IIm a :=
    (IIm a : Submodule (𝓞 D.host.E) D.host.E).neg_mem
      (IIm_mul_int a hy' ⟨D.host.sqrtMinusD, sqrtMinusD_int⟩)
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]
  refine ⟨(D.host.d : D.host.F) * y, ?_, ?_⟩
  · rw [mem_JF]
    convert hm using 1
    rw [Subfield.coe_mul, coeF_nat]
    linear_combination (y : D.host.E) * h2
  · rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]

def bbF (a : Fin D.R.rS) : FIF := ⟨bbSub a, FractionalIdeal.isFractional_of_le (bb_le a)⟩

theorem mem_bbF (a : Fin D.R.rS) (y : D.host.F) : y ∈ bbF a ↔ D.host.sqrtMinusD * (y : D.host.E) ∈ IIm a := Iff.rfl

theorem bbF_ne (a : Fin D.R.rS) : bbF a ≠ 0 := by
  intro h
  have h1 : (1 : D.host.F) ∈ bbF a := by
    rw [mem_bbF]
    have := int_mem_IIm a ⟨D.host.sqrtMinusD, sqrtMinusD_int⟩
    first
      | (rw [OneMemClass.coe_one, mul_one]; exact this)
      | simpa using this
  rw [h, FractionalIdeal.mem_zero_iff] at h1
  exact one_ne_zero h1

def cIm (v : InfinitePlace X.B.I.F) : ℝ := (embS D (X.pl v) D.host.sqrtMinusD).im

theorem cIm_ne (v : InfinitePlace X.B.I.F) : cIm X v ≠ 0 := by
  intro h
  apply sqrtMinusD_ne (D := D)
  apply (embS D (X.pl v)).injective
  rw [map_zero]
  exact Complex.ext (embS_sqrtMinusD_re_eq_zero (X.pl v)) h

theorem mem_cLatIm_bb (u : D.what₂.Word) (a : Fin D.R.rS) (y : InfinitePlace X.B.I.F → ℝ) :
    y ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ ∃ x ∈ reLat X (bbF a), (fun v => x v * cIm X v) = y := by
  rw [mem_cLatIm]
  have hs := sqrtMinusD_ne (D := D)
  constructor
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    have hwF : t / D.host.sqrtMinusD ∈ D.host.F := by
      rw [mem_F_iff, map_div₀, hc, conj_sqrtMinusD', neg_div_neg_eq]
    refine ⟨reVHom X ⟨t / D.host.sqrtMinusD, hwF⟩, ?_, ?_⟩
    · show _ ∈ ((bbF a : Submodule (𝓞 D.host.F) D.host.F).toAddSubgroup).map (reVHom X)
      refine AddSubgroup.mem_map_of_mem _ ?_
      show D.host.sqrtMinusD * (t / D.host.sqrtMinusD) ∈ IIm a
      have e : D.host.sqrtMinusD * (t / D.host.sqrtMinusD) = t := by field_simp
      rw [e]
      exact ht
    · funext v
      have him : (embS D (X.pl v) (t / D.host.sqrtMinusD)).im = 0 := embS_coe_F_im_eq_zero (X.pl v) ⟨_, hwF⟩
      have hre : (embS D (X.pl v) D.host.sqrtMinusD).re = 0 := embS_sqrtMinusD_re_eq_zero (X.pl v)
      have e : t / D.host.sqrtMinusD * D.host.sqrtMinusD = t := by field_simp
      show (embS D (X.pl v) (t / D.host.sqrtMinusD)).re * (embS D (X.pl v) D.host.sqrtMinusD).im =
        (embS D (X.pl v) t).im
      conv_rhs => rw [← e, map_mul, Complex.mul_im]
      rw [him, hre]
      ring
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ ((bbF a : Submodule (𝓞 D.host.F) D.host.F).toAddSubgroup).map (reVHom X) := hx
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hx'
    refine ⟨D.host.sqrtMinusD * (w : D.host.E), ⟨hw, ?_⟩, ?_⟩
    · rw [map_mul, conj_sqrtMinusD', (mem_F_iff (w : D.host.E)).1 w.2, neg_mul]
    · funext v
      show (embS D (X.pl v) (D.host.sqrtMinusD * (w : D.host.E))).im =
        (embS D (X.pl v) (w : D.host.E)).re * (embS D (X.pl v) D.host.sqrtMinusD).im
      rw [map_mul, Complex.mul_im, embS_sqrtMinusD_re_eq_zero, embS_coe_F_im_eq_zero]
      ring

abbrev toF {a : Fin D.R.rS} (x : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inr a) : CBlk D.R.rS)) :
    InfinitePlace X.B.I.F → ℝ := x

theorem fd_cLatIm (u : D.what₂.Word) (a : Fin D.R.rS) :
    ∃ F : Set (InfinitePlace X.B.I.F → ℝ), MeasurableSet F ∧
      ∀ z : InfinitePlace X.B.I.F → ℝ, ∃! b : cLat X u (Sum.inr (Sum.inr a)),
        toF X (b : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inr a) : CBlk D.R.rS)) + z ∈ F := by
  obtain ⟨⟨F₀, hF₀m, hF₀⟩, -⟩ := realIdealBlock X (Units.mk0 (bbF a) (bbF_ne a))
  refine ⟨(fun (y : InfinitePlace X.B.I.F → ℝ) v => y v / cIm X v) ⁻¹' F₀, ?_, ?_⟩
  · refine hF₀m.preimage ?_
    first
      | exact measurable_pi_lambda _ fun v => (measurable_pi_apply v).div_const _
      | measurability
      | fun_prop
  · intro z
    obtain ⟨⟨x, hx⟩, hxF, huniq⟩ := hF₀ (fun v => z v / cIm X v)
    have hmem : (fun v => x v * cIm X v : InfinitePlace X.B.I.F → ℝ) ∈ cLat X u (Sum.inr (Sum.inr a)) :=
      (mem_cLatIm_bb X u a _).2 ⟨x, hx, rfl⟩
    refine ⟨⟨(fun v => x v * cIm X v : InfinitePlace X.B.I.F → ℝ), hmem⟩, ?_, ?_⟩
    · show (fun v => (x v * cIm X v + z v) / cIm X v) ∈ F₀
      convert hxF using 1
      funext v
      show (x v * cIm X v + z v) / cIm X v = x v + z v / cIm X v
      have hc := cIm_ne X v
      field_simp
    · rintro ⟨b, hb⟩ hbF
      obtain ⟨x', hx', rfl⟩ := (mem_cLatIm_bb X u a b).1 hb
      have hbF' : (fun v => (x' v * cIm X v + z v) / cIm X v) ∈ F₀ := hbF
      have h := huniq ⟨x', hx'⟩ (by
        convert hbF' using 1
        funext v
        show x' v + z v / cIm X v = (x' v * cIm X v + z v) / cIm X v
        have hc := cIm_ne X v
        field_simp)
      have hxx : x' = x := congrArg Subtype.val h
      subst hxx
      rfl

def reImE : (InfinitePlace X.B.I.F → ℂ) ≃ᵐ (InfinitePlace X.B.I.F → ℝ) × (InfinitePlace X.B.I.F → ℝ) :=
  (MeasurableEquiv.piCongrRight (fun _ => Complex.measurableEquivRealProd)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (InfinitePlace X.B.I.F))

theorem reImE_apply (z : InfinitePlace X.B.I.F → ℂ) : reImE X z = reImHom X z := rfl

theorem reImE_mp : MeasurePreserving (reImE X) volume volume := by
  first
    | exact (MeasureTheory.volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (InfinitePlace X.B.I.F)).comp
        (MeasureTheory.volume_preserving_pi (fun _ => Complex.volume_preserving_equiv_real_prod))
    | exact (MeasureTheory.measurePreserving_arrowProdEquivProdArrow ℝ ℝ (InfinitePlace X.B.I.F)
        (fun _ => volume) (fun _ => volume)).comp
        (MeasureTheory.volume_preserving_pi (fun _ => Complex.volume_preserving_equiv_real_prod))
    | exact (MeasureTheory.volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (InfinitePlace X.B.I.F)).comp
        (MeasureTheory.measurePreserving_piCongrRight _ (fun _ => Complex.volume_preserving_equiv_real_prod))

theorem reImE_symm_add (p q : (InfinitePlace X.B.I.F → ℝ) × (InfinitePlace X.B.I.F → ℝ)) :
    (reImE X).symm (p + q) = (reImE X).symm p + (reImE X).symm q := by
  apply (reImE X).injective
  rw [MeasurableEquiv.apply_symm_apply, reImE_apply, map_add, ← reImE_apply, ← reImE_apply]
  simp only [MeasurableEquiv.apply_symm_apply]

theorem card_ι : Fintype.card (InfinitePlace X.B.I.F) = Module.finrank ℚ D.host.F := by
  rw [Fintype.card_congr (psiP X)]
  first
    | (have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.F
       rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h
       rw [← h, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
         NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero])
    | simp [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank]

theorem absNorm_Ahalf (a : Fin D.R.rS) :
    ((FractionalIdeal.absNorm (Ahalf a) : ℚ) : ℝ) = (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(discr X.B.I.F : ℝ)| ^ (-(2 * ((D.R.rS : ℝ) - (a : ℕ)))) := by
  have hle : (a : ℕ) ≤ D.R.rS := a.isLt.le
  have hJ : FractionalIdeal.absNorm (JF a) = (((discr D.host.F).natAbs : ℚ) ^ nIm a)⁻¹ := by
    show FractionalIdeal.absNorm (((differentIdeal ℤ (𝓞 D.host.F) ^ nIm a : Ideal (𝓞 D.host.F)) : FIF))⁻¹ = _
    simp only [map_inv₀, FractionalIdeal.coeIdeal_absNorm, map_pow, Nat.cast_pow]
    congr 2
    have h := NumberField.absNorm_differentIdeal (K := D.host.F)
    rw [h]
  have hS : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.F)) (2⁻¹ : D.host.F)) =
      (2⁻¹ : ℚ) ^ Module.finrank ℚ D.host.F := by
    rw [FractionalIdeal.absNorm_span_singleton]
    rw [show (2⁻¹ : D.host.F) = algebraMap ℚ D.host.F 2⁻¹ by simp, Algebra.norm_algebraMap]
    rw [abs_pow, abs_of_pos (by norm_num : (0 : ℚ) < 2⁻¹)]
  show ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton _ (2⁻¹ : D.host.F) * JF a) : ℚ) : ℝ) = _
  have e1 : ((nIm a : ℕ) : ℝ) = 2 * ((D.R.rS : ℝ) - (a : ℕ)) := by
    push_cast [nIm, Nat.cast_sub hle]
    ring
  rw [map_mul, hS, hJ, card_ι, discrF_eq, ← e1, Real.rpow_neg (abs_nonneg _), Real.rpow_natCast]
  push_cast
  first
    | done
    | rfl
    | simp [Nat.cast_natAbs, Int.cast_abs]

theorem realId {d : ℝ} (hd : 0 < d) (m c : ℝ) :
    d ^ (-(2 * m)) * d ^ (-(2 * m)) * c * d = d ^ ((1 / 2 : ℝ) - 2 * m) * (c * d ^ (-(2 * m)) * √d) := by
  rw [Real.sqrt_eq_rpow]
  calc d ^ (-(2 * m)) * d ^ (-(2 * m)) * c * d = c * (d ^ (-(2 * m)) * d ^ (-(2 * m)) * d ^ (1 : ℝ)) := by
        rw [Real.rpow_one]; ring
    _ = c * d ^ (-(2 * m) + -(2 * m) + 1) := by
        rw [Real.rpow_add hd, Real.rpow_add hd]
    _ = c * d ^ (((1 / 2 : ℝ) - 2 * m) + -(2 * m) + 1 / 2) := by
        congr 2; ring
    _ = d ^ ((1 / 2 : ℝ) - 2 * m) * (c * d ^ (-(2 * m)) * d ^ (1 / 2 : ℝ)) := by
        rw [Real.rpow_add hd, Real.rpow_add hd]; ring

theorem blockCovol_M (u : D.what₂.Word) (a : Fin D.R.rS) :
    Countable (cLat X u (Sum.inr (Sum.inr a))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inr a) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! b : cLat X u (Sum.inr (Sum.inr a)),
        (b : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inr a) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inr a) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! b : cLat X u (Sum.inr (Sum.inr a)),
        (b : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inr a) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inr a)) F = ENNReal.ofReal (cVal X u (Sum.inr (Sum.inr a))) := by
  have hcE : Countable D.host.E := by
    let b := Module.finBasis ℚ D.host.E
    exact Function.Injective.countable b.equivFun.injective
  refine ⟨?_, fd_cLatIm X u a, fun F hF hFd => ?_⟩
  · exact Function.Surjective.countable
      (f := fun t : Ssub a => (⟨imVHom X t, (mem_cLatIm X u a _).2 ⟨t, t.2, rfl⟩⟩ : cLat X u (Sum.inr (Sum.inr a))))
      (fun ⟨y, hy⟩ => by obtain ⟨t, ht, rfl⟩ := (mem_cLatIm X u a y).1 hy; exact ⟨⟨t, ht⟩, rfl⟩)

  set Γ := ΓIm X a with hΓ
  have : Countable Γ := by
    refine Function.Surjective.countable (f := fun t : (IIm a : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup =>
      (⟨reImHom X (embVHom X t), (mem_ΓIm X a _).2 ⟨t, t.2, rfl⟩⟩ : Γ)) ?_
    rintro ⟨g, hg⟩
    obtain ⟨t, ht, rfl⟩ := (mem_ΓIm X a g).1 hg
    exact ⟨⟨t, ht⟩, rfl⟩
  set A₂ : AddSubgroup (InfinitePlace X.B.I.F → ℝ) := (Ssub a).map (imVHom X) with hA₂def
  have hA₂mem : ∀ y, y ∈ A₂ ↔ y ∈ cLat X u (Sum.inr (Sum.inr a)) := by
    intro y; rw [mem_cLatIm, hA₂def, AddSubgroup.mem_map]
  have hA₂ : ∀ y, y ∈ A₂ ↔ ((0 : InfinitePlace X.B.I.F → ℝ), y) ∈ Γ := fun y => (hA₂mem y).trans (hA2 X u a y)
  have hd₂ : ∀ y : InfinitePlace X.B.I.F → ℝ, ∃! c : A₂, (c : InfinitePlace X.B.I.F → ℝ) + y ∈ F := by
    intro y
    obtain ⟨⟨b, hb⟩, hbF, hu⟩ := hFd y
    refine ⟨⟨b, (hA₂mem b).2 hb⟩, hbF, ?_⟩
    rintro ⟨c, hc⟩ hcF
    have := hu ⟨c, (hA₂mem c).1 hc⟩ hcF
    have h' : c = b := congrArg Subtype.val this
    exact Subtype.ext h'

  obtain ⟨F₁, hF₁, hd₁⟩ := (realIdealBlock X (Units.mk0 (Ahalf a) (by
      intro h
      have : (2⁻¹ : D.host.F) ∈ Ahalf a := (mem_Ahalf a _).2 (by
        rw [mul_inv_cancel₀ two_ne_zero, Subfield.coe_one]
        exact int_mem_IIm a 1)
      rw [h, FractionalIdeal.mem_zero_iff] at this
      exact two_ne_zero (inv_eq_zero.1 this)))).1
  have hF₁v := (realIdealBlock X (Units.mk0 (Ahalf a) (by
      intro h
      have : (2⁻¹ : D.host.F) ∈ Ahalf a := (mem_Ahalf a _).2 (by
        rw [mul_inv_cancel₀ two_ne_zero, Subfield.coe_one]
        exact int_mem_IIm a 1)
      rw [h, FractionalIdeal.mem_zero_iff] at this
      exact two_ne_zero (inv_eq_zero.1 this)))).2 F₁ hF₁ hd₁
  have hA₁ : ∀ x, x ∈ reLat X (Ahalf a) ↔ ∃ y, (x, y) ∈ Γ := hA1 X a

  have hI0 : aaD D a * aaD D a ≠ 0 := mul_ne_zero (aaD_ne_zero X a) (aaD_ne_zero X a)
  obtain ⟨-, ⟨K0, hK0, hK0d⟩, hK0v⟩ := idealBlock X (aaD D a * aaD D a) hI0
  have hK0vol := hK0v K0 hK0 hK0d
  set K := (reImE X).symm ⁻¹' K0 with hKdef
  have hK : MeasurableSet K := (reImE X).symm.measurable hK0
  have hKd : ∀ g, ∃! γ : Γ, (γ : (InfinitePlace X.B.I.F → ℝ) × (InfinitePlace X.B.I.F → ℝ)) + g ∈ K := by
    intro g
    obtain ⟨⟨c, hc⟩, hcK, hu⟩ := hK0d ((reImE X).symm g)
    obtain ⟨t, ht, rfl⟩ := (mem_closure_embV X _ c).1 hc
    rw [aa_sq] at ht
    refine ⟨⟨reImHom X (embVHom X t), (mem_ΓIm X a _).2 ⟨t, ht, rfl⟩⟩, ?_, ?_⟩
    · show (reImE X).symm (reImHom X (embVHom X t) + g) ∈ K0
      rw [reImE_symm_add, ← reImE_apply, MeasurableEquiv.symm_apply_apply]; exact hcK
    · rintro ⟨γ, hγ⟩ hγK
      obtain ⟨t', ht', rfl⟩ := (mem_ΓIm X a γ).1 hγ
      have h1 : embVHom X t' ∈ AddSubgroup.closure (embV X '' ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)) :=
        (mem_closure_embV X _ _).2 ⟨t', by rw [aa_sq]; exact ht', rfl⟩
      have h2 : ((⟨embVHom X t', h1⟩ : AddSubgroup.closure (embV X '' ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E))) :
          InfinitePlace X.B.I.F → ℂ) + (reImE X).symm g ∈ K0 := by
        have : (reImE X).symm (reImHom X (embVHom X t') + g) ∈ K0 := hγK
        rwa [reImE_symm_add, ← reImE_apply, MeasurableEquiv.symm_apply_apply] at this
      have h3 := hu _ h2
      have h4 : embVHom X t' = embVHom X t := congrArg Subtype.val h3
      apply Subtype.ext
      show reImHom X (embVHom X t') = reImHom X (embVHom X t)
      rw [h4]
  have hfib := fib2 (volume : Measure (InfinitePlace X.B.I.F → ℝ)) Γ (reLat X (Ahalf a)) A₂ hA₁ hA₂ F₁ F hF₁ hF
    (fun v => by simpa using hd₁ v) hd₂ K hK hKd
  have hKv : (volume.prod volume : Measure ((InfinitePlace X.B.I.F → ℝ) × (InfinitePlace X.B.I.F → ℝ))) K = volume K0 :=
    (reImE_mp X).symm.measure_preimage hK0.nullMeasurableSet
  rw [hKv, hK0vol, hF₁v] at hfib

  show (volume : Measure (InfinitePlace X.B.I.F → ℝ)) F = _
  have hd := dF_pos X
  set m : ℝ := (D.R.rS : ℝ) - (a : ℕ) with hm
  have hB : 0 < ((FractionalIdeal.absNorm (Ahalf a) : ℚ) : ℝ) * √|(discr D.host.F : ℝ)| := by
    rw [absNorm_Ahalf X a]
    have : 0 < √|(discr D.host.F : ℝ)| := Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.F))
    positivity
  have hval : ((FractionalIdeal.absNorm (aaD D a * aaD D a) : ℚ) : ℝ) * 2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(discr X.B.I.F : ℝ)| = cVal X u (Sum.inr (Sum.inr a)) *
        (((FractionalIdeal.absNorm (Ahalf a) : ℚ) : ℝ) * √|(discr D.host.F : ℝ)|) := by
    rw [map_mul, Rat.cast_mul, absNorm_aaD X, absNorm_Ahalf X a, ← discrF_eq X]
    show _ = |(discr X.B.I.F : ℝ)| ^ ((1 / 2 : ℝ) - 2 * m) * _
    exact realId hd m _
  have hcv : 0 ≤ cVal X u (Sum.inr (Sum.inr a)) := Real.rpow_nonneg (abs_nonneg _) _
  rw [hval, ENNReal.ofReal_mul hcv, mul_comm] at hfib
  exact ((ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hB).ne' ENNReal.ofReal_ne_top).1 hfib).symm

theorem blockCovol_of (hR : RowBlockCovol) : BlockCovol := by
  intro D X u p
  rcases p with (p | b) | (p | a)
  · exact blockCovol_X X u p
  · exact hR X u b
  · exact blockCovol_K X u p
  · exact blockCovol_M X u a

end Formalism.L2.SG.Pf.NcReal.JX.CovB
